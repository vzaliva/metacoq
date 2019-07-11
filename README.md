Coq Coq Correct: Verification of Type Checking and Erasure for Coq, in Coq
=======

This directory contains the anonymised supplementary material for the paper "Coq Coq Correct: Verification of Type Checking and Erasure for Coq, in Coq".

There are several subdirectories:

Template-Coq (`template-coq`)
------------ 

Template-Coq is a quoting library for [Coq](http://coq.inria.fr). It
takes `Coq` terms and constructs a representation of their syntax tree as
a `Coq` inductive data type. The representation is based on the kernel's
term representation.

In addition to this representation of terms, Template Coq includes:

- Reification of the environment structures, for constant and inductive
  declarations.

- Denotation of terms and global declarations

- A monad for manipulating global declarations, calling the type
  checker, and inserting them in the global environment, in
  the stype of MTac.
  
Template-Coq was originally developed by
[Gregory Malecha](https://github.com/gmalecha).
  
PCUIC, Coq's Core Calculus (`pcuic`)
-----

PCUIC, the Polymorphic Cumulative Calculus of Inductive Constructions is
a cleaned up version of the term language of Coq and its associated
type system, equivalent to the one of Coq. This version of the
calculus has (partial) proofs of standard metatheoretical results:

- Weakening for global declarations, weakening and substitution for
  local contexts.

- Confluence of reduction using a notion of parallel reduction

- Subject Reduction

Contains the formalisation corresponding to section 2 of the paper.
There are some assumptions and admitted lemmas concerning the meta-theory of PCUIC, which are listed in the file `PCUICAdmittedLemmata.v`
  
A verified checker for PCUIC (`safechecker`)
-------
  
Contains the implementation of a correct conversion algorithm and type checker, described in section 3 of the paper.
The directory does not contain admits or axioms.

Type and proof erasure for PCUIC (`extraction`)
----------

Contains the implementation of a correct type and proof erasure procedure, described in section 4 of the paper.
The directory does not contain admits or axioms.

Compilation instructions
=========================

Requirements
------------

To compile the library, you need:

- `Coq 8.8.2` (older versions of `8.8` might also work)
- `OCaml` (tested with `4.06.1`, beware that `OCaml 4.06.0` can 
  produce linking errors on some platforms)
- [`Equations 1.2`](http://mattam82.github.io/Coq-Equations/)

Requirements through opam
-------------------------

The easiest way to get all packages is through [opam](http://opam.ocaml.org):

You might want to create a "switch" (an environment of `opam` packages) for `Coq` if
you don't have one yet. You need to use **opam 2** to obtain the right version of `Equations`.

    # opam switch create coq.8.8.2 4.06.1 
    # eval $(opam env)
    
This creates the `coq.8.8.2` switch which initially contains only the
basic `OCaml` `4.06.1` compiler, and puts you in the right environment
(check with `ocamlc -v`).

You can also create a [local
switch](https://opam.ocaml.org/blog/opam-20-tips/#Local-switches) for
developing using:

    # opam switch create . 4.06.1

Once in the right switch, you can install `Coq` and the `Equations` package using:
    
    # opam pin add coq 8.8.2
    # opam pin add coq-equations 1.2+8.8
    
Pinning the packages prevents `opam` from trying to upgrade it afterwards, in
this switch. If the commands are successful you should have `coq`
available (check with `coqc -v`).

Compile
-------

Once in the right environment, Use:

- `./configure.sh local` to prepare compilation

- `make` to compile the `template-coq` plugin, the `safechecker`, the `pcuic`
  development and the `extraction` development. You can also selectively build
  each target.

- `make html` to generate `html` files for all Coq files.
