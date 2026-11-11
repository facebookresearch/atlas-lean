/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.NormTrace.Prod

@[expose] public section

example {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
    (x : A × B) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 :=
  Algebra.norm_prod x

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Subsingleton A] (a : A) :
    Algebra.norm R a = 1 :=
  Algebra.norm_of_subsingleton a
