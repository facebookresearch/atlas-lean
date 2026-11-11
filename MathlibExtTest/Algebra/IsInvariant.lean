/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.IsInvariant

@[expose] public section

example (R : Type*) [CommRing R] [IsNoetherianRing R]
    (A : Type*) [CommRing A] [Algebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Algebra.FiniteType R B] :
    Module.Finite A B ∧ Algebra.FiniteType R A :=
  Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType R A B G
