/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
public import MathlibExt.Algebra.Homology.ShiftedTensorUnits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Actual weighted negative-cyclic integration composite

Given the source-normalized relative DR map, integration is its
actual NC map, the inverse of the canonical finite-coefficient NC
tensor comparison, and id⊗trace. The final unit/shift comparison is
fixed on every homogeneous unit summand with the native sign.

This completed construction supplies neither the relative DR map nor
perfection/invertibility by a hypothesis containing the final result.
Those source constructions/proofs are separate dependencies. The
relative map and canonical comparison retain all NC closing coefficients.
Reference: PTVV arXiv:1111.3209v4, Definition 2.3, p.32.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.WeightedNCIntegration

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.Algebra.Homology.ShiftedTensorUnits

universe u
variable {R : Type u} [CommRing R]
attribute [local instance] HasDerivedCategory.standard

/-- The genuine integration morphism is relative NC pullback/comparison followed by id⊗trace. -/
def integrate {E F : GradedMixed R} {C : CochainComplex (ModuleCat.{u} R) ℤ}
    {p : ℤ} (P : PureTensorModel F C) (κ : MixedMap E P.mixed)
    (M : NegativeCyclicModel E p) (N : NegativeCyclicModel F p)
    (T : NegativeCyclicModel P.mixed p) (K : CyclicMapModel κ p M T)
    (B : Comparison P p N T) [IsIso (DerivedCategory.Q.map B.map)]
    {d : ℤ} (trace : C ⟶ (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))⟦-d⟧)
    (U : UnitTensorModel N.complex (-d)) :
    DerivedCategory.Q.obj M.complex ⟶ DerivedCategory.Q.obj (N.complex⟦-d⟧) :=
  DerivedCategory.Q.map K.map ≫ inv (DerivedCategory.Q.map B.map) ≫
    DerivedCategory.Q.map (𝟙 N.complex ⊗ₘ trace) ≫ DerivedCategory.Q.map U.comparison.hom

end MathlibExt.AlgebraicGeometry.WeightedNCIntegration
