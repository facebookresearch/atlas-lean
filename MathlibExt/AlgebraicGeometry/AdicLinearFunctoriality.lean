/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.AdjunctionLinear
public import MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality

/-! # Linearity of actual continuous-coefficient cohomology pullback

Restriction along scheme base change is visibly linear. The actual
inverse-image adjunction transfers this to pullback, and Mathlib's linear
Ext maps give the scalar action on the already fixed cohomology operator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality

open _root_.CategoryTheory _root_.AlgebraicGeometry
open ContinuousAdicCoefficients ProEtaleCohomologyFunctoriality

variable (R : Type) [CommRing R]

instance pushforwardLinear {Y X : Scheme} (f : Y ⟶ X) :
    Functor.Linear R (pushforward R f) where
  map_smul _ _ := rfl

instance pullbackLinear {Y X : Scheme} (f : Y ⟶ X) :
    Functor.Linear R (pullback R f) :=
  MathlibExt.CategoryTheory.linear_leftAdjoint R (pullbackAdjunction R f)

/-- The linear Ext construction uses the same inverse image and unit maps. -/
def cohomologyPullbackLinear {Y X : Scheme} (f : Y ⟶ X)
    {F : CoefficientSheaf X R} {G : CoefficientSheaf Y R}
    (c : (pullback R f).obj F ⟶ G) (n : ℕ) :
    Cohomology R X F n →ₗ[R] Cohomology R Y G n := by
  let A : CoefficientSheaf X R := constantUnit R X
  let B : CoefficientSheaf Y R := (pullback R f).obj A
  let F' : CoefficientSheaf Y R := (pullback R f).obj F
  let m₀ : Abelian.Ext.{1} A F n →ₗ[R] Abelian.Ext.{1} B F' n :=
    (pullback R f).mapExtLinearMap R A F n
  let m₁ : Abelian.Ext.{1} B F' n →ₗ[R] Abelian.Ext.{1} B G n :=
    (Abelian.Ext.mk₀ c).postcompOfLinear R B (add_zero n)
  let m₂ : Abelian.Ext.{1} B G n →ₗ[R]
      Abelian.Ext.{1} (constantUnit R Y) G n :=
    (Abelian.Ext.mk₀ (constantPullbackIso R f).inv).precompOfLinear R G
      (zero_add n)
  exact m₂.comp (m₁.comp m₀)

/-- Its value is the existing normalized actual cohomology pullback. -/
theorem cohomologyPullbackLinear_apply {Y X : Scheme} (f : Y ⟶ X)
    {F : CoefficientSheaf X R} {G : CoefficientSheaf Y R}
    (c : (pullback R f).obj F ⟶ G) (n : ℕ) (a : Cohomology R X F n) :
    cohomologyPullbackLinear R f c n a = cohomologyPullback R f c n a := rfl

variable (M : Type 1) [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

def continuousPullbackLinear {Y X : Scheme} (f : Y ⟶ X) (n : ℕ) :
    Cohomology R X (continuousModuleSheaf R M X) n →ₗ[R]
      Cohomology R Y (continuousModuleSheaf R M Y) n :=
  cohomologyPullbackLinear R f (coefficientPullback R M f) n

theorem continuousPullbackLinear_apply {Y X : Scheme} (f : Y ⟶ X) (n : ℕ)
    (a : Cohomology R X (continuousModuleSheaf R M X) n) :
    continuousPullbackLinear R M f n a =
      continuousCohomologyPullback R M f n a := rfl

end MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
