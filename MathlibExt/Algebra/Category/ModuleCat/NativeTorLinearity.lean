/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseCompatibility
public import MathlibExt.Algebra.Homology.Linear
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Scalar linearity of native Tor in its first coefficient

The original projective resolution in the second coefficient computes the
first-variable native Tor maps. The actual tensor and homology maps retain
addition and the original base scalar action in every degree. The ring and
module carrier universes are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor
universe nr nm
variable (R₇ : Type nr) [CommRing R₇]

/-- The genuine first-variable map of native Tor is linear, computed
using the actual original projective resolution and homology maps. -/
def nativeTorFirstMapLinear {X₁ X₂ : ModuleCat.{max nr nm} R₇}
    (Y : ModuleCat.{max nr nm} R₇) (q : ℕ) :
    (X₁ ⟶ X₂) →ₗ[R₇]
      (((Tor (ModuleCat.{max nr nm} R₇) q).obj X₁).obj Y ⟶
        ((Tor (ModuleCat.{max nr nm} R₇) q).obj X₂).obj Y) where
  toFun f := ((Tor (ModuleCat.{max nr nm} R₇) q).map f).app Y
  map_add' f g := by
    let P := projectiveResolution Y
    let T := tensoringLeft (ModuleCat.{max nr nm} R₇)
    let κ : (X₁ ⟶ X₂) →
        (((T.obj X₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex ⟶
          ((T.obj X₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) :=
      fun h => (NatTrans.mapHomologicalComplex (T.map h) (ComplexShape.down ℕ)).app P.complex
    have hc : κ (f + g) = κ f + κ g := by
      apply HomologicalComplex.Hom.ext
      funext i
      change (f + g) ▷ P.complex.X i = f ▷ P.complex.X i + g ▷ P.complex.X i
      exact MonoidalPreadditive.add_whiskerRight f g
    change (NatTrans.leftDerived (T.map (f + g)) q).app Y =
      (NatTrans.leftDerived (T.map f) q).app Y + (NatTrans.leftDerived (T.map g) q).app Y
    rw [P.leftDerived_app_eq (T.map (f + g)) q,
      P.leftDerived_app_eq (T.map f) q, P.leftDerived_app_eq (T.map g) q]
    let K₁ := ((T.obj X₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    let K₂ := ((T.obj X₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    let u₁ : ((Tor (ModuleCat.{max nr nm} R₇) q).obj X₁).obj Y ⟶ K₁.homology q :=
      (P.isoLeftDerivedObj (T.obj X₁) q).hom
    let u₂ : K₂.homology q ⟶ ((Tor (ModuleCat.{max nr nm} R₇) q).obj X₂).obj Y :=
      (P.isoLeftDerivedObj (T.obj X₂) q).inv
    change u₁ ≫ HomologicalComplex.homologyMap (κ (f + g)) q ≫ u₂ =
      (u₁ ≫ HomologicalComplex.homologyMap (κ f) q ≫ u₂) +
        (u₁ ≫ HomologicalComplex.homologyMap (κ g) q ≫ u₂)
    rw [hc, HomologicalComplex.homologyMap_add]
    simp only [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r f := by
    let P := projectiveResolution Y
    let T := tensoringLeft (ModuleCat.{max nr nm} R₇)
    let κ : (X₁ ⟶ X₂) →
        (((T.obj X₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex ⟶
          ((T.obj X₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) :=
      fun h => (NatTrans.mapHomologicalComplex (T.map h) (ComplexShape.down ℕ)).app P.complex
    have hc : κ (r • f) = r • κ f := by
      apply HomologicalComplex.Hom.ext
      funext i
      change (r • f) ▷ P.complex.X i = r • (f ▷ P.complex.X i)
      exact MonoidalLinear.smul_whiskerRight r f (P.complex.X i)
    change (NatTrans.leftDerived (T.map (r • f)) q).app Y =
      r • (NatTrans.leftDerived (T.map f) q).app Y
    rw [P.leftDerived_app_eq (T.map (r • f)) q, P.leftDerived_app_eq (T.map f) q]
    let K₁ := ((T.obj X₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    let K₂ := ((T.obj X₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    let u₁ : ((Tor (ModuleCat.{max nr nm} R₇) q).obj X₁).obj Y ⟶ K₁.homology q :=
      (P.isoLeftDerivedObj (T.obj X₁) q).hom
    let u₂ : K₂.homology q ⟶ ((Tor (ModuleCat.{max nr nm} R₇) q).obj X₂).obj Y :=
      (P.isoLeftDerivedObj (T.obj X₂) q).inv
    change u₁ ≫ HomologicalComplex.homologyMap (κ (r • f)) q ≫ u₂ =
      r • (u₁ ≫ HomologicalComplex.homologyMap (κ f) q ≫ u₂)
    rw [hc]
    have hh := Functor.map_smul
      (HomologicalComplex.homologyFunctor (ModuleCat.{max nr nm} R₇)
        (ComplexShape.down ℕ) q) r (κ f)
    change HomologicalComplex.homologyMap (r • κ f) q =
      r • HomologicalComplex.homologyMap (κ f) q at hh
    rw [hh]
    simp only [Linear.comp_smul, Linear.smul_comp]

end ModuleCat.UniverseTensor
