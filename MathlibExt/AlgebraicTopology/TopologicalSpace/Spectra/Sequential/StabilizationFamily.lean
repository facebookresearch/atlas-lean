/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.StabilizationMap
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# The literal countable unit stabilization family

The right unitor inverse gives the original free source of each unit map.
The family retains the actual natural-number label and its original arrow.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory MonoidalCategory

namespace PointedCGWH.SequentialSpectrum

/-- Unit normalization of the original stabilization map for any coordinate. -/
def unitStabilizationMap (K : PointedCGWH.{u, v}) (n : ℕ) :
    (freeAt K (n + 1)).obj K ⟶ (freeAt K n).obj (𝟙_ PointedCGWH.{u, v}) :=
  (freeAt K (n + 1)).map (ρ_ K).inv ≫
    stabilizationMap K n (𝟙_ PointedCGWH.{u, v})

/-- The adjunct retains the actual right unitor, free unit and structure map. -/
theorem unitStabilizationMap_homEquiv (K : PointedCGWH.{u, v}) (n : ℕ) :
    (freeAtEvaluationAdjunction K (n + 1)).homEquiv
        K ((freeAt K n).obj (𝟙_ PointedCGWH.{u, v}))
        (unitStabilizationMap K n) =
      (ρ_ K).inv ≫
        (K ◁ (freeAtEvaluationAdjunction K n).unit.app (𝟙_ PointedCGWH.{u, v})) ≫
        CategoryTheory.Spectra.Sequential.structureMap
        ((freeAt K n).obj (𝟙_ PointedCGWH.{u, v})) n := by
  have hMap : unitStabilizationMap K n =
      (freeAt K (n + 1)).map (ρ_ K).inv ≫
        stabilizationMap K n (𝟙_ PointedCGWH.{u, v}) := rfl
  have hApply := congrArg
    (fun q : (freeAt K (n + 1)).obj K ⟶
        (freeAt K n).obj (𝟙_ PointedCGWH.{u, v}) =>
      (freeAtEvaluationAdjunction K (n + 1)).homEquiv
        K ((freeAt K n).obj (𝟙_ PointedCGWH.{u, v})) q) hMap
  have hNatural := (freeAtEvaluationAdjunction K (n + 1)).homEquiv_naturality_left
    (ρ_ K).inv (stabilizationMap K n (𝟙_ PointedCGWH.{u, v}))
  have hAdjunct := congrArg (fun q => (ρ_ K).inv ≫ q)
    (stabilizationMap_homEquiv K n (𝟙_ PointedCGWH.{u, v}))
  exact hApply.trans (hNatural.trans hAdjunct)

/-- The literal natural-number-indexed family for any native coordinate. -/
def unitStabilizationFamily (K : PointedCGWH.{u, v}) :
    MorphismProperty (CategoryTheory.Spectra.Sequential.Spectrum K) :=
  MorphismProperty.ofHoms (unitStabilizationMap K)

/-- Membership retains equality with the original correlated free arrow. -/
theorem unitStabilizationFamily_iff (K : PointedCGWH.{u, v})
    {X Y : CategoryTheory.Spectra.Sequential.Spectrum K} (f : X ⟶ Y) :
    unitStabilizationFamily K f ↔
      ∃ n : ℕ, Arrow.mk f = Arrow.mk (unitStabilizationMap K n) :=
  MorphismProperty.ofHoms_iff _ f

/-- Each original normalized stabilization map belongs to the family. -/
theorem unitStabilizationMap_mem (K : PointedCGWH.{u, v}) (n : ℕ) :
    unitStabilizationFamily K (unitStabilizationMap K n) :=
  MorphismProperty.ofHoms.mk n

/-- The literal countable family is small in an independent size universe. -/
theorem unitStabilizationFamily_isSmall (K : PointedCGWH.{u, v}) :
    (unitStabilizationFamily K).IsSmall.{w} := by
  let _ : Small.{w} ℕ := inferInstance
  exact MorphismProperty.isSmall_ofHoms (unitStabilizationMap K)

end PointedCGWH.SequentialSpectrum
