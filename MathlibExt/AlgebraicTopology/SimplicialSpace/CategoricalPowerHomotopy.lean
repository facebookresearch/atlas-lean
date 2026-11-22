/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingEUnitDwyerKan
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Categorical homotopies induce homotopies of true-power precomposition

Source: Rezk2001 Proposition13.5. The original E-cylinder has BOTH original
endpoints. No fibrancy, Segal, completeness, weakness, Ho or DK outcome is
assumed. The power is the existing native Cartesian closed power.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian

namespace SimplicialSpace.CategoricalPowerHomotopy

local notation "E" => WalkingEUnit.coherentSpace

/-- Endpoint insertion commutes with the actual tensor exchange of A, E and X. -/
@[reassoc]
theorem endpoint_tensor_exchange (A X : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    A ◁ WalkingEUnit.spaceEndpoint X e ≫ (α_ A E X).inv ≫
        ((β_ A E).hom ▷ X) = WalkingEUnit.spaceEndpoint A e ▷ X := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, whiskerRight_fst_assoc,
        braiding_hom_fst, associator_inv_fst_snd,
        whiskerLeft_snd_assoc, (WalkingEUnit.spaceEndpoint_laws X e).1,
        (WalkingEUnit.spaceEndpoint_laws A e).1, comp_toUnit_assoc]
    · simp only [Category.assoc, whiskerRight_fst_assoc,
        braiding_hom_snd, associator_inv_fst_fst,
        whiskerLeft_fst, (WalkingEUnit.spaceEndpoint_laws A e).2.1,
        Category.comp_id]
  · simp only [Category.assoc, whiskerRight_snd, associator_inv_snd,
      whiskerLeft_snd_assoc, (WalkingEUnit.spaceEndpoint_laws X e).2.1,
      Category.comp_id]

/-- The actual E-homotopy on precomposition is curry of the original H and evaluation. -/
def homotopyPrecomp {A B : SimplicialSpace.{u}}
    (H : E ⊗ A ⟶ B) (W : SimplicialSpace.{u}) :
    E ⊗ ((ihom B).obj W) ⟶ (ihom A).obj W :=
  curry ((α_ A E ((ihom B).obj W)).inv ≫
    ((β_ A E).hom ▷ (ihom B).obj W) ≫
    (H ▷ (ihom B).obj W) ≫ (ihom.ev B).app W)

/-- Every original E vertex gives exactly precomposition by the corresponding H endpoint. -/
theorem homotopyPrecomp_endpoint {A B : SimplicialSpace.{u}}
    (H : E ⊗ A ⟶ B) (W : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    WalkingEUnit.spaceEndpoint ((ihom B).obj W) e ≫ homotopyPrecomp H W =
      (pre (WalkingEUnit.spaceEndpoint A e ≫ H)).app W := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre]
  dsimp only [homotopyPrecomp]
  rw [uncurry_curry]
  rw [endpoint_tensor_exchange_assoc, ← comp_whiskerRight_assoc]

/-- BOTH original whole endpoint equations are retained in the SAME true-power homotopy. -/
theorem homotopyPrecomp_endpoints {A B : SimplicialSpace.{u}}
    (f0 f1 : A ⟶ B) (H : E ⊗ A ⟶ B)
    (h0 : WalkingEUnit.spaceEndpoint A SSet.coherentIso.x₀ ≫ H = f0)
    (h1 : WalkingEUnit.spaceEndpoint A SSet.coherentIso.x₁ ≫ H = f1)
    (W : SimplicialSpace.{u}) :
    WalkingEUnit.spaceEndpoint ((ihom B).obj W) SSet.coherentIso.x₀ ≫
        homotopyPrecomp H W = (pre f0).app W ∧
      WalkingEUnit.spaceEndpoint ((ihom B).obj W) SSet.coherentIso.x₁ ≫
        homotopyPrecomp H W = (pre f1).app W := by
  constructor
  · simpa only [h0] using homotopyPrecomp_endpoint H W SSet.coherentIso.x₀
  · simpa only [h1] using homotopyPrecomp_endpoint H W SSet.coherentIso.x₁

/-- Every original target map acts by the SAME native power functors on both sides. -/
theorem homotopyPrecomp_target {A B : SimplicialSpace.{u}}
    (H : E ⊗ A ⟶ B) {W V : SimplicialSpace.{u}} (w : W ⟶ V) :
    (E ◁ (ihom B).map w) ≫ homotopyPrecomp H V =
      homotopyPrecomp H W ≫ (ihom A).map w := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  dsimp only [homotopyPrecomp]
  rw [uncurry_curry, uncurry_curry]
  have hn := (ihom.ev B).naturality w
  change B ◁ (ihom B).map w ≫ (ihom.ev B).app V =
    (ihom.ev B).app W ≫ w at hn
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, whisker_exchange_assoc, hn]

/-- Both original exponent-source maps retain their contravariant precomposition actions. -/
theorem homotopyPrecomp_source_target
    {A' A B B' : SimplicialSpace.{u}} (a : A' ⟶ A) (b : B ⟶ B')
    (H : E ⊗ A ⟶ B) (W : SimplicialSpace.{u}) :
    (E ◁ (pre b).app W) ≫ homotopyPrecomp H W ≫ (pre a).app W =
      homotopyPrecomp (E ◁ a ≫ H ≫ b) W := by
  apply uncurry_injective
  rw [← Category.assoc, uncurry_pre_app, uncurry_natural_left]
  dsimp only [homotopyPrecomp]
  rw [uncurry_curry, uncurry_curry]
  simp only [Category.assoc, comp_whiskerRight]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left, comp_whiskerRight]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    whisker_exchange_assoc, whisker_exchange_assoc, id_tensor_pre_app_comp_ev]

end SimplicialSpace.CategoricalPowerHomotopy
