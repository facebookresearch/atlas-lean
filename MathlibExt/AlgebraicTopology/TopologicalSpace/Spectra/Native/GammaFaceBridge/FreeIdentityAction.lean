/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback

/-!
# Free Identity Action

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The identity generator of the actual free object retains any complete original left coefficient. -/
theorem free_left_identity_coefficient (a b : A) (K L : PointedCGWH.{u, v})
    (D : L ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    (L ◁ Free.evaluate a K (Free.object a K) (𝟙 (Free.object a K))) ≫
      CurrentFree.action a b L D (Free.object a K) =
    (β_ L K).hom ≫ (K ◁ D) := by
  let X := Free.object a K
  let E := X.toEnrichedFunctor.obj a
  let H := a ⟶[PointedCGWH.{u, v}] b
  let ev := Free.evaluate a K X (𝟙 X)
  let act := MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)
  have hD : (D ▷ E) ≫ (β_ E H).inv = (β_ L E).hom ≫ (E ◁ D) :=
    (braiding_inv_naturality_left D E).trans
      (congrArg (fun z => z ≫ (E ◁ D))
        (SymmetricCategory.braiding_swap_eq_inv_braiding E L).symm)
  have hNat : (L ◁ ev) ≫ (β_ L E).hom =
      (β_ L K).hom ≫ (ev ▷ L) := by
    simpa only [id_tensorHom, tensorHom_id] using braiding_naturality (𝟙 L) ev
  change (L ◁ ev) ≫ ((D ▷ E) ≫ (β_ E H).inv ≫ act) = _
  calc
    _ = (L ◁ ev) ≫ (β_ L E).hom ≫ (E ◁ D) ≫ act := by
      rw [← Category.assoc (D ▷ E) (β_ E H).inv act, hD]
      simp only [Category.assoc]
    _ = (β_ L K).hom ≫ (ev ▷ L) ≫ (E ◁ D) ≫ act := by
      rw [← Category.assoc (L ◁ ev) (β_ L E).hom ((E ◁ D) ≫ act), hNat]
      simp only [Category.assoc]
    _ = (β_ L K).hom ≫ (ev ⊗ₘ D) ≫ act := by
      rw [tensorHom_def]
      simp only [Category.assoc]
      rfl
    _ = _ := congrArg (fun z => (β_ L K).hom ≫ z)
      (FreeAction.identity_coefficient a b K L D)

/-- The same actual free identity keeps its complete coefficient followed by the original target-index map. -/
theorem free_left_identity_target (a b c : A) (K L : PointedCGWH.{u, v})
    (D : L ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (q : ForgetEnrichment.of PointedCGWH.{u, v} b ⟶
      ForgetEnrichment.of PointedCGWH.{u, v} c) :
    (L ◁ Free.evaluate a K (Free.object a K) (𝟙 (Free.object a K))) ≫
      CurrentFree.action a b L D (Free.object a K) ≫
      Sequential.indexMap (Free.object a K) q =
    (β_ L K).hom ≫
      (K ◁ (D ≫ eHomWhiskerLeft PointedCGWH.{u, v}
        (ForgetEnrichment.of PointedCGWH.{u, v} a) q)) := by
  rw [← Sequential.action_postcompose]
  exact free_left_identity_coefficient a c K L
    (D ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} a) q)

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
