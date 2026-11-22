/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectPullbackIntervalLiftBothLabels
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerEquivalenceVertexLifting

/-!
# Exact original F2 vertex equations read back as whole unit coefficient equations

The original source and target equalities eliminate only their stated
endpoint transports. The genuine original zero-vertex/unit-Hom dictionary
therefore turns the exact supplied F2 equation into the SAME whole unit
image equality. No coefficient map or weak outcome is replaced.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory
open Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalF2CoefficientEquation
variable {C : Type v} [EnrichedCategory SSet.{u} C]
variable {D : Type w} [EnrichedCategory SSet.{u} D]

/-- The actual original F2 image vertex retains its SAME complete unit Hom map at the original image endpoints. -/
theorem full_unit_image (r : EnrichedFunctor SSet.{u} C D) (x y : C) (dx dy : D)
    (hx : r.obj x = dx) (hy : r.obj y = dy)
    (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) (Q : 𝟙_ SSet.{u} ⟶ (dx ⟶[SSet.{u}] dy))
    (h : (r.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) rfl hy)).app _
      (SSet.unitHomEquiv _ q) = SSet.unitHomEquiv _
        (Q ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) hx.symm rfl))) :
    q ≫ (r.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) hx hy)) = Q := by
  cases hx
  cases hy
  have hv : (r.map x y).app (op ⦋0⦌) (SSet.unitHomEquiv _ q) = SSet.unitHomEquiv _ Q := by
    simpa only [eqToHom_refl, Category.comp_id] using h
  have hm : SSet.unitHomEquiv _ (q ≫ r.map x y) =
      (r.map x y).app (op ⦋0⦌) (SSet.unitHomEquiv _ q) := rfl
  have hf : q ≫ r.map x y = Q := (SSet.unitHomEquiv _).injective (hm.trans hv)
  exact (congrArg (fun k => q ≫ k) (Category.comp_id (r.map x y))).trans hf

end CategoryTheory.SimplicialEnrichment.OriginalF2CoefficientEquation
