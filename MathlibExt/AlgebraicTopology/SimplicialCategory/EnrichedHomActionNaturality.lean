/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomPrecomposition

/-!
# Naturality of the SAME original full Hom actions

The actual original enriched-functor composition law supplies both
complete Hom-action squares, at every original scalar ordinal. The
component arrow readback retains the SAME original image unit-Hom map,
rather than a separately selected representative. Object and coefficient
universes remain independent, with no fibrancy or weak-outcome premise.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomActionNaturality
open ComponentCategory EnrichedHomVertexActions EnrichedHomPrecomposition

variable {C : Type v} [EnrichedCategory SSet.{u} C]
variable {D : Type w} [EnrichedCategory SSet.{u} D]
variable (F : EnrichedFunctor SSet.{u} C D)

/-- The original enriched map preserves the SAME whole postcomposition action square at every scalar ordinal. -/
theorem post_natural (z : C) {x y : C} (A : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    post z A ≫ F.map z y = F.map z x ≫ post (F.obj z) (A ≫ F.map x y) := by
  ext q a
  exact congrArg
    (fun h : (z ⟶[SSet.{u}] x) ⊗ (x ⟶[SSet.{u}] y) ⟶ (F.obj z ⟶[SSet.{u}] F.obj y) =>
      h.app q (SSet.componentTensorSimplex q a (A.app q PUnit.unit)))
    (F.map_comp z x y)

/-- The original enriched map preserves the SAME whole precomposition action square at every scalar ordinal. -/
theorem pre_natural (z : C) {x y : C} (A : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    pre z A ≫ F.map x z = F.map y z ≫ pre (F.obj z) (A ≫ F.map x y) := by
  ext q a
  exact congrArg
    (fun h : (x ⟶[SSet.{u}] y) ⊗ (y ⟶[SSet.{u}] z) ⟶ (F.obj x ⟶[SSet.{u}] F.obj z) =>
      h.app q (SSet.componentTensorSimplex q (A.app q PUnit.unit) a))
    (F.map_comp x y z)

/-- The SAME original component image arrow is represented by the actual original image unit-Hom map. -/
theorem component_map_unit {x y : C} (A : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    (mapFunctor F).map (arrowOf C (SSet.unitHomEquiv _ A)) =
      arrowOf D (SSet.unitHomEquiv _ (A ≫ F.map x y)) := by
  change SSet.mapπ₀ (F.map x y) (SSet.π₀.mk (SSet.unitHomEquiv _ A)) =
    SSet.π₀.mk (SSet.unitHomEquiv _ (A ≫ F.map x y))
  rw [SSet.mapπ₀_mk]
  rfl

end CategoryTheory.SimplicialEnrichment.EnrichedHomActionNaturality
