/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomVertexActions
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationIhomInverse

/-!
# The actual full Hom action on original component objects

The full original enriched composition acts on every original Hom
simplicial set. Its parameter map sends the original component Hom
classes to the corresponding full internal-Hom classes. The actual
vertex dictionary and original unit/composition laws give a genuine
ordinary component functor, without replacing any original Hom or
assuming any fibrancy or weak-comparison outcome.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalClosed

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomComponentAction
open EnrichedHomVertexActions ComponentCategory

/-- Pin the actual scalar internal-Hom enrichment, retaining its whole original Hom complexes. -/
local instance scalarEnrichment : EnrichedCategory SSet.{u} SSet.{u} :=
  (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}).toEnrichedCategory

/-- Pin the matching actual scalar ordinary/enriched vertex dictionary. -/
local instance scalarOrdinaryEnrichment : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- The SAME original full Hom at the fixed original source object. -/
def homObject (z : C) (x : objects.{u} C) : SSet.{u} := z ⟶[SSet.{u}] originalObject C x

/-- The full original Hom parameter preserves component composition at the SAME three original objects. -/
theorem postClass_comp (z : C) {X Y T : C}
    (f : SSet.π₀ (X ⟶[SSet.{u}] Y)) (g : SSet.π₀ (Y ⟶[SSet.{u}] T)) :
    SSet.mapπ₀ (postParameter z X T)
      (SSet.mapπ₀ (eComp SSet.{u} X Y T)
        ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _) (f, g))) =
      SSet.mapπ₀ (eComp SSet.{u} (z ⟶[SSet.{u}] X) (z ⟶[SSet.{u}] Y) (z ⟶[SSet.{u}] T))
        ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _)
          (SSet.mapπ₀ (postParameter z X Y) f, SSet.mapπ₀ (postParameter z Y T) g)) := by
  induction f using SSet.π₀.rec with
  | mk a =>
    induction g using SSet.π₀.rec with
    | mk b =>
      let A : 𝟙_ SSet.{u} ⟶ (X ⟶[SSet.{u}] Y) := (SSet.unitHomEquiv _).symm a
      let B : 𝟙_ SSet.{u} ⟶ (Y ⟶[SSet.{u}] T) := (SSet.unitHomEquiv _).symm b
      have ha : SSet.unitHomEquiv _ A = a := Equiv.apply_symm_apply _ _
      have hb : SSet.unitHomEquiv _ B = b := Equiv.apply_symm_apply _ _
      simp only [SSet.piZeroMonoidal_μ_mk, SSet.mapπ₀_mk]
      rw [← ha, ← hb]
      let AB : 𝟙_ SSet.{u} ⟶ (X ⟶[SSet.{u}] T) :=
        (λ_ (𝟙_ SSet.{u})).inv ≫ (A ⊗ₘ B) ≫ eComp SSet.{u} X Y T
      have hab :
          (eComp SSet.{u} X Y T).app (op ⦋0⦌)
            (SSet.componentTensorSimplex _ (SSet.unitHomEquiv _ A) (SSet.unitHomEquiv _ B)) =
          SSet.unitHomEquiv _ AB := rfl
      rw [hab, postParameter_vertex, postParameter_vertex, postParameter_vertex, post_comp]
      apply congrArg SSet.π₀.mk
      rw [SSet.ihomVertexEquiv_eq]
      rw [MonoidalClosed.curry'_comp]
      rfl

/-- The actual component Hom action is induced by the full original composition parameter map. -/
def postFunctor (z : C) : objects.{u} C ⥤ objects.{u} SSet.{u} where
  obj x := objectOf.{u} SSet.{u} (homObject z x)
  map {x y} f := SSet.mapπ₀ (postParameter z (originalObject C x) (originalObject C y)) f
  map_id x := by
    let a := originalObject C x
    change SSet.mapπ₀ (postParameter z a a) (𝟙 (objectOf.{u} C a)) =
      𝟙 (objectOf.{u} SSet.{u} (z ⟶[SSet.{u}] a))
    rw [← arrowOf_identity C a]
    change SSet.mapπ₀ (postParameter z a a) (SSet.π₀.mk (SSet.unitHomEquiv _ (eId SSet.{u} a))) = _
    rw [SSet.mapπ₀_mk, postParameter_vertex, post_identity]
    change (vertexFunctor SSet.{u}).map (𝟙 (z ⟶[SSet.{u}] a)) = 𝟙 _
    exact (vertexFunctor SSet.{u}).map_id _
  map_comp {x y t} f g := by
    change SSet.mapπ₀ (postParameter z (originalObject C x) (originalObject C t))
      (SSet.mapπ₀ (eComp SSet.{u} (originalObject C x) (originalObject C y) (originalObject C t))
        ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _) (f, g))) = _
    exact postClass_comp z f g

/-- The actual postcomponent functor retains the SAME entire original source Hom object. -/
theorem postFunctor_obj (z : C) (x : C) :
    (postFunctor z).obj (objectOf.{u} C x) = objectOf.{u} SSet.{u} (z ⟶[SSet.{u}] x) := rfl

/-- Its full original parameter-vertex map is the SAME internal-Hom class of the actual Hom action. -/
theorem postFunctor_vertex (z : C) {x y : C} (f : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    (postFunctor z).map (arrowOf C (SSet.unitHomEquiv _ f)) =
      (vertexFunctor SSet.{u}).map (post z f) := by
  change SSet.mapπ₀ (postParameter z x y) (SSet.π₀.mk (SSet.unitHomEquiv _ f)) =
    SSet.π₀.mk (SSet.ihomVertexEquiv _ _ (post z f))
  rw [SSet.mapπ₀_mk, postParameter_vertex]

end CategoryTheory.SimplicialEnrichment.EnrichedHomComponentAction
