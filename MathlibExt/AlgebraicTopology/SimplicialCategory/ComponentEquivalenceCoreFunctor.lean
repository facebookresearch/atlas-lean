/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentEquivalenceCoreGroupoid

/-!
# Genuine full functoriality of the original component-equivalence core

Every original enriched functor preserves actual component-invertible
classes. Its SAME full Hom map therefore restricts to the actual whole
original selected subcomplexes. All scalar operators, identities,
compositions, original object maps and full inclusion squares remain.
No scalar or global weak comparison is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore

variable {C D E : Carrier.{u}}

private theorem class_map (F : C ⟶ D) (x y : C) (a : SSet.π₀ (x ⟶[SSet.{u}] y))
    (ha : equivalentClass C x y a) : equivalentClass D (F.obj x) (F.obj y) (SSet.mapπ₀ (F.map x y) a) := by
  let e : ComponentCategory.objectOf.{u} C x ≅ ComponentCategory.objectOf.{u} C y :=
    @asIso (ComponentCategory.objects.{u} C) inferInstance
      (ComponentCategory.objectOf.{u} C x) (ComponentCategory.objectOf.{u} C y) a ha
  exact ((ComponentCategory.mapFunctor F).mapIso e).isIso_hom

/-- The SAME entire original enriched Hom map restricts to its actual selected component-equivalence Homs. -/
def mapHom (F : C ⟶ D) (x y : C) : hom C x y ⟶ hom D (F.obj x) (F.obj y) where
  app q := ↾fun a => ⟨(F.map x y).app q a.val,
    SSet.componentUnion_map (F.map x y) (equivalentClass C x y)
      (equivalentClass D (F.obj x) (F.obj y)) (class_map F x y) q a.val a.property⟩
  naturality q r f := by
    ext a
    apply Subtype.ext
    exact NatTrans.naturality_apply (F.map x y) f a.val

/-- Every original full selected-Hom map retains the SAME inclusion square and original coefficient map. -/
theorem mapHom_inclusion (F : C ⟶ D) (x y : C) :
    mapHom F x y ≫ inclusionHom D (F.obj x) (F.obj y) = inclusionHom C x y ≫ F.map x y := rfl

/-- The original full enriched functor restricts genuinely to the SAME original component-equivalence cores. -/
def map (F : C ⟶ D) : object C ⟶ object D where
  obj := F.obj
  map := mapHom F
  map_id x := by
    ext q a
    apply Subtype.ext
    exact congr($(F.map_id x).app q PUnit.unit)
  map_comp x y z := by
    ext q a
    apply Subtype.ext
    exact congr($(F.map_comp x y z).app q (a.1.val, a.2.val))

/-- Every SAME original object map is retained literally in the full core functor. -/
theorem map_obj (F : C ⟶ D) (x : object C) : (map F).obj x = F.obj x := rfl

/-- The actual entire original core inclusion square commutes on the SAME full enriched maps. -/
theorem inclusion_naturality (F : C ⟶ D) : map F ≫ inclusion D = inclusion C ≫ F := by
  apply EnrichedFunctor.ext SSet.{u} (F := map F ≫ inclusion D) (G := inclusion C ≫ F) (fun _ => rfl)
  intro x y
  exact Category.comp_id _

/-- The original core identity restriction is the SAME whole enriched identity. -/
theorem map_id (C : Carrier.{u}) : map (𝟙 C) = 𝟙 (object C) := by
  apply EnrichedFunctor.ext SSet.{u} (F := map (𝟙 C)) (G := 𝟙 (object C)) (fun _ => rfl)
  intro x y
  exact Category.comp_id _

/-- The whole original core maps retain the SAME original composition of both enriched functors. -/
theorem map_comp (F : C ⟶ D) (G : D ⟶ E) : map (F ≫ G) = map F ≫ map G := by
  apply EnrichedFunctor.ext SSet.{u} (F := map (F ≫ G)) (G := map F ≫ map G) (fun _ => rfl)
  intro x y
  exact Category.comp_id _

/-- The SAME genuine component-equivalence core functor on the full original changing-object carrier. -/
def functor : Carrier.{u} ⥤ Carrier.{u} where
  obj := object
  map := map
  map_id := map_id
  map_comp := map_comp

end CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore
