/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCofreeFunctorUniversal

/-!
# The same complete cofree scalar maps and universal-map naturality

Every ordinary functor acts on each complete operator-indexed
Hom family. The full inverse functor bijection is natural in
both the source enrichment and the ordinary target.
All object and coefficient universes remain independent.
-/

noncomputable section
universe u v w z t
open CategoryTheory

namespace SSet.ScalarCofree

variable (q : SimplexCategoryᵒᵖ) {E : Type v} [Category.{u} E] {D : Type w} [Category.{u} D]

/-- The same ordinary functor acts on every operator family. -/
def map (F : E ⥤ D) :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    let _ : EnrichedCategory SSet.{u} D := enrichment q D
    EnrichedFunctor SSet.{u} E D := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  let _ : EnrichedCategory SSet.{u} D := enrichment q D
  exact {
    obj := F.obj
    map _x _y := {
      app _n := ↾fun h θ => F.map (h θ)
      naturality _n _m _f := by
        apply ConcreteCategory.hom_ext
        intro h
        rfl }
    map_id x := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro _h
      funext θ
      exact F.map_id x
    map_comp _x _y _z := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro h
      funext θ
      exact F.map_comp (h.1 θ) (h.2 θ) }

/-- The same full cofree identity is the enriched identity. -/
theorem map_id :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    map q (𝟭 E) = EnrichedFunctor.id SSet.{u} E := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  apply EnrichedFunctor.ext SSet.{u} (F := map q (𝟭 E)) (G :=
    EnrichedFunctor.id SSet.{u} E) (fun _ => rfl)
  intro x y
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro h
  rfl

/-- The cofree map retains composition of the same complete ordinary functors. -/
theorem map_comp {K : Type z} [Category.{u} K] (F : E ⥤ D) (G : D ⥤ K) :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    let _ : EnrichedCategory SSet.{u} D := enrichment q D
    let _ : EnrichedCategory SSet.{u} K := enrichment q K
    map q (F ⋙ G) = (map q F).comp SSet.{u} (map q G) := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  let _ : EnrichedCategory SSet.{u} D := enrichment q D
  let _ : EnrichedCategory SSet.{u} K := enrichment q K
  apply EnrichedFunctor.ext SSet.{u}
    (F := map q (F ⋙ G)) (G := (map q F).comp SSet.{u} (map q G)) (fun _ => rfl)
  intro x y
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro h
  rfl

/-- The cofree universal map retains the same ordinary target
postcomposition. -/
theorem ofFunctor_target {C : Type t} [EnrichedCategory SSet.{u} C]
    (F : ScalarObject C q ⥤ E) (G : E ⥤ D) :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    let _ : EnrichedCategory SSet.{u} D := enrichment q D
    (ofFunctor q E F).comp SSet.{u} (map q G) = ofFunctor q D (F ⋙ G) := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  let _ : EnrichedCategory SSet.{u} D := enrichment q D
  apply EnrichedFunctor.ext SSet.{u}
    (F := (ofFunctor q E F).comp SSet.{u} (map q G)) (G := ofFunctor q D (F ⋙ G)) (fun _ => rfl)
  intro x y
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro h
  rfl

/-- Reading the universal functor retains the same full enriched source
precomposition. -/
theorem toFunctor_source {C : Type z} [EnrichedCategory SSet.{u} C]
    {K : Type t} [EnrichedCategory SSet.{u} K] (F : EnrichedFunctor SSet.{u} C K) :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    ∀ G : EnrichedFunctor SSet.{u} K E,
      toFunctor q E (F.comp SSet.{u} G) = scalarFunctor F q ⋙ toFunctor q E G := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  dsimp only
  intro G
  rfl

end SSet.ScalarCofree
