/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCofreeEnrichment

/-!
# The genuine whole cofree scalar-functor universal property

A functor from the SAME canonical scalar category extends to all
original enriched coefficients by every full ordinal operator. Reading
the actual identity operator recovers both entire original functors.
Original source and target object universes remain independent.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory

namespace SSet.ScalarCofree

variable (q : SimplexCategoryᵒᵖ) {C : Type v} [EnrichedCategory SSet.{u} C]
  (E : Type w) [Category.{u} E]

/-- The SAME original scalar functor supplies every full original coefficient at all operators. -/
def ofFunctor (F : ScalarObject C q ⥤ E) :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    EnrichedFunctor SSet.{u} C E := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  exact {
    obj x := F.obj ⟨x⟩
    map x y := {
      app _n := ↾fun h θ => F.map ((x ⟶[SSet.{u}] y).map θ h)
      naturality _n _m f := by
        apply ConcreteCategory.hom_ext
        intro h
        funext θ
        exact congrArg (fun a : (⟨x⟩ : ScalarObject C q) ⟶ ⟨y⟩ => F.map a)
          (Functor.map_comp_apply (x ⟶[SSet.{u}] y) f θ h).symm }
    map_id x := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro _h
      funext θ
      have h : (((x ⟶[SSet.{u}] x).map θ ((eId SSet.{u} x).app n PUnit.unit)) :
          (⟨x⟩ : ScalarObject C q) ⟶ ⟨x⟩) = 𝟙 (⟨x⟩ : ScalarObject C q) :=
        (NatTrans.naturality_apply (eId SSet.{u} x) θ PUnit.unit).symm
      exact (congrArg (fun a : (⟨x⟩ : ScalarObject C q) ⟶ ⟨x⟩ => F.map a) h).trans (F.map_id ⟨x⟩)
    map_comp x y z := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro h
      funext θ
      have ht : (x ⟶[SSet.{u}] z).map θ ((eComp SSet.{u} x y z).app n h) =
          (eComp SSet.{u} x y z).app q
            ((x ⟶[SSet.{u}] y).map θ h.1, (y ⟶[SSet.{u}] z).map θ h.2) :=
        (NatTrans.naturality_apply (eComp SSet.{u} x y z) θ h).symm
      exact (congrArg (fun a : (⟨x⟩ : ScalarObject C q) ⟶ ⟨z⟩ => F.map a) ht).trans
        (F.map_comp (X := (⟨x⟩ : ScalarObject C q)) (Y := (⟨y⟩ : ScalarObject C q))
          (Z := (⟨z⟩ : ScalarObject C q)) ((x ⟶[SSet.{u}] y).map θ h.1) ((y
            ⟶[SSet.{u}] z).map θ h.2)) }

/-- Read the SAME actual original scalar functor through the complete cofree
identity-operator evaluation. -/
def toFunctor :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    EnrichedFunctor SSet.{u} C E → (ScalarObject C q ⥤ E) := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  exact fun G => scalarFunctor G q ⋙ evaluation q E

/-- Reading the full original extension recovers the SAME entire original scalar functor. -/
theorem toFunctor_ofFunctor (F : ScalarObject C q ⥤ E) :
    toFunctor q E (ofFunctor q E F) = F := by
  apply Functor.hext (F := toFunctor q E (ofFunctor q E F)) (G := F) (fun _ => rfl)
  intro x y h
  exact heq_of_eq (congrArg (fun a : x ⟶ y => F.map a)
    (Functor.map_id_apply (x.obj ⟶[SSet.{u}] y.obj) q h))

/-- Extending and reading every original coefficient recovers the SAME entire original
enriched functor. -/
theorem ofFunctor_toFunctor :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    ∀ G : EnrichedFunctor SSet.{u} C E, ofFunctor q E (toFunctor q E G) = G := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  dsimp only
  intro G
  apply EnrichedFunctor.ext SSet.{u} (F := ofFunctor q E (toFunctor q E G)) (G := G) (fun _ => rfl)
  intro x y
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro h
  funext θ
  have hn := congrArg (fun a : (homObject q E (G.obj x) (G.obj y)).obj q => a (𝟙 q))
    (NatTrans.naturality_apply (G.map x y) θ h)
  exact hn.trans (congrArg ((G.map x y).app n h) (Category.comp_id θ))

/-- The complete genuine original cofree Hom bijection retains both full original inverse
functors. -/
def homEquiv :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    EnrichedFunctor SSet.{u} C E ≃ (ScalarObject C q ⥤ E) := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  exact {
    toFun := toFunctor q E
    invFun := ofFunctor q E
    left_inv := ofFunctor_toFunctor q E
    right_inv := toFunctor_ofFunctor q E }

end SSet.ScalarCofree
