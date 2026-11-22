/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingStrictWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingKan
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKanRecognition

/-!
# Genuine DK recognition for the same original coherent-nerve map

The already proved strict enriched Hom comparison is identified with
the canonical raw right-mapping map by a whole endpoint Arrow Iso.
For actual locally Kan enrichments, categorical weakness of the nerve
is therefore exactly actual ordinary essential surjectivity together
with weakness of each supplied original enriched Hom map.

This is a theorem about the constructed nerve and actual maps. It does
not assume a Bergner model or an enriched source-cofibrancy certificate.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.NerveDwyerKan
open SimplicialEnrichment
variable {C D : Carrier.{u}} (F : C ⟶ D)

/-- The canonical raw right-mapping map and the proved original enriched-map comparison are the same whole
  arrow, with only the actual endpoint equality transport. -/
def mapArrowIso (x y : C) :
    CategoryTheory.Arrow.mk (SSet.mappingSpaceRight.map (coherentNerveFunctor.obj C)
      (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) (coherentNerveFunctor.map F)) ≅
        CategoryTheory.Arrow.mk (MappingStrictNaturality.map F x y) :=
  CategoryTheory.Arrow.isoMk (Iso.refl (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
      (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)))
    (SSet.PointedRightMappingSpace.endpointIso (HomStrictMaps.vertex_map F x)
      (HomStrictMaps.vertex_map F y)) (by
      have h : MappingStrictNaturality.map F x y =
          SSet.mappingSpaceRight.map (coherentNerveFunctor.obj C)
            (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)
            (coherentNerveFunctor.map F) ≫
              (SSet.PointedRightMappingSpace.endpointIso (HomStrictMaps.vertex_map F x)
                (HomStrictMaps.vertex_map F y)).hom := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro σ
        apply Subtype.ext
        exact (MappingStrictNaturality.map_val F x y n σ).trans
          (SSet.PointedRightMappingSpace.endpointIso_hom_val (HomStrictMaps.vertex_map F x)
            (HomStrictMaps.vertex_map F y) n
            ((SSet.mappingSpaceRight.map (coherentNerveFunctor.obj C)
              (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)
              (coherentNerveFunctor.map F)).app n σ)).symm
      exact (Category.id_comp (MappingStrictNaturality.map F x y)).trans h)

/-- Weakness of the canonical same-map right mapping space is exactly weakness of the actual supplied
  original enriched Hom map at Kan endpoints. -/
theorem raw_map_weak_iff (x y : C) [SSet.KanComplex (x ⟶[SSet.{u}] y)]
    [SSet.KanComplex (F.obj x ⟶[SSet.{u}] F.obj y)] :
    SSet.realizationWeakEquivalences
        (SSet.mappingSpaceRight.map (coherentNerveFunctor.obj C)
          (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)
          (coherentNerveFunctor.map F)) ↔ SSet.realizationWeakEquivalences (F.map x y) :=
  (SSet.realizationWeakEquivalences.arrow_mk_iso_iff (mapArrowIso F x y)).trans
    (MappingStrictNaturality.map_weak_iff F x y)

private theorem exists_vertex (C : Carrier.{u})
    (a : (Δ[0] : SSet.{u}) ⟶ coherentNerveFunctor.obj C) :
    ∃ x : C, HomSimplexEndpoints.vertex x = a := by
  refine ⟨verticesEquiv C (SSet.yonedaEquiv a), ?_⟩
  apply SSet.yonedaEquiv.injective
  change constantSimplex C ⦋0⦌ (verticesEquiv C (SSet.yonedaEquiv a)) = SSet.yonedaEquiv a
  exact (verticesEquiv C).symm_apply_apply _

/-- Full faithfulness of the actual original coherent-nerve map is exactly weakness on each original
  enriched Hom, under genuine locally Kan hypotheses. -/
theorem nerve_fullyFaithful_iff
    (hC : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    SSet.dwyerKanFullyFaithful (coherentNerveFunctor.map F) ↔
      ∀ x y : C, SSet.realizationWeakEquivalences (F.map x y) := by
  constructor
  · intro h x y
    let _ := hC x y
    let _ := hD (F.obj x) (F.obj y)
    exact (raw_map_weak_iff F x y).mp (h (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y))
  · intro h a b
    obtain ⟨x, rfl⟩ := exists_vertex C a
    obtain ⟨y, rfl⟩ := exists_vertex C b
    let _ := hC x y
    let _ := hD (F.obj x) (F.obj y)
    exact (raw_map_weak_iff F x y).mpr (h x y)

/-- Genuine categorical equivalence of the same original coherent-nerve map is exactly its actual ordinary
  essential surjectivity and local original Hom weakness. -/
theorem nerve_categoricalEquivalence_iff
    (hC : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    SSet.categoricalEquivalences (coherentNerveFunctor.map F) ↔
      SSet.dwyerKanEssentiallySurjective (coherentNerveFunctor.map F) ∧
        ∀ x y : C, SSet.realizationWeakEquivalences (F.map x y) := by
  let _ := coherentNerve_quasicategory C hC
  let _ := coherentNerve_quasicategory D hD
  constructor
  · intro h
    have hDK := h.isDwyerKanEquivalence
    exact ⟨hDK.1, (nerve_fullyFaithful_iff F hC hD).mp hDK.2⟩
  · rintro ⟨hES, hMap⟩
    exact (show SSet.isDwyerKanEquivalence (coherentNerveFunctor.map F) from
      ⟨hES, (nerve_fullyFaithful_iff F hC hD).mpr hMap⟩).categoricalEquivalences

/-- Surjectivity on the supplied original enriched objects gives actual essential surjectivity of the same
  original coherent-nerve map. -/
theorem nerve_essentiallySurjective_of_surjective_objects (hF : Function.Surjective F.obj) :
    SSet.dwyerKanEssentiallySurjective (coherentNerveFunctor.map F) := by
  have hV : Function.Surjective ((coherentNerveFunctor.map F).app (op ⦋0⦌)) := by
    intro σ
    obtain ⟨x, hx⟩ := hF (verticesEquiv D σ)
    refine ⟨(verticesEquiv C).symm x, ?_⟩
    apply (verticesEquiv D).injective
    rw [verticesEquiv_map, Equiv.apply_symm_apply, hx]
  apply Functor.essSurj_of_surj
  intro a
  cases a using SSet.HomotopyCategory.rec with
  | mk σ =>
    obtain ⟨τ, hτ⟩ := hV σ
    exact ⟨SSet.HomotopyCategory.mk τ, congrArg SSet.HomotopyCategory.mk hτ⟩

/-- A genuinely locally Kan original enriched map which is surjective on original objects and weak on all
  original Hom objects has a categorical-equivalence coherent nerve. -/
theorem nerve_categoricalEquivalence_of_surjective_objects
    (hC : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hF : Function.Surjective F.obj)
    (hMap : ∀ x y : C, SSet.realizationWeakEquivalences (F.map x y)) :
    SSet.categoricalEquivalences (coherentNerveFunctor.map F) :=
  (nerve_categoricalEquivalence_iff F hC hD).mpr
    ⟨nerve_essentiallySurjective_of_surjective_objects F hF, hMap⟩

end CategoryTheory.CoherentRealization.NerveDwyerKan
