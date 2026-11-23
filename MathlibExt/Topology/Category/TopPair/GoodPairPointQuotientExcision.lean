/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopPair.Excision
public import MathlibExt.Topology.Category.TopPair.GoodPairPointQuotientHomotopy
public import MathlibExt.Topology.Homeomorph.Set

/-!
# Good-pair excision comparison for point quotients

The point-quotient projection identifies the complementary excision source
pairs and gives the two commuting squares used by the relative-homology
comparison for a good pair.
-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

universe u

namespace TopPair

local notation "forgetToArrow" => MorphismProperty.Arrow.forget _ _ _

namespace GoodPairData

variable {P : TopPair.{u}} (d : GoodPairData P)

set_option backward.isDefEq.respectTransparency false

local notation "Q" =>
  TopCat.pointQuotient
    (Functor.obj (MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤) P)
local notation "q" =>
  NatTrans.app TopCat.pointQuotientProjection
    (Functor.obj (MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤) P)
local notation "p" =>
  TopCat.pointQuotientPoint
    (Functor.obj (MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤) P) PUnit.unit

/-- The quotient projection as a map from the chosen neighborhood pair to its
image-neighborhood pair. -/
noncomputable def neighborhoodPairToPointQuotientNeighborhoodPair :
    d.neighborhoodPair ⟶ d.pointQuotientNeighborhoodPair :=
  TopPair.ofHom q d.pointQuotientNeighborhoodProjection (by
    apply TopCat.hom_ext
    ext x
    exact d.pointQuotientNeighborhoodProjection_val x)

@[simp]
theorem neighborhoodPairToPointQuotientNeighborhoodPair_fst :
    TopPair.Hom.fst d.neighborhoodPairToPointQuotientNeighborhoodPair =
      q :=
  rfl

@[simp]
theorem neighborhoodPairToPointQuotientNeighborhoodPair_snd :
    TopPair.Hom.snd d.neighborhoodPairToPointQuotientNeighborhoodPair =
      d.pointQuotientNeighborhoodProjection :=
  rfl

/-- The collapsed closed range has closure contained in the chosen open
neighborhood. -/
theorem closure_range_subset_interior_neighborhood :
    closure (Set.range P.map) ⊆ interior d.neighborhood := by
  simpa [d.isClosed_range.closure_eq, d.isOpen_neighborhood.interior_eq] using
    d.range_subset_neighborhood

/-- The closed distinguished quotient point has closure contained in the open
quotient neighborhood. -/
theorem closure_point_subset_interior_pointQuotientNeighborhood :
    closure ({p} : Set Q) ⊆
      interior d.pointQuotientNeighborhood := by
  let _ : Nonempty (((forgetToArrow).obj P).left) := d.nonempty_snd
  have hp : IsClosed ({p} : Set Q) :=
    TopCat.pointQuotientPoint_isClosed_of_isClosed_range
      ((forgetToArrow).obj P) d.isClosed_range
  simpa [hp.closure_eq, d.isOpen_pointQuotientNeighborhood.interior_eq] using
    d.pointQuotientPoint_mem_pointQuotientNeighborhood

/-- The point-quotient projection is a homeomorphism away from the collapsed
closed range and the distinguished point. -/
noncomputable def pointQuotientComplementHomeomorph :
    ((Set.range P.map)ᶜ : Set P.fst) ≃ₜ
      (({p} : Set Q)ᶜ : Set Q) := by
  let _ : Nonempty (((forgetToArrow).obj P).left) := d.nonempty_snd
  let e :
      (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
          (({p} : Set Q)ᶜ : Set Q) ≃ₜ
        (({p} : Set Q)ᶜ : Set Q) :=
    (TopCat.pointQuotientProjection_isHomeomorph_compl_of_isClosed_range
      ((forgetToArrow).obj P) d.isClosed_range).homeomorph _
  exact
    (Homeomorph.setCongr (by
      rw [Set.preimage_compl]
      exact congrArg (fun s : Set P.fst => sᶜ)
        (TopCat.pointQuotientProjection_preimage_singleton
          ((forgetToArrow).obj P)).symm)).trans e

@[simp]
theorem pointQuotientComplementHomeomorph_apply
    (x : ((Set.range P.map)ᶜ : Set P.fst)) :
    (d.pointQuotientComplementHomeomorph x).1 =
      q x.1 :=
  rfl

/-- Restricting the complementary homeomorphism identifies the two
intersection subspaces in the excision sources. -/
noncomputable def pointQuotientNeighborhoodComplementHomeomorph :
    (d.neighborhood ∩ ((Set.range P.map)ᶜ : Set P.fst) : Set P.fst) ≃ₜ
      (d.pointQuotientNeighborhood ∩
        (({p} : Set Q)ᶜ : Set Q) : Set Q) :=
  Homeomorph.inter d.pointQuotientComplementHomeomorph (fun z => by
    rw [d.pointQuotientComplementHomeomorph_apply]
    change z.1 ∈ d.neighborhood ↔
      (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)) z.1 ∈
        d.pointQuotientNeighborhood
    simpa only [Set.mem_preimage] using
      (Set.ext_iff.mp d.pointQuotientProjection_preimage_neighborhood z.1).symm)

@[simp]
theorem pointQuotientNeighborhoodComplementHomeomorph_apply
    (x : (d.neighborhood ∩ ((Set.range P.map)ᶜ : Set P.fst) : Set P.fst)) :
    (d.pointQuotientNeighborhoodComplementHomeomorph x).1 =
      q x.1 :=
  rfl

/-- The complementary homeomorphisms assemble into an isomorphism between the
two excision source pairs. -/
noncomputable def pointQuotientExcisionSourceIso :
    TopPair.excisionSource P.fst d.neighborhood
        ((Set.range P.map)ᶜ : Set P.fst) ≅
      TopPair.excisionSource Q d.pointQuotientNeighborhood
        (({p} : Set Q)ᶜ : Set Q) :=
  CategoryTheory.MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo d.pointQuotientNeighborhoodComplementHomeomorph)
    (TopCat.isoOfHomeo d.pointQuotientComplementHomeomorph) (by
      apply TopCat.hom_ext
      ext x
      rfl)

/-- The source-pair isomorphism intertwines the two excision morphisms with the
restricted quotient map. -/
theorem pointQuotientExcision_square :
    d.pointQuotientExcisionSourceIso.hom ≫
        TopPair.excisionHom Q d.pointQuotientNeighborhood
          (({p} : Set Q)ᶜ : Set Q) =
      TopPair.excisionHom P.fst d.neighborhood
          ((Set.range P.map)ᶜ : Set P.fst) ≫
        d.neighborhoodPairToPointQuotientNeighborhoodPair := by
  apply CategoryTheory.MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    ext x
    apply Subtype.ext
    exact d.pointQuotientNeighborhoodComplementHomeomorph_apply x
  · apply TopCat.hom_ext
    ext x
    exact d.pointQuotientComplementHomeomorph_apply x

/-- The good-pair neighborhood enlargement square commutes with the canonical
point-quotient comparison. -/
theorem pointQuotientComparison_neighborhood_square :
    d.toNeighborhoodPair ≫
        d.neighborhoodPairToPointQuotientNeighborhoodPair =
      pointQuotientComparison.app P ≫
        d.pointQuotientPairToNeighborhoodPair := by
  apply CategoryTheory.MorphismProperty.Arrow.Hom.ext
  · simp only [MorphismProperty.Comma.comp_left,
      toNeighborhoodPair_snd,
      neighborhoodPairToPointQuotientNeighborhoodPair_snd,
      pointQuotientComparison_app_snd,
      pointQuotientPairToNeighborhoodPair_snd]
    apply TopCat.hom_ext
    ext x
    change d.pointQuotientNeighborhoodProjection (d.inclusion x) =
      d.pointQuotientNeighborhoodInclusion
        (TopCat.isTerminalPUnit.from P.snd x)
    apply Subtype.ext
    rw [d.pointQuotientNeighborhoodProjection_val,
      d.pointQuotientNeighborhoodInclusion_val]
    exact ConcreteCategory.congr_hom
      (TopCat.pointQuotient_condition ((forgetToArrow).obj P)) x
  · simp only [MorphismProperty.Comma.comp_right,
      toNeighborhoodPair_fst,
      neighborhoodPairToPointQuotientNeighborhoodPair_fst,
      pointQuotientComparison_app_fst,
      pointQuotientPairToNeighborhoodPair_fst]
    simp only [Category.id_comp, Category.comp_id]

end GoodPairData

end TopPair
