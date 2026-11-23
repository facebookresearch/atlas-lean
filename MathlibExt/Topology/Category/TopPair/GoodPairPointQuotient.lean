/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopPair.GoodPair
public import MathlibExt.Topology.Category.TopPair.PointQuotient

/-!
# Good-pair neighborhoods in point quotients

The chosen neighborhood of a good pair descends to an open neighborhood of the
distinguished point in the point quotient.
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace TopPair

local notation "forgetToArrow" => MorphismProperty.Arrow.forget _ _ _

namespace GoodPairData

variable {P : TopPair.{u}} (d : GoodPairData P)

/-- The image of the chosen good-pair neighborhood in the point quotient. -/
noncomputable def pointQuotientNeighborhood :
    Set (TopCat.pointQuotient ((forgetToArrow).obj P)) :=
  (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ''
    d.neighborhood

/-- The chosen neighborhood is saturated for the point-quotient projection. -/
theorem pointQuotientProjection_preimage_neighborhood :
    (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
      d.pointQuotientNeighborhood = d.neighborhood := by
  let _ : Nonempty (((forgetToArrow).obj P).left) := d.nonempty_snd
  apply Set.Subset.antisymm
  · intro x hx
    change
      (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom x ∈
        (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ''
          d.neighborhood at hx
    rcases hx with ⟨y, hy, hq⟩
    by_cases hyrange : y ∈ Set.range P.map
    · have hypoint :
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom y =
            TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit := by
        change y ∈
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
            {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit}
        rw [TopCat.pointQuotientProjection_preimage_singleton]
        exact hyrange
      have hxpoint :
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom x =
            TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit :=
        hq.symm.trans hypoint
      have hxfiber : x ∈
        (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
          {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :=
        hxpoint
      rw [TopCat.pointQuotientProjection_preimage_singleton] at hxfiber
      rcases hxfiber with ⟨a, ha⟩
      apply d.range_subset_neighborhood
      refine ⟨a, ?_⟩
      exact ha
    · have hynotpoint :
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom y ≠
            TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit := by
        intro hypoint
        apply hyrange
        have hyfiber : y ∈
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
            {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :=
          hypoint
        rw [TopCat.pointQuotientProjection_preimage_singleton] at hyfiber
        rcases hyfiber with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        exact ha
      have hxnotpoint :
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom x ≠
            TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit := by
        intro hxpoint
        exact hynotpoint (hq.trans hxpoint)
      let y' :
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
            ({TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :
              Set (TopCat.pointQuotient ((forgetToArrow).obj P)))ᶜ :=
        ⟨y, by
          change
            (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom y ≠
              TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit
          exact hynotpoint⟩
      let x' :
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
            ({TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :
              Set (TopCat.pointQuotient ((forgetToArrow).obj P)))ᶜ :=
        ⟨x, by
          change
            (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom x ≠
              TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit
          exact hxnotpoint⟩
      have hyx' : y' = x' := by
        apply (TopCat.pointQuotientProjection_isHomeomorph_compl_of_isClosed_range
          ((forgetToArrow).obj P) d.isClosed_range).injective
        apply Subtype.ext
        exact hq
      have hyx : y = x := congrArg Subtype.val hyx'
      simpa [hyx] using hy
  · intro x hx
    exact ⟨x, hx, rfl⟩

/-- The image neighborhood is open in the point quotient. -/
theorem isOpen_pointQuotientNeighborhood :
    IsOpen d.pointQuotientNeighborhood := by
  let _ : Nonempty (((forgetToArrow).obj P).left) := d.nonempty_snd
  apply (TopCat.pointQuotientProjection_isQuotientMap
    ((forgetToArrow).obj P)).isCoinducing.isOpen_preimage.mp
  rw [d.pointQuotientProjection_preimage_neighborhood]
  exact d.isOpen_neighborhood

/-- The distinguished quotient point lies in the image neighborhood. -/
theorem pointQuotientPoint_mem_pointQuotientNeighborhood :
    TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit ∈
      d.pointQuotientNeighborhood := by
  let a : P.snd := Classical.choice d.nonempty_snd
  refine ⟨P.map a, d.range_subset_neighborhood ⟨a, rfl⟩, ?_⟩
  change P.map a ∈
    (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
      {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit}
  rw [TopCat.pointQuotientProjection_preimage_singleton]
  exact ⟨a, rfl⟩

end GoodPairData

namespace GoodPairData

variable {P : TopPair.{u}} (d : GoodPairData P)

/-- The point quotient paired with the image of the chosen neighborhood. -/
noncomputable abbrev pointQuotientNeighborhoodPair : TopPair.{u} :=
  TopPair.ofSubset d.pointQuotientNeighborhood

/-- The distinguished quotient point as a map into its chosen neighborhood. -/
noncomputable def pointQuotientNeighborhoodInclusion :
    TopCat.of PUnit ⟶ TopCat.of d.pointQuotientNeighborhood :=
  TopCat.const
    ⟨TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit,
      d.pointQuotientPoint_mem_pointQuotientNeighborhood⟩

@[simp]
theorem pointQuotientNeighborhoodInclusion_val (p : PUnit) :
    (d.pointQuotientNeighborhoodInclusion p).1 =
      TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit :=
  rfl

/-- The pointed quotient pair maps canonically to the quotient-neighborhood pair. -/
noncomputable def pointQuotientPairToNeighborhoodPair :
    pointQuotientPairFunctor.obj P ⟶ d.pointQuotientNeighborhoodPair :=
  TopPair.ofHom (𝟙 _) d.pointQuotientNeighborhoodInclusion (by
    apply TopCat.hom_ext
    ext p
    cases p
    rfl)

@[simp]
theorem pointQuotientPairToNeighborhoodPair_fst :
    TopPair.Hom.fst d.pointQuotientPairToNeighborhoodPair = 𝟙 _ :=
  rfl

@[simp]
theorem pointQuotientPairToNeighborhoodPair_snd :
    TopPair.Hom.snd d.pointQuotientPairToNeighborhoodPair =
      d.pointQuotientNeighborhoodInclusion :=
  rfl

end GoodPairData

end TopPair
