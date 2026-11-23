/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopPair.GoodPairPointQuotient

/-!
# Good-pair contractions in point-quotient neighborhoods

The chosen deformation of a good pair descends through the restricted quotient
projection and contracts the resulting quotient neighborhood to its distinguished point.
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace TopPair

local notation "forgetToArrow" => MorphismProperty.Arrow.forget _ _ _

namespace GoodPairData

variable {P : TopPair.{u}} (d : GoodPairData P)

set_option backward.isDefEq.respectTransparency false

/-- The quotient projection restricted to the chosen good-pair neighborhood. -/
noncomputable def pointQuotientNeighborhoodProjection :
    TopCat.of d.neighborhood ⟶ TopCat.of d.pointQuotientNeighborhood :=
  let e := Homeomorph.setCongr
    d.pointQuotientProjection_preimage_neighborhood.symm
  TopCat.ofHom
    (((TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom.restrictPreimage
        d.pointQuotientNeighborhood).comp
      { toFun := e
        continuous_toFun := e.continuous })

@[simp]
theorem pointQuotientNeighborhoodProjection_val (x : d.neighborhood) :
    (d.pointQuotientNeighborhoodProjection x).1 =
      TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) x.1 :=
  rfl

/-- The restricted neighborhood projection is a quotient map. -/
theorem pointQuotientNeighborhoodProjection_isQuotientMap :
    IsQuotientMap d.pointQuotientNeighborhoodProjection.hom := by
  let _ : Nonempty (((forgetToArrow).obj P).left) := d.nonempty_snd
  exact
    ((TopCat.pointQuotientProjection_isQuotientMap
      ((forgetToArrow).obj P)).restrictPreimage_isOpen
        d.isOpen_pointQuotientNeighborhood).comp
      (Homeomorph.setCongr
        d.pointQuotientProjection_preimage_neighborhood.symm).isQuotientMap

/-- The unique map from the quotient neighborhood to a point. -/
noncomputable def pointQuotientNeighborhoodRetraction :
    TopCat.of d.pointQuotientNeighborhood ⟶ TopCat.of PUnit :=
  TopCat.isTerminalPUnit.from _

/-- The chosen deformation is constant on fibers of the restricted quotient projection. -/
theorem pointQuotientNeighborhoodDeformation_factors
    (t : unitInterval) :
    Function.FactorsThrough
      (fun x => d.pointQuotientNeighborhoodProjection
        (d.deformation (t, x)))
      d.pointQuotientNeighborhoodProjection := by
  let _ : Nonempty (((forgetToArrow).obj P).left) := d.nonempty_snd
  intro x y hxy
  apply Subtype.ext
  rw [d.pointQuotientNeighborhoodProjection_val,
    d.pointQuotientNeighborhoodProjection_val]
  have hqxy :
      TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) x.1 =
        TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) y.1 := by
    exact congrArg Subtype.val hxy
  by_cases hxrange : x.1 ∈ Set.range P.map
  · have hyrange : y.1 ∈ Set.range P.map := by
      have hxpoint :
          TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) x.1 =
            TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit := by
        have hxmem : x.1 ∈
            (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
              {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} := by
          rw [TopCat.pointQuotientProjection_preimage_singleton]
          exact hxrange
        exact hxmem
      have hypoint :
          TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) y.1 =
            TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit :=
        hqxy.symm.trans hxpoint
      have hymem : y.1 ∈
        (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
          {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :=
        hypoint
      rw [TopCat.pointQuotientProjection_preimage_singleton] at hymem
      exact hymem
    have hxrel : x ∈ Set.range d.inclusion.hom := by
      rcases hxrange with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact ha
    have hyrel : y ∈ Set.range d.inclusion.hom := by
      rcases hyrange with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact ha
    rw [d.deformation.eq_fst t hxrel, d.deformation.eq_fst t hyrel]
    exact hqxy
  · have hyrange : y.1 ∉ Set.range P.map := by
      intro hyrange
      apply hxrange
      have hypoint :
          TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) y.1 =
            TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit := by
        have hymem : y.1 ∈
            (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
              {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} := by
          rw [TopCat.pointQuotientProjection_preimage_singleton]
          exact hyrange
        exact hymem
      have hxpoint :
          TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) x.1 =
            TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit :=
        hqxy.trans hypoint
      have hxmem : x.1 ∈
        (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
          {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :=
        hxpoint
      rw [TopCat.pointQuotientProjection_preimage_singleton] at hxmem
      exact hxmem
    have hxnotpoint :
        TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) x.1 ≠
          TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit := by
      intro hxpoint
      apply hxrange
      have hxmem : x.1 ∈
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
            {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :=
        hxpoint
      rw [TopCat.pointQuotientProjection_preimage_singleton] at hxmem
      exact hxmem
    have hynotpoint :
        TopCat.pointQuotientProjection.app ((forgetToArrow).obj P) y.1 ≠
          TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit := by
      intro hypoint
      apply hyrange
      have hymem : y.1 ∈
          (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
            {TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :=
        hypoint
      rw [TopCat.pointQuotientProjection_preimage_singleton] at hymem
      exact hymem
    let x' :
        (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
          ({TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :
            Set (TopCat.pointQuotient ((forgetToArrow).obj P)))ᶜ :=
      ⟨x.1, hxnotpoint⟩
    let y' :
        (TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)).hom ⁻¹'
          ({TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :
            Set (TopCat.pointQuotient ((forgetToArrow).obj P)))ᶜ :=
      ⟨y.1, hynotpoint⟩
    have hxy' : x' = y' := by
      apply (TopCat.pointQuotientProjection_isHomeomorph_compl_of_isClosed_range
        ((forgetToArrow).obj P) d.isClosed_range).injective
      apply Subtype.ext
      exact hqxy
    have hxyval : x.1 = y.1 := congrArg (fun z => z.1) hxy'
    have hxy_subtype : x = y := by
      apply Subtype.ext
      exact hxyval
    rw [hxy_subtype]

/-- The chosen good-pair deformation descends to a contraction of the quotient
neighborhood onto the distinguished point. -/
noncomputable def pointQuotientNeighborhoodDeformation :
    TopCat.Homotopy (𝟙 (TopCat.of d.pointQuotientNeighborhood))
      (d.pointQuotientNeighborhoodRetraction ≫
        d.pointQuotientNeighborhoodInclusion) := by
  let raw : C(unitInterval × d.neighborhood,
      d.pointQuotientNeighborhood) :=
    d.pointQuotientNeighborhoodProjection.hom.comp
      d.deformation.toHomotopy.toContinuousMap
  refine TopCat.Homotopy.ofQuotientMap
    d.pointQuotientNeighborhoodProjection
    d.pointQuotientNeighborhoodProjection_isQuotientMap raw ?_ ?_ ?_
  · intro x
    apply Subtype.ext
    simp [raw]
  · intro x
    apply Subtype.ext
    change
      (d.pointQuotientNeighborhoodProjection
          (d.deformation (1, x))).1 =
        (d.pointQuotientNeighborhoodInclusion
          (d.pointQuotientNeighborhoodRetraction
            (d.pointQuotientNeighborhoodProjection x))).1
    rw [d.pointQuotientNeighborhoodProjection_val,
      d.pointQuotientNeighborhoodInclusion_val]
    change
      TopCat.pointQuotientProjection.app ((forgetToArrow).obj P)
          (d.deformation (1, x)).1 =
        TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit
    rw [d.deformation.apply_one]
    exact ConcreteCategory.congr_hom
      (TopCat.pointQuotient_condition ((forgetToArrow).obj P))
      (d.retraction x)
  · exact d.pointQuotientNeighborhoodDeformation_factors

@[simp]
theorem pointQuotientNeighborhoodDeformation_apply_projection
    (t : unitInterval) (x : d.neighborhood) :
    d.pointQuotientNeighborhoodDeformation
        (t, d.pointQuotientNeighborhoodProjection x) =
      d.pointQuotientNeighborhoodProjection (d.deformation (t, x)) := by
  unfold pointQuotientNeighborhoodDeformation
  apply TopCat.Homotopy.ofQuotientMap_apply

/-- The distinguished point is a homotopy equivalent model for the quotient
neighborhood. -/
noncomputable def pointQuotientNeighborhoodHomotopyEquiv :
    ContinuousMap.HomotopyEquiv PUnit d.pointQuotientNeighborhood where
  toFun := d.pointQuotientNeighborhoodInclusion.hom
  invFun := d.pointQuotientNeighborhoodRetraction.hom
  left_inv := by
    rw [show d.pointQuotientNeighborhoodRetraction.hom.comp
      d.pointQuotientNeighborhoodInclusion.hom =
        ContinuousMap.id PUnit by
      ext p]
  right_inv := ⟨d.pointQuotientNeighborhoodDeformation.symm⟩

@[simp]
theorem pointQuotientNeighborhoodHomotopyEquiv_toFun :
    d.pointQuotientNeighborhoodHomotopyEquiv.toFun =
      d.pointQuotientNeighborhoodInclusion.hom :=
  rfl

@[simp]
theorem pointQuotientNeighborhoodHomotopyEquiv_invFun :
    d.pointQuotientNeighborhoodHomotopyEquiv.invFun =
      d.pointQuotientNeighborhoodRetraction.hom :=
  rfl

end GoodPairData

end TopPair
