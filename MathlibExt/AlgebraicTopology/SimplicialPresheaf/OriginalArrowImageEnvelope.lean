/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CardinalSubarrowPresentation
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellReplacement
import MathlibExt.CategoryTheory.Presentable.BoundedPresheafArrows
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Original bounded arrows and larger replacement images

The representatives and point maps live on the original presheaf carrier.
A set of actual replacement images gives a uniform larger bound and both
endpoint presentability ranks, without a preservation assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D]

/-- An original isomorphism maps each point through its component at the SAME site and degree. -/
def originalTotalPointsEquivOfIso {X Y : SimplicialPresheaf.{u} D} (e : X ≅ Y) :
    originalTotalPoints X ≃ originalTotalPoints Y where
  toFun p := ⟨p.1, Functor.elementsMk (Y.obj p.1) p.2.obj
    (((e.hom.app p.1).app p.2.obj) p.2.val)⟩
  invFun p := ⟨p.1, Functor.elementsMk (X.obj p.1) p.2.obj
    (((e.inv.app p.1).app p.2.obj) p.2.val)⟩
  left_inv := by
    rintro ⟨d, q⟩
    cases q with
    | @mk n x =>
      have hx := congrArg (fun k : X ⟶ X => ((k.app d).app n) x) e.hom_inv_id
      exact congrArg (fun z => (⟨d, Functor.elementsMk (X.obj d) n z⟩ : originalTotalPoints X)) hx
  right_inv := by
    rintro ⟨d, q⟩
    cases q with
    | @mk n x =>
      have hx := congrArg (fun k : Y ⟶ Y => ((k.app d).app n) x) e.inv_hom_id
      exact congrArg (fun z => (⟨d, Functor.elementsMk (Y.obj d) n z⟩ : originalTotalPoints Y)) hx

/-- BOTH actual original endpoint point types are bounded, for an arbitrary cardinal. -/
def originalArrowPointBound (μ : Cardinal.{u}) :
    ObjectProperty (Arrow (SimplicialPresheaf.{u} D)) :=
  fun a => HasCardinalLT (originalTotalPoints a.left) μ ∧
    HasCardinalLT (originalTotalPoints a.right) μ

private theorem value_bound {X : SimplicialPresheaf.{u} D} (μ : Cardinal.{u})
    (hX : HasCardinalLT (originalTotalPoints X) μ) (d : Dᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    Cardinal.mk ((X.obj d).obj n) ≤ μ := by
  have hi : Function.Injective (fun x : (X.obj d).obj n =>
      (⟨d, Functor.elementsMk (X.obj d) n x⟩ : originalTotalPoints X)) := by
    intro x y h
    have he : Functor.elementsMk (X.obj d) n x = Functor.elementsMk (X.obj d) n y :=
      (sigma_mk_injective (β := fun d => (X.obj d).Elements)) h
    simpa only [Functor.elementsMk, Functor.Elements.mk.injEq, heq_eq_eq, true_and] using he
  exact ((hasCardinalLT_iff_cardinal_mk_lt _ μ).mp (hX.of_injective _ hi)).le

section SmallSite

variable [Small.{u} D] [LocallySmall.{u} D]

private theorem originalArrowPointBound_essentiallySmall (μ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u} (originalArrowPointBound (D := D) μ) := by
  let T := smallModelTransport (D := D)
  let L : SimplicialPresheaf.{u} (SmallModel.{u} D) ≌
      ((SmallModel.{u} D × SimplexCategory)ᵒᵖ ⥤ Type u) :=
    Functor.currying.trans (prodOpEquiv (SmallModel.{u} D)).congrLeft.symm
  let E := T.trans L
  let P := originalArrowPointBound (D := D) μ
  let P' := P.strictMap E.functor.mapArrow
  have hP' : ObjectProperty.EssentiallySmall.{u} P' :=
    ObjectProperty.essentiallySmall_presheaf_arrows_of_pointwise_bound μ P' (by
      intro a ha x
      rcases ha with ⟨a, ha⟩
      change Cardinal.mk
          ((a.left.obj ((equivSmallModel.{u} D).inverse.op.obj (op x.unop.1))).obj
            (op x.unop.2)) ≤ μ ∧
        Cardinal.mk
          ((a.right.obj ((equivSmallModel.{u} D).inverse.op.obj (op x.unop.1))).obj
            (op x.unop.2)) ≤ μ
      exact ⟨value_bound μ ha.1 _ _, value_bound μ ha.2 _ _⟩)
  let : ObjectProperty.EssentiallySmall.{u} P' := hP'
  obtain ⟨Q, hQ, hcover⟩ := ObjectProperty.EssentiallySmall.exists_small_le' P'
  let : ObjectProperty.Small.{u} Q := hQ
  obtain ⟨J, F, hF⟩ := ObjectProperty.Small.exists_eq_ofObj Q
  let K : J → Arrow (SimplicialPresheaf.{u} D) := fun j => E.inverse.mapArrow.obj (F j)
  refine ⟨⟨ObjectProperty.ofObj K, inferInstance, ?_⟩⟩
  intro a ha
  obtain ⟨b, hb, ⟨eb⟩⟩ := hcover (E.functor.mapArrow.obj a) (ObjectProperty.strictMap.mk a ha)
  rw [hF, ObjectProperty.ofObj_iff] at hb
  obtain ⟨j, rfl⟩ := hb
  exact ⟨K j, ObjectProperty.ofObj_apply K j,
    ⟨(Functor.mapArrowEquivalence E).unitIso.app a ≪≫ E.inverse.mapArrow.mapIso eb⟩⟩

/-- A small family of ORIGINAL bounded arrows covers every original bounded arrow by an Iso. -/
theorem exists_originalArrowPointBound_representatives (μ : Cardinal.{u}) :
    ∃ (J : Type u) (K : J → Arrow (SimplicialPresheaf.{u} D)),
      (∀ j, originalArrowPointBound μ (K j)) ∧
      ∀ a, originalArrowPointBound μ a → ∃ j, Nonempty (a ≅ K j) := by
  let P := originalArrowPointBound (D := D) μ
  let : ObjectProperty.EssentiallySmall.{u} P := originalArrowPointBound_essentiallySmall μ
  obtain ⟨Q, hQ, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  let : ObjectProperty.Small.{u} Q := hQ
  obtain ⟨J, K, hK⟩ := ObjectProperty.Small.exists_eq_ofObj Q
  refine ⟨J, K, ?_, ?_⟩
  · intro j
    apply hQP
    rw [hK]
    exact ObjectProperty.ofObj_apply K j
  · intro a ha
    obtain ⟨b, hb, ⟨eb⟩⟩ := hPQ a ha
    rw [hK, ObjectProperty.ofObj_iff] at hb
    obtain ⟨j, rfl⟩ := hb
    exact ⟨j, ⟨eb⟩⟩

namespace InjectiveKan

variable {I : Type i} [Small.{u} I]

/-- The SAME actual replacement has a uniform LARGER original point and rank envelope. -/
theorem exists_originalLocalCellImageEnvelope
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ lower : Cardinal.{u}) :
    ∃ (ν : Cardinal.{u}) (hν : Fact ν.IsRegular),
      letI : Fact ν.IsRegular := hν
      lower < ν ∧ μ < ν ∧ (originalLocalCellData S).κ < ν ∧
        ∀ a, originalArrowPointBound μ a →
          HasCardinalLT (originalTotalPoints ((originalLocalCellReplacement S).obj a.left)) ν ∧
          HasCardinalLT (originalTotalPoints ((originalLocalCellReplacement S).obj a.right)) ν ∧
          IsCardinalPresentable ((originalLocalCellReplacement S).obj a.left) ν ∧
          IsCardinalPresentable ((originalLocalCellReplacement S).obj a.right) ν := by
  let R := originalLocalCellReplacement S
  obtain ⟨J, K, _hK, hcover⟩ := exists_originalArrowPointBound_representatives (D := D) μ
  let H : J → Arrow (SimplicialPresheaf.{u} D) := fun j => R.mapArrow.obj (K j)
  let Fixed := Σ j, originalTotalPoints (H j).left ⊕ originalTotalPoints (H j).right
  let : Small.{u} Fixed := by infer_instance
  let budget := lower ⊔ μ ⊔ (originalLocalCellData S).κ
  obtain ⟨ν, hν, hbudget, _, _, hFixed, _, ranks⟩ :=
    exists_regular_cardinal_for_family H budget Fixed
  let : Fact ν.IsRegular := hν
  have hLower : lower < ν :=
    (show lower ≤ budget from le_sup_left.trans le_sup_left).trans_lt hbudget
  have hμ : μ < ν :=
    (show μ ≤ budget from le_sup_right.trans le_sup_left).trans_lt hbudget
  have hκ : (originalLocalCellData S).κ < ν :=
    (show (originalLocalCellData S).κ ≤ budget from le_sup_right).trans_lt hbudget
  have hPoints (j : J) : HasCardinalLT (originalTotalPoints (H j).left) ν ∧
      HasCardinalLT (originalTotalPoints (H j).right) ν := by
    exact ⟨hFixed.of_injective (fun x => (⟨j, Sum.inl x⟩ : Fixed))
        (sigma_mk_injective.comp Sum.inl_injective),
      hFixed.of_injective (fun x => (⟨j, Sum.inr x⟩ : Fixed))
        (sigma_mk_injective.comp Sum.inr_injective)⟩
  refine ⟨ν, hν, hLower, hμ, hκ, ?_⟩
  intro a ha
  obtain ⟨j, ⟨e⟩⟩ := hcover a ha
  let eL : R.obj a.left ≅ R.obj (K j).left := R.mapIso (Arrow.leftFunc.mapIso e)
  let eR : R.obj a.right ≅ R.obj (K j).right := R.mapIso (Arrow.rightFunc.mapIso e)
  let : IsCardinalPresentable (R.obj (K j).left) ν := (ranks j).1
  let : IsCardinalPresentable (R.obj (K j).right) ν := (ranks j).2
  exact ⟨(hasCardinalLT_iff_of_equiv (originalTotalPointsEquivOfIso eL) ν).mpr (hPoints j).1,
    (hasCardinalLT_iff_of_equiv (originalTotalPointsEquivOfIso eR) ν).mpr (hPoints j).2,
    isCardinalPresentable_of_iso eL.symm ν, isCardinalPresentable_of_iso eR.symm ν⟩

end InjectiveKan
end SmallSite
end SimplicialPresheaf
