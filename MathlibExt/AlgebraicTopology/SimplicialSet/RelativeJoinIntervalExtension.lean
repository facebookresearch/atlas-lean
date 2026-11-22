/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SliceRestrictionPullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLiftingComponents
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftFibrationEquivalence

/-!
# Relative extension over a join interval

This file proves the under-slice/left-fibration dual of Joyal's Lemma 4.12.
An equivalence on the canonical interval inside a relative target-endpoint
pushout join extends across the full join, while retaining the complete
prescribed map in the base.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

/-- Target-prescribed equivalence lifting, expressed as a lift of the target
endpoint square. -/
theorem nonempty_liftStruct_targetEndpoint_of_isEquivalence
    {C D : SSet.{u}} (F : C ⟶ D) [LeftFibration F] [Quasicategory D]
    (sq : Arrow.mk (stdSimplex.δ (0 : Fin 2)) ⟶ Arrow.mk F)
    (h : (Edge.mk' (yonedaEquiv sq.right)).IsEquivalence) :
    Nonempty (Arrow.LiftStruct sq) := by
  let e : Edge
      (D.δ 1 (yonedaEquiv sq.right))
      (D.δ 0 (yonedaEquiv sq.right)) :=
    Edge.mk' (yonedaEquiv sq.right)
  have hw : sq.left ≫ F =
      stdSimplex.δ (0 : Fin 2) ≫ sq.right := sq.w
  have htgt : F.app _ (yonedaEquiv sq.left) =
      D.δ 0 (yonedaEquiv sq.right) := by
    calc
      F.app _ (yonedaEquiv sq.left) =
          yonedaEquiv (sq.left ≫ F) := by rw [yonedaEquiv_comp]
      _ = yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ sq.right) := by
        rw [hw]
      _ = D.δ 0 (yonedaEquiv sq.right) := by
        exact stdSimplex.yonedaEquiv_δ_comp sq.right 0
  obtain ⟨y₀, hy₀, e', he', heq⟩ :=
    LeftFibration.exists_isoLift_target (F := F) (u := e) h htgt
  refine ⟨CommSq.LiftStruct.mk (yonedaEquiv.symm e'.edge) ?_ ?_⟩
  · apply yonedaEquiv.injective
    change yonedaEquiv
        (stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e'.edge) =
      yonedaEquiv sq.left
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply,
      e'.tgt_eq]
  · apply yonedaEquiv.injective
    change yonedaEquiv (yonedaEquiv.symm e'.edge ≫ F) =
      yonedaEquiv sq.right
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact heq

/-- The structured target-endpoint relative join square has a filler when its
canonical interval edge is an equivalence. -/
theorem nonempty_liftStruct_joinUnder_targetEndpoint_of_isEquivalence
    {K₀ K X Y : SSet.{u}} (i : K₀ ⟶ K) [Mono i]
    (f : K ⟶ X) (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    (sq : Arrow.mk
        (joinUnderPushoutMap i (stdSimplex.δ (0 : Fin 2))) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)))
    (h : (Edge.mk' (yonedaEquiv
      (joinInr K₀ (Δ[1] : SSet.{u}) ≫
        (joinUnderPushoutObjObj i
          (stdSimplex.δ (0 : Fin 2))).inr ≫ sq.left.right))).IsEquivalence) :
    Nonempty (Arrow.LiftStruct sq) := by
  let sq' := sliceUnder.restrictionArrowHomEquiv i
    (stdSimplex.δ (0 : Fin 2)) f p sq
  let P := pullback (sliceUnder.map X (i ≫ f) p)
    (sliceUnder.restrict Y (f ≫ p) i)
  let Fproj : P ⟶ X :=
    pullback.fst (sliceUnder.map X (i ≫ f) p)
      (sliceUnder.restrict Y (f ≫ p) i) ≫
        sliceUnder.proj X (i ≫ f)
  let _ : Quasicategory X := quasicategory_of_innerFibration p
  let _ : LeftFibration
      (pullback.fst (sliceUnder.map X (i ≫ f) p)
        (sliceUnder.restrict Y (f ≫ p) i)) :=
    leftFibration_sliceUnder_restriction_pullback_fst p i f
  let _ : LeftFibration (sliceUnder.proj X (i ≫ f)) :=
    leftFibration_sliceUnder_proj X (i ≫ f)
  let _ : LeftFibration Fproj :=
    ⟨leftFibrations.comp_mem _ _ LeftFibration.mem LeftFibration.mem⟩
  let _ : Quasicategory P :=
    quasicategory_sliceUnder_restriction_pullback p i f
  let _ : LeftFibration (sliceUnder.restrictionComparison i f p) :=
    leftFibration_sliceUnder_restrictionComparison i f p
  let e := Edge.mk' (yonedaEquiv sq'.right)
  have heq : (e.map Fproj).edge =
      (Edge.mk' (yonedaEquiv
        (joinInr K₀ (Δ[1] : SSet.{u}) ≫
          (joinUnderPushoutObjObj i
            (stdSimplex.δ (0 : Fin 2))).inr ≫ sq.left.right))).edge := by
    dsimp only [e]
    simp only [Edge.map_edge, Edge.mk'_edge]
    dsimp only [Fproj]
    rw [← yonedaEquiv_comp]
    exact congrArg yonedaEquiv
      (sliceUnder.restrictionArrowHomEquiv_right_fst_proj i
        (stdSimplex.δ (0 : Fin 2)) f p sq)
  have hemap : (e.map Fproj).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq heq).2 h
  have he : e.IsEquivalence := LeftFibration.isEquivalence_of_map hemap
  have hlift : Nonempty (Arrow.LiftStruct sq') :=
    nonempty_liftStruct_targetEndpoint_of_isEquivalence
      (sliceUnder.restrictionComparison i f p) sq' he
  exact hlift.map (sliceUnder.restrictionLiftStructEquiv sq).symm

/-- Map-and-equations form of the structured relative join interval
extension. -/
theorem exists_joinUnder_targetEndpoint_extension_of_isEquivalence
    {K₀ K X Y : SSet.{u}} (i : K₀ ⟶ K) [Mono i]
    (f : K ⟶ X) (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    (sq : Arrow.mk
        (joinUnderPushoutMap i (stdSimplex.δ (0 : Fin 2))) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)))
    (h : (Edge.mk' (yonedaEquiv
      (joinInr K₀ (Δ[1] : SSet.{u}) ≫
        (joinUnderPushoutObjObj i
          (stdSimplex.δ (0 : Fin 2))).inr ≫ sq.left.right))).IsEquivalence) :
    ∃ l : K ⋆ (Δ[1] : SSet.{u}) ⟶ X,
      (joinUnderPushoutObjObj i
          (stdSimplex.δ (0 : Fin 2))).ι ≫ l = sq.left.right ∧
        l ≫ p = sq.right.right := by
  obtain ⟨L⟩ :=
    nonempty_liftStruct_joinUnder_targetEndpoint_of_isEquivalence
      i f p sq h
  refine ⟨L.l.right, ?_, ?_⟩
  · exact congrArg Under.Hom.right L.fac_left
  · exact congrArg Under.Hom.right L.fac_right

/-- Source-level target-endpoint relative join interval extension.  An
equivalence on the canonical interval extends while retaining the entire
prescribed map `K ⋆ Δ[1] ⟶ Y`. -/
theorem exists_fill_relativeJoinInterval_target_of_isEquivalence
    {K₀ K X Y : SSet.{u}} (i : K₀ ⟶ K) [Mono i]
    (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    (u : (joinUnderPushoutObjObj i
      (stdSimplex.δ (0 : Fin 2))).pt ⟶ X)
    (v : K ⋆ (Δ[1] : SSet.{u}) ⟶ Y)
    (hsq : u ≫ p =
      (joinUnderPushoutObjObj i
        (stdSimplex.δ (0 : Fin 2))).ι ≫ v)
    (h : (Edge.mk' (yonedaEquiv
      (joinInr K₀ (Δ[1] : SSet.{u}) ≫
        (joinUnderPushoutObjObj i
          (stdSimplex.δ (0 : Fin 2))).inr ≫ u))).IsEquivalence) :
    ∃ l : K ⋆ (Δ[1] : SSet.{u}) ⟶ X,
      (joinUnderPushoutObjObj i
          (stdSimplex.δ (0 : Fin 2))).ι ≫ l = u ∧
        l ≫ p = v := by
  let f : K ⟶ X :=
    joinInl K (Δ[0] : SSet.{u}) ≫
      (joinUnderPushoutObjObj i
        (stdSimplex.δ (0 : Fin 2))).inl ≫ u
  let top : joinUnderPushoutSource i (stdSimplex.δ (0 : Fin 2)) ⟶
      Under.mk f := Under.homMk u rfl
  have hv : joinInl K (Δ[1] : SSet.{u}) ≫ v = f ≫ p := by
    calc
      joinInl K (Δ[1] : SSet.{u}) ≫ v =
          (joinInl K (Δ[0] : SSet.{u}) ≫
            (join.obj K).map (stdSimplex.δ (0 : Fin 2))) ≫ v := by
              rw [joinInl_comp_map]
      _ = (joinInl K (Δ[0] : SSet.{u}) ≫
            (joinUnderPushoutObjObj i
              (stdSimplex.δ (0 : Fin 2))).inl) ≫
            ((joinUnderPushoutObjObj i
              (stdSimplex.δ (0 : Fin 2))).ι ≫ v) := by
              simpa only [Category.assoc] using congrArg
                (fun z => joinInl K (Δ[0] : SSet.{u}) ≫ z ≫ v)
                (joinUnderPushoutObjObj i
                  (stdSimplex.δ (0 : Fin 2))).inl_ι.symm
      _ = f ≫ p := by rw [← hsq]; rfl
  let bottom : (joinUnder K).obj (Δ[1] : SSet.{u}) ⟶
      Under.mk (f ≫ p) := Under.homMk v hv
  let sq : Arrow.mk
        (joinUnderPushoutMap i (stdSimplex.δ (0 : Fin 2))) ⟶
      Arrow.mk (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)) :=
    { left := top
      right := bottom
      w := by
        apply StructuredArrow.hom_ext
        exact hsq }
  have sq_left_right : sq.left.right = u := rfl
  have sq_right_right : sq.right.right = v := rfl
  have hsqEquiv :
      (Edge.mk' (yonedaEquiv
        (joinInr K₀ (Δ[1] : SSet.{u}) ≫
          (joinUnderPushoutObjObj i
            (stdSimplex.δ (0 : Fin 2))).inr ≫ sq.left.right))).IsEquivalence := by
    change (Edge.mk' (yonedaEquiv
      (joinInr K₀ (Δ[1] : SSet.{u}) ≫
        (joinUnderPushoutObjObj i
          (stdSimplex.δ (0 : Fin 2))).inr ≫ u))).IsEquivalence
    exact h
  obtain ⟨l, hl, hp⟩ :=
    exists_joinUnder_targetEndpoint_extension_of_isEquivalence
      i f p sq hsqEquiv
  exact ⟨l, by simpa only [sq_left_right] using hl,
    by simpa only [sq_right_right] using hp⟩

end SSet
