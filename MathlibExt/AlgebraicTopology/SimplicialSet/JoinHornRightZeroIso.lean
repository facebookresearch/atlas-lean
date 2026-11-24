/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornRightPositiveIso

/-!
# The zero-left-dimensional right join--horn isomorphism
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

/-- The unique front-block inverse face in zero left dimension. -/
noncomputable def joinBoundaryHornRightZeroFrontFace
    (q : ℕ) (j : Fin (q + 2)) :
    (Δ[0 + (q + 1)] : SSet.{u}) ⟶
      (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).pt :=
  joinHornΔcastInv (by omega : q + 1 = 0 + (q + 1)) ≫
    joinInr (boundary 0 : SSet.{u}) (Δ[q + 1] : SSet.{u}) ≫
      (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inr

/-- The right-block face index in zero left dimension. -/
def joinBoundaryHornRightZeroBackIndex (q : ℕ)
    (t : Fin (((0 + (q + 1) + 1) + 1))) : Fin (q + 2) :=
  ⟨t.val - 1, by
    have := t.isLt
    omega⟩

lemma joinBoundaryHornRightZeroBackIndex_ne (q : ℕ) (j : Fin (q + 2))
    (t : Fin (((0 + (q + 1) + 1) + 1))) (ht : t.val ≠ 0)
    (hne : t ≠ rightJoinHornIndex 0 q j) :
    joinBoundaryHornRightZeroBackIndex q t ≠ j := by
  intro h
  apply hne
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [joinBoundaryHornRightZeroBackIndex, rightJoinHornIndex] at hh ⊢
  have htpos : 1 ≤ t.val := by omega
  omega

/-- A back-block inverse face in zero left dimension. -/
noncomputable def joinBoundaryHornRightZeroBackFace
    (q : ℕ) (j : Fin (q + 2))
    (t : Fin (((0 + (q + 1) + 1) + 1))) (ht : t.val ≠ 0)
    (hne : t ≠ rightJoinHornIndex 0 q j) :
    (Δ[0 + (q + 1)] : SSet.{u}) ⟶
      (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).pt :=
  joinHornΔcastInv (by omega : 0 + q + 1 = 0 + (q + 1)) ≫
    (joinStdSimplexIso 0 q).inv ≫
      (join.obj (Δ[0] : SSet.{u})).map
        (horn.ι j (joinBoundaryHornRightZeroBackIndex q t)
          (joinBoundaryHornRightZeroBackIndex_ne q j t ht hne)) ≫
        (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inl

/-- The complete inverse face family in zero left dimension. -/
noncomputable def joinBoundaryHornRightZeroFace
    (q : ℕ) (j : Fin (q + 2))
    (t : Fin (((0 + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex 0 q j) :
    (Δ[0 + (q + 1)] : SSet.{u}) ⟶
      (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).pt :=
  if ht : t.val = 0 then
    joinBoundaryHornRightZeroFrontFace q j
  else
    joinBoundaryHornRightZeroBackFace q j t ht hne

lemma joinBoundaryHornRightZeroFace_front
    (q : ℕ) (j : Fin (q + 2))
    (t : Fin (((0 + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex 0 q j) (ht : t.val = 0) :
    joinBoundaryHornRightZeroFace q j t hne = joinBoundaryHornRightZeroFrontFace q j :=
  dite_eq_left ht

lemma joinBoundaryHornRightZeroFace_back
    (q : ℕ) (j : Fin (q + 2))
    (t : Fin (((0 + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex 0 q j) (ht : t.val ≠ 0) :
    joinBoundaryHornRightZeroFace q j t hne = joinBoundaryHornRightZeroBackFace q j t ht hne :=
  dite_eq_right ht


lemma joinBoundaryHornRightZeroFrontFace_δ
    (q : ℕ) (j : Fin (q + 2))
    (d : Fin ((0 + (q + 1)) + 1)) (hd : d.val < q + 2) :
    stdSimplex.δ d ≫ joinBoundaryHornRightZeroFrontFace q j =
      joinHornΔcast (by omega : 0 + q = q) ≫
        stdSimplex.δ (⟨d.val, hd⟩ : Fin (q + 2)) ≫
          joinInr (boundary 0 : SSet.{u}) (Δ[q + 1] : SSet.{u}) ≫
            (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inr := by
  unfold joinBoundaryHornRightZeroFrontFace
  rw [joinHornΔcastInv_eq]
  rw [← Category.assoc,
    joinHorn_δ_joinHornΔcast
      (by omega : (0 + q) + 1 = q + 1)
      (by omega : 0 + q = q)
      d (⟨d.val, hd⟩ : Fin (q + 2)) rfl,
    Category.assoc]

lemma joinBoundaryHornRightZeroBackFace_δ
    (q : ℕ) (j : Fin (q + 2))
    (t : Fin (((0 + (q + 1) + 1) + 1))) (ht : t.val ≠ 0)
    (hne : t ≠ rightJoinHornIndex 0 q j)
    (d : Fin ((0 + (q + 1)) + 1))
    (hd : d.val < (0 + q) + 2) :
    stdSimplex.δ d ≫ joinBoundaryHornRightZeroBackFace q j t ht hne =
      stdSimplex.δ (⟨d.val, hd⟩ : Fin ((0 + q) + 2)) ≫
        (joinStdSimplexIso 0 q).inv ≫
          (join.obj (Δ[0] : SSet.{u})).map
            (horn.ι j (joinBoundaryHornRightZeroBackIndex q t)
              (joinBoundaryHornRightZeroBackIndex_ne q j t ht hne)) ≫
            (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inl := by
  unfold joinBoundaryHornRightZeroBackFace
  rw [joinHornΔcastInv_eq]
  rw [← Category.assoc,
    joinHorn_δ_joinHornΔcast
      (rfl : (0 + q) + 1 = (0 + q) + 1)
      (rfl : 0 + q = 0 + q)
      d (⟨d.val, hd⟩ : Fin ((0 + q) + 2)) rfl,
    joinHornΔcast_rfl, Category.id_comp]

lemma joinBoundaryHornRightZeroFace_compatible
    (q : ℕ) (j : Fin (q + 2)) :
    horn.IsCompatible (joinBoundaryHornRightZeroFace.{u} q j) := by
  rw [horn.isCompatible_iff]
  intro s t hs ht hst
  by_cases hsf : s.val = 0
  · have htf : t.val ≠ 0 := by omega
    rw [joinBoundaryHornRightZeroFace_front q j s hs hsf,
      joinBoundaryHornRightZeroFace_back q j t ht htf]
    set tr := joinBoundaryHornRightZeroBackIndex q t
    have htr : tr ≠ j := joinBoundaryHornRightZeroBackIndex_ne q j t htf ht
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < q + 2 := by
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      have htt : t.val < q + 3 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < (0 + q) + 2 := by
      have hcast : (s.castPred (Fin.ne_last_of_lt hst)).val = s.val := rfl
      omega
    rw [joinBoundaryHornRightZeroFrontFace_δ q j
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinBoundaryHornRightZeroBackFace_δ q j t htf ht
          (s.castPred (Fin.ne_last_of_lt hst)) hdR]
    have hidx : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ : Fin (q + 2)) = tr := by
      apply Fin.ext
      change (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1
      rfl
    have hzero : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
        Fin ((0 + q) + 2)).val = 0 := by
      change (s.castPred (Fin.ne_last_of_lt hst)).val = 0
      have hcast : (s.castPred (Fin.ne_last_of_lt hst)).val = s.val := rfl
      omega
    rw [hidx, joinHorn_frontPush_zero_assoc _ hzero]
    rw [cancel_epi]
    simp only [← Category.assoc]
    rw [map_comp_joinInr]
    rw [← horn.ι_ι j tr htr, Functor.map_comp]
    simp only [Category.assoc]
    rw [← (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).isPushout.w]
    rw [(join.map (boundary 0).ι).naturality_assoc]
    simp only [← Category.assoc]
    rw [joinInr_comp_map]
  · have htf : t.val ≠ 0 := by omega
    rw [joinBoundaryHornRightZeroFace_back q j s hs hsf,
      joinBoundaryHornRightZeroFace_back q j t ht htf]
    have hslo : 1 ≤ s.val := by omega
    have htlo : 1 ≤ t.val := by omega
    set sr := joinBoundaryHornRightZeroBackIndex q s
    set tr := joinBoundaryHornRightZeroBackIndex q t
    have hsr : sr ≠ j := joinBoundaryHornRightZeroBackIndex_ne q j s hsf hs
    have htr : tr ≠ j := joinBoundaryHornRightZeroBackIndex_ne q j t htf ht
    have hstr : sr < tr := by
      rw [Fin.lt_def]
      dsimp [sr, tr, joinBoundaryHornRightZeroBackIndex]
      omega
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < (0 + q) + 2 := by
      have htbound : t.val < q + 3 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < (0 + q) + 2 := by
      have hsbound : s.val < q + 3 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using s.isLt
      have htbound : t.val < q + 3 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hstval : s.val < t.val := hst
      simp only [Fin.coe_castPred]
      rw [show (0 + q) + 2 = q + 2 by omega]
      omega
    rw [joinBoundaryHornRightZeroBackFace_δ q j s hsf hs
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinBoundaryHornRightZeroBackFace_δ q j t htf ht
          (s.castPred (Fin.ne_last_of_lt hst)) hdR]
    obtain _ | q := q
    · have hsrval : sr.val ≠ j.val := fun h => hsr (Fin.ext h)
      have htrval : tr.val ≠ j.val := fun h => htr (Fin.ext h)
      have hstrval : sr.val < tr.val := hstr
      have hsrlt := sr.isLt
      have htrlt := tr.isLt
      have hjlt := j.isLt
      omega
    · have haL : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
          Fin ((0 + (q + 1)) + 2)).val =
          1 + (tr.pred (Fin.ne_zero_of_lt hstr)).val := by
        change (t.pred (Fin.ne_zero_of_lt hst)).val =
          1 + (tr.pred (Fin.ne_zero_of_lt hstr)).val
        have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
        have hpred : (tr.pred (Fin.ne_zero_of_lt hstr)).val = tr.val - 1 := rfl
        have htrval : tr.val = t.val - 1 := rfl
        have htrpos : 0 < tr.val := by omega
        omega
      have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin ((0 + (q + 1)) + 2)).val =
          1 + (sr.castPred (Fin.ne_last_of_lt hstr)).val := by
        change (s.castPred (Fin.ne_last_of_lt hst)).val =
          1 + (sr.castPred (Fin.ne_last_of_lt hstr)).val
        have hsrval : sr.val = s.val - 1 := rfl
        have hcastS : (s.castPred (Fin.ne_last_of_lt hst)).val = s.val := rfl
        have hcastR : (sr.castPred (Fin.ne_last_of_lt hstr)).val = sr.val := rfl
        omega
      rw [show (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
            Fin (0 + (q + 1) + 2)) =
          (⟨1 + (tr.pred (Fin.ne_zero_of_lt hstr)).val,
            by have := (tr.pred (Fin.ne_zero_of_lt hstr)).isLt; omega⟩ :
              Fin (0 + q + 3)) by apply Fin.ext; exact haL]
      rw [show (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
            Fin (0 + (q + 1) + 2)) =
          (⟨1 + (sr.castPred (Fin.ne_last_of_lt hstr)).val,
            by have := (sr.castPred (Fin.ne_last_of_lt hstr)).isLt; omega⟩ :
              Fin (0 + q + 3)) by apply Fin.ext; exact haR]
      rw [joinHorn_backPush_assoc, joinHorn_backPush_assoc]
      rw [cancel_epi]
      simp only [← Category.assoc, ← Functor.map_comp]
      have hc := (horn.IsCompatible.of_hom
        (𝟙 (horn (q + 2) j : SSet.{u}))).δ_pred_comp
          sr tr (hj := hsr) (hk := htr) (hjk := hstr)
      simp only [Category.comp_id] at hc
      have hm := congrArg (join.obj (Δ[0] : SSet.{u})).map hc
      exact congrArg (fun z => z ≫
        (joinBoundaryHornRightPushoutObjObj.{u} 0 (q + 1) j).inl) hm


/-- The inverse map obtained from the zero-dimensional face family. -/
noncomputable def joinBoundaryHornRightZeroFromHorn
    (q : ℕ) (j : Fin (q + 2)) :
    (horn (0 + (q + 1) + 1) (rightJoinHornIndex 0 q j) : SSet.{u}) ⟶
      (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).pt :=
  (joinBoundaryHornRightZeroFace_compatible q j).desc

@[reassoc]
lemma joinBoundaryHornRightZeroHornFace_fromHorn
    (q : ℕ) (j : Fin (q + 2))
    (t : Fin (((0 + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex 0 q j) :
    horn.ι (rightJoinHornIndex 0 q j) t hne ≫
        joinBoundaryHornRightZeroFromHorn q j =
      joinBoundaryHornRightZeroFace q j t hne :=
  horn.IsCompatible.ι_desc (joinBoundaryHornRightZeroFace_compatible q j) t hne


@[reassoc]
lemma joinBoundaryHornRightZeroFace_toHorn
    (q : ℕ) (j : Fin (q + 2))
    (t : Fin (((0 + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex 0 q j) :
    joinBoundaryHornRightZeroFace q j t hne ≫
        joinBoundaryHornRightToHorn 0 q j =
      horn.ι (rightJoinHornIndex 0 q j) t hne := by
  rw [← cancel_mono
    (horn (0 + (q + 1) + 1) (rightJoinHornIndex 0 q j)).ι]
  simp only [Category.assoc, joinBoundaryHornRightToHorn_ι,
    horn.ι_ι]
  by_cases htf : t.val = 0
  · rw [joinBoundaryHornRightZeroFace_front q j t hne htf]
    unfold joinBoundaryHornRightZeroFrontFace
    simp only [Category.assoc]
    rw [(joinBoundaryHornRightPushoutObjObj 0 q j).inr_ι_assoc]
    slice_lhs 2 3 => rw [joinInr_comp_map]
    rw [joinHorn_joinInr_zero]
    rw [joinHornΔcastInv_eq]
    slice_lhs 1 2 => rw [joinHornΔcast_comp_eq_id]
    rw [Category.id_comp]
    congr 1
    apply Fin.ext
    exact htf.symm
  · rw [joinBoundaryHornRightZeroFace_back q j t hne htf]
    unfold joinBoundaryHornRightZeroBackFace
    simp only [Category.assoc]
    rw [(joinBoundaryHornRightPushoutObjObj 0 q j).inl_ι_assoc]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [horn.ι_ι]
    simp only [Category.assoc]
    rw [← joinHorn_backPush_assoc]
    simp only [Iso.inv_hom_id, Category.comp_id]
    rw [joinHornΔcastInv_eq]
    let a : Fin (0 + q + 3) :=
      ⟨0 + 1 + (joinBoundaryHornRightZeroBackIndex q t).val,
        by have := (joinBoundaryHornRightZeroBackIndex q t).isLt; omega⟩
    have ha : a.val = t.val := by
      dsimp [a, joinBoundaryHornRightZeroBackIndex]
      have htpos : 1 ≤ t.val := by omega
      omega
    rw [← joinHorn_δ_joinHornΔcast
      (A := 0 + (q + 1)) (B := 0 + q + 1)
      (by omega : (0 + (q + 1)) + 1 = (0 + q + 1) + 1)
      (by omega : 0 + (q + 1) = 0 + q + 1)
      t a ha.symm]
    rw [joinHornΔcast_eq _ rfl, joinHornΔcast_rfl, Category.comp_id]


lemma joinBoundaryHornRightZeroFromHorn_toHorn
    (q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightZeroFromHorn q j ≫ joinBoundaryHornRightToHorn 0 q j =
      𝟙 (horn (0 + (q + 1) + 1)
        (rightJoinHornIndex 0 q j) : SSet.{u}) := by
  apply horn.hom_ext'
  intro t hne
  rw [joinBoundaryHornRightZeroHornFace_fromHorn_assoc,
    joinBoundaryHornRightZeroFace_toHorn, Category.comp_id]

private instance joinBoundaryHornRightZeroJoinInr_epi (q : ℕ) :
    Epi (joinInr (boundary 0 : SSet.{u}) (Δ[q + 1] : SSet.{u})) := by
  rw [← epi_comp_iff_of_isIso _
    ((join.map joinHornBoundaryZeroIso.hom).app (Δ[q + 1] : SSet.{u}))]
  rw [joinInr_comp_map, joinInr_bot]
  infer_instance

private instance joinBoundaryHornRightZeroFrontSource_epi (q : ℕ) :
    Epi (joinHornΔcastInv (by omega : q + 1 = 0 + (q + 1)) ≫
      joinInr (boundary 0 : SSet.{u}) (Δ[q + 1] : SSet.{u})) := by
  rw [joinHornΔcastInv_eq]
  apply epi_comp

lemma joinBoundaryHornRightZeroBackFace_after_iso
    (q : ℕ) (j r : Fin (q + 2)) (hr : r ≠ j) :
    (joinStdSimplexIso 0 q).hom ≫
        joinBoundaryHornRightZeroFace q j (rightJoinHornIndex 0 q r)
          (rightJoinHornIndex_ne 0 q j r hr) =
      (join.obj (Δ[0] : SSet.{u})).map (horn.ι j r hr) ≫
        (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inl := by
  have ht : (rightJoinHornIndex 0 q r).val ≠ 0 := by
    dsimp [rightJoinHornIndex]
    omega
  rw [joinBoundaryHornRightZeroFace_back q j (rightJoinHornIndex 0 q r)
    (rightJoinHornIndex_ne 0 q j r hr) ht]
  unfold joinBoundaryHornRightZeroBackFace
  rw [joinHornΔcastInv_eq, joinHornΔcast_eq _ rfl, joinHornΔcast_rfl]
  simp only [Category.id_comp, Iso.hom_inv_id_assoc]
  congr 3
  apply Fin.ext
  dsimp [joinBoundaryHornRightZeroBackIndex, rightJoinHornIndex]
  omega


lemma joinBoundaryHornRightZeroToHorn_fromHorn
    (q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightToHorn 0 q j ≫ joinBoundaryHornRightZeroFromHorn q j =
      𝟙 (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).pt := by
  apply (joinBoundaryHornRightPushoutObjObj 0 q j).hom_ext
  · simp only [Category.comp_id]
    apply joinBoundaryHornRight_hom_ext 0 q j
    intro r hr
    slice_lhs 2 3 => rw [joinBoundaryHornRightPushout_inl_toHorn]
    slice_lhs 1 2 => rw [joinBoundaryHornRightFactorMap_face]
    slice_lhs 2 3 => rw [joinBoundaryHornRightZeroHornFace_fromHorn]
    rw [joinBoundaryHornRightZeroBackFace_after_iso]
  · simp only [Category.comp_id]
    let src : (Δ[0 + (q + 1)] : SSet.{u}) ⟶
        (join.flip.obj (Δ[q + 1] : SSet.{u})).obj (boundary 0 : SSet.{u}) :=
      joinHornΔcastInv (by omega : q + 1 = 0 + (q + 1)) ≫
        joinInr (boundary 0 : SSet.{u}) (Δ[q + 1] : SSet.{u})
    let _ : Epi src := joinBoundaryHornRightZeroFrontSource_epi q
    rw [← cancel_epi src]
    let z : Fin ((0 + (q + 1) + 1) + 1) := 0
    have hz : z ≠ rightJoinHornIndex 0 q j := by
      exact rightJoinZeroFaceIndex_ne q j
    have hface : joinBoundaryHornRightZeroFace q j z hz =
        src ≫ (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inr := by
      rw [joinBoundaryHornRightZeroFace_front q j z hz (by rfl)]
      rfl
    dsimp only [src] at hface
    have hface' : joinBoundaryHornRightZeroFace q j z hz =
        joinHornΔcastInv (by omega : q + 1 = 0 + (q + 1)) ≫
          joinInr (boundary 0 : SSet.{u}) (Δ[q + 1] : SSet.{u}) ≫
            (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inr := by
      simpa only [Category.assoc] using hface
    slice_lhs 1 3 => rw [← hface']
    slice_lhs 1 2 => rw [joinBoundaryHornRightZeroFace_toHorn]
    rw [joinBoundaryHornRightZeroHornFace_fromHorn, hface']
    dsimp only [src]
    simp only [Category.assoc]


/-- The right boundary--horn point isomorphism in zero left dimension. -/
noncomputable def joinBoundaryHornRightPointIsoZero
    (q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).pt ≅
      (horn (0 + (q + 1) + 1) (rightJoinHornIndex 0 q j) : SSet.{u}) where
  hom := joinBoundaryHornRightToHorn 0 q j
  inv := joinBoundaryHornRightZeroFromHorn q j
  hom_inv_id := joinBoundaryHornRightZeroToHorn_fromHorn q j
  inv_hom_id := joinBoundaryHornRightZeroFromHorn_toHorn q j

@[simp]
lemma joinBoundaryHornRightPointIsoZero_hom
    (q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPointIsoZero.{u} q j).hom =
      joinBoundaryHornRightToHorn 0 q j :=
  rfl

@[reassoc]
lemma joinBoundaryHornRightPointIsoZero_hom_ι
    (q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPointIsoZero.{u} q j).hom ≫
        (horn (0 + (q + 1) + 1) (rightJoinHornIndex 0 q j)).ι =
      (joinBoundaryHornRightPushoutObjObj 0 q j).ι ≫
        (joinStdSimplexIso 0 (q + 1)).hom :=
  joinBoundaryHornRightToHorn_ι 0 q j

@[reassoc]
lemma joinBoundaryHornRightPointIsoZero_hom_inl
    (q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inl ≫
        (joinBoundaryHornRightPointIsoZero q j).hom =
      joinBoundaryHornRightFactorMap 0 q j :=
  joinBoundaryHornRightPushout_inl_toHorn 0 q j

@[reassoc]
lemma joinBoundaryHornRightPointIsoZero_hom_inr
    (q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} 0 q j).inr ≫
        (joinBoundaryHornRightPointIsoZero q j).hom =
      joinBoundaryHornRightBoundaryFactorMap 0 q j :=
  joinBoundaryHornRightPushout_inr_toHorn 0 q j

end JoinHorn.Internal
end SSet
