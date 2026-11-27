/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornRightComparison

/-!
# Faces of the right boundary--horn pushout

Canonical lifts of every face of the shifted horn into the pushout.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

/-!
## The inverse face family in positive left dimension
-/

set_option maxHeartbeats 1000000 in
/-- A front-block inverse face for the positive left-dimensional right decomposition. -/
noncomputable def joinBoundaryHornRightFrontFaceSucc
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1))) (ht : t.val ≤ p + 1) :
    (Δ[(p + 1) + (q + 1)] : SSet.{u}) ⟶
      (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).pt :=
  joinHornΔcastInv (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1)) ≫
    (joinStdSimplexIso p (q + 1)).inv ≫
      (join.map (boundary.ι (⟨t.val, by omega⟩ : Fin (p + 2)))).app
        (Δ[q + 1] : SSet.{u}) ≫
        (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).inr

lemma joinBackIndexSucc_ne
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : ¬ t.val ≤ p + 1)
    (hne : t ≠ rightJoinHornIndex (p + 1) q j) :
    joinBackIndexSucc p q t ht ≠ j := by
  intro h
  apply hne
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [joinBackIndexSucc, rightJoinHornIndex] at this ⊢
  have hle : p + 2 ≤ t.val := by omega
  omega

/-- A back-block inverse face for the positive left-dimensional right decomposition. -/
noncomputable def joinBoundaryHornRightBackFaceSucc
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : ¬ t.val ≤ p + 1)
    (hne : t ≠ rightJoinHornIndex (p + 1) q j) :
    (Δ[(p + 1) + (q + 1)] : SSet.{u}) ⟶
      (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).pt :=
  joinHornΔcastInv (by omega : (p + 1) + q + 1 = (p + 1) + (q + 1)) ≫
    (joinStdSimplexIso (p + 1) q).inv ≫
      (join.obj (Δ[p + 1] : SSet.{u})).map
        (horn.ι j (joinBackIndexSucc p q t ht)
          (joinBackIndexSucc_ne p q j t ht hne)) ≫
        (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).inl

/-- The inverse face family, selected by its join block. -/
noncomputable def joinBoundaryHornRightFaceSucc
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex (p + 1) q j) :
    (Δ[(p + 1) + (q + 1)] : SSet.{u}) ⟶
      (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).pt :=
  if ht : t.val ≤ p + 1 then
    joinBoundaryHornRightFrontFaceSucc p q j t ht
  else
    joinBoundaryHornRightBackFaceSucc p q j t ht hne

lemma joinBoundaryHornRightFaceSucc_front
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex (p + 1) q j) (ht : t.val ≤ p + 1) :
    joinBoundaryHornRightFaceSucc p q j t hne =
      joinBoundaryHornRightFrontFaceSucc p q j t ht :=
  dite_eq_left ht

lemma joinBoundaryHornRightFaceSucc_back
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex (p + 1) q j) (ht : ¬ t.val ≤ p + 1) :
    joinBoundaryHornRightFaceSucc p q j t hne =
      joinBoundaryHornRightBackFaceSucc p q j t ht hne :=
  dite_eq_right ht

lemma joinBoundaryHornRightFrontFaceSucc_δ
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1))) (ht : t.val ≤ p + 1)
    (d : Fin (((p + 1) + (q + 1)) + 1))
    (hd : d.val < p + (q + 1) + 2) :
    stdSimplex.δ d ≫ joinBoundaryHornRightFrontFaceSucc p q j t ht =
      joinHornΔcast (by omega : (p + 1) + q = p + (q + 1)) ≫
        stdSimplex.δ
          (⟨d.val, hd⟩ : Fin (p + (q + 1) + 2)) ≫
          (joinStdSimplexIso p (q + 1)).inv ≫
            (join.map (boundary.ι (⟨t.val, by omega⟩ : Fin (p + 2)))).app
              (Δ[q + 1] : SSet.{u}) ≫
              (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).inr := by
  unfold joinBoundaryHornRightFrontFaceSucc
  rw [joinHornΔcastInv_eq]
  rw [← Category.assoc,
    joinHorn_δ_joinHornΔcast
      (by omega : ((p + 1) + q) + 1 = (p + (q + 1)) + 1)
      (by omega : (p + 1) + q = p + (q + 1))
      d (⟨d.val, hd⟩ : Fin (p + (q + 1) + 2)) rfl,
    Category.assoc]

lemma joinBoundaryHornRightBackFaceSucc_δ
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : ¬ t.val ≤ p + 1)
    (hne : t ≠ rightJoinHornIndex (p + 1) q j)
    (d : Fin (((p + 1) + (q + 1)) + 1))
    (hd : d.val < ((p + 1) + q) + 2) :
    stdSimplex.δ d ≫ joinBoundaryHornRightBackFaceSucc p q j t ht hne =
      stdSimplex.δ (⟨d.val, hd⟩ : Fin (((p + 1) + q) + 2)) ≫
        (joinStdSimplexIso (p + 1) q).inv ≫
          (join.obj (Δ[p + 1] : SSet.{u})).map
            (horn.ι j (joinBackIndexSucc p q t ht)
              (joinBackIndexSucc_ne p q j t ht hne)) ≫
            (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).inl := by
  unfold joinBoundaryHornRightBackFaceSucc
  rw [joinHornΔcastInv_eq]
  rw [← Category.assoc,
    joinHorn_δ_joinHornΔcast
      (by omega : (((p + 1) + q) + 1) = ((p + 1) + q) + 1)
      (rfl : (p + 1) + q = (p + 1) + q)
      d (⟨d.val, hd⟩ : Fin (((p + 1) + q) + 2)) rfl,
    joinHornΔcast_rfl, Category.id_comp]

lemma joinBoundaryHornRightFaceSucc_compatible
    (p q : ℕ) (j : Fin (q + 2)) :
    horn.IsCompatible (joinBoundaryHornRightFaceSucc.{u} p q j) := by
  rw [horn.isCompatible_iff]
  intro s t hs ht hst
  by_cases hsf : s.val ≤ p + 1 <;> by_cases htf : t.val ≤ p + 1
  · rw [joinBoundaryHornRightFaceSucc_front p q j s hs hsf,
      joinBoundaryHornRightFaceSucc_front p q j t ht htf]
    set sr : Fin (p + 2) := ⟨s.val, by omega⟩
    set tr : Fin (p + 2) := ⟨t.val, by omega⟩
    have hstr : sr < tr := by
      rw [Fin.lt_def]
      dsimp [sr, tr]
      exact hst
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < p + (q + 1) + 2 := by
      have := t.isLt
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < p + (q + 1) + 2 := by
      have := s.isLt
      simp only [Fin.coe_castPred] at this ⊢
      omega
    rw [joinBoundaryHornRightFrontFaceSucc_δ p q j s hsf
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinBoundaryHornRightFrontFaceSucc_δ p q j t htf
          (s.castPred (Fin.ne_last_of_lt hst)) hdR]
    rw [cancel_epi]
    obtain _ | p := p
    · have hs0 : s.val = 0 := by omega
      have ht1 : t.val = 1 := by omega
      have haL : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
          Fin (0 + (q + 1) + 2)).val = 0 := by
        change (t.pred (Fin.ne_zero_of_lt hst)).val = 0
        have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
        omega
      have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin (0 + (q + 1) + 2)).val = 0 := by
        simp only [Fin.coe_castPred]
        omega
      rw [joinHorn_frontPush_zero_assoc _ haL, joinHorn_frontPush_zero_assoc _ haR]
      rw [cancel_epi]
      simp only [← Category.assoc]
      rw [joinInr_comp_map, joinInr_comp_map]
    · have haL : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
          Fin ((p + 1) + (q + 1) + 2)).val =
          (tr.pred (Fin.ne_zero_of_lt hstr)).val := by
        dsimp [tr]
      have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin ((p + 1) + (q + 1) + 2)).val =
          (sr.castPred (Fin.ne_last_of_lt hstr)).val := by
        dsimp [sr]
      rw [joinHorn_frontPush_assoc _ _ haL, joinHorn_frontPush_assoc _ _ haR]
      rw [cancel_epi, cancel_epi]
      simp only [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp]
      rw [boundary.ι_isCompatible (p + 1) sr tr hstr]
  · rw [joinBoundaryHornRightFaceSucc_front p q j s hs hsf,
      joinBoundaryHornRightFaceSucc_back p q j t ht htf]
    set sr : Fin (p + 2) := ⟨s.val, by omega⟩
    set tr := joinBackIndexSucc p q t htf
    have htr : tr ≠ j := joinBackIndexSucc_ne p q j t htf ht
    have htlo : p + 2 ≤ t.val := by omega
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < p + (q + 1) + 2 := by
      have htbound : t.val < p + q + 4 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < ((p + 1) + q) + 2 := by
      have hsbound : s.val < p + 2 := by omega
      simp only [Fin.coe_castPred]
      omega
    rw [joinBoundaryHornRightFrontFaceSucc_δ p q j s hsf
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinBoundaryHornRightBackFaceSucc_δ p q j t htf ht
          (s.castPred (Fin.ne_last_of_lt hst)) hdR]
    have haL : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
        Fin (p + (q + 1) + 2)).val = p + 1 + tr.val := by
      change (t.pred (Fin.ne_zero_of_lt hst)).val = p + 1 + tr.val
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      have htrval : tr.val = t.val - (p + 2) := rfl
      have hdecomp : p + 2 + tr.val = t.val := by
        rw [htrval]
        exact Nat.add_sub_of_le htlo
      omega
    have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
        Fin (((p + 1) + q) + 2)).val = sr.val := by
      dsimp [sr]
    rw [show (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
          Fin (p + (q + 1) + 2)) =
        (⟨p + 1 + tr.val, by have := tr.isLt; omega⟩ :
          Fin (p + q + 3)) by apply Fin.ext; exact haL]
    rw [joinHorn_backPush_assoc]
    rw [show (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin ((p + 1) + q + 2)) =
        (⟨sr.val, by have := sr.isLt; omega⟩ :
          Fin ((p + 1) + q + 2)) by apply Fin.ext; exact haR]
    rw [joinHorn_frontPush_assoc sr _ rfl]
    rw [cancel_epi, cancel_epi]
    have hsface : boundary.ι (⟨s.val, by omega⟩ : Fin (p + 2)) =
        boundary.ι sr := by rfl
    have htface : horn.ι j (joinBackIndexSucc p q t htf)
          (joinBackIndexSucc_ne p q j t htf ht) =
        horn.ι j tr htr := by rfl
    rw [hsface, htface]
    simp only [← Category.assoc]
    rw [(join.map (boundary.ι sr)).naturality]
    rw [← horn.ι_ι j tr htr, Functor.map_comp]
    rw [← boundary.ι_ι sr, Functor.map_comp, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [← (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).isPushout.w]
    rw [(join.map (boundary (p + 1)).ι).naturality_assoc]
  · have : s.val < t.val := hst
    omega
  · rw [joinBoundaryHornRightFaceSucc_back p q j s hs hsf,
      joinBoundaryHornRightFaceSucc_back p q j t ht htf]
    have hslo : p + 2 ≤ s.val := by omega
    have htlo : p + 2 ≤ t.val := by omega
    set sr := joinBackIndexSucc p q s hsf
    set tr := joinBackIndexSucc p q t htf
    have hsr : sr ≠ j := joinBackIndexSucc_ne p q j s hsf hs
    have htr : tr ≠ j := joinBackIndexSucc_ne p q j t htf ht
    have hsface : horn.ι j (joinBackIndexSucc p q s hsf)
          (joinBackIndexSucc_ne p q j s hsf hs) =
        horn.ι j sr hsr := by rfl
    have htface : horn.ι j (joinBackIndexSucc p q t htf)
          (joinBackIndexSucc_ne p q j t htf ht) =
        horn.ι j tr htr := by rfl
    have hstr : sr < tr := by
      rw [Fin.lt_def]
      simp only [sr, tr, joinBackIndexSucc_val]
      have : s.val < t.val := hst
      omega
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < ((p + 1) + q) + 2 := by
      have htbound : t.val < p + q + 4 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < ((p + 1) + q) + 2 := by
      have hsbound : s.val < p + q + 4 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using s.isLt
      have htbound : t.val < p + q + 4 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hstval : s.val < t.val := hst
      simp only [Fin.coe_castPred]
      rw [show ((p + 1) + q) + 2 = p + q + 3 by omega]
      omega
    rw [joinBoundaryHornRightBackFaceSucc_δ p q j s hsf hs
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinBoundaryHornRightBackFaceSucc_δ p q j t htf ht
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
          Fin (((p + 1) + (q + 1)) + 2)).val =
          (p + 2) + (tr.pred (Fin.ne_zero_of_lt hstr)).val := by
        change (t.pred (Fin.ne_zero_of_lt hst)).val =
          p + 2 + (tr.pred (Fin.ne_zero_of_lt hstr)).val
        have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
        have hpred : (tr.pred (Fin.ne_zero_of_lt hstr)).val = tr.val - 1 := rfl
        have htrval : tr.val = t.val - (p + 2) := rfl
        have htrpos : 0 < tr.val := by
          have := hstr
          omega
        have hdecomp : p + 2 + tr.val = t.val := by
          rw [htrval]
          exact Nat.add_sub_of_le htlo
        omega
      have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin (((p + 1) + (q + 1)) + 2)).val =
          (p + 2) + (sr.castPred (Fin.ne_last_of_lt hstr)).val := by
        change (s.castPred (Fin.ne_last_of_lt hst)).val =
          p + 2 + (sr.castPred (Fin.ne_last_of_lt hstr)).val
        have hsrval : sr.val = s.val - (p + 2) := rfl
        have hcast : (sr.castPred (Fin.ne_last_of_lt hstr)).val = sr.val := rfl
        have hdecomp : p + 2 + sr.val = s.val := by
          rw [hsrval]
          exact Nat.add_sub_of_le hslo
        calc
          (s.castPred (Fin.ne_last_of_lt hst)).val = s.val := rfl
          _ = p + 2 + sr.val := hdecomp.symm
          _ = p + 2 + (sr.castPred (Fin.ne_last_of_lt hstr)).val := by
            rw [hcast]
      rw [show (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
            Fin ((p + 1) + (q + 1) + 2)) =
          (⟨p + 2 + (tr.pred (Fin.ne_zero_of_lt hstr)).val,
            by have := (tr.pred (Fin.ne_zero_of_lt hstr)).isLt; omega⟩ :
              Fin ((p + 1) + q + 3)) by apply Fin.ext; exact haL]
      rw [show (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
            Fin ((p + 1) + (q + 1) + 2)) =
          (⟨p + 2 + (sr.castPred (Fin.ne_last_of_lt hstr)).val,
            by have := (sr.castPred (Fin.ne_last_of_lt hstr)).isLt; omega⟩ :
              Fin ((p + 1) + q + 3)) by apply Fin.ext; exact haR]
      rw [joinHorn_backPush_assoc, joinHorn_backPush_assoc]
      rw [cancel_epi]
      rw [hsface, htface]
      simp only [← Category.assoc, ← Functor.map_comp]
      have hc := (horn.IsCompatible.of_hom
        (𝟙 (horn (q + 2) j : SSet.{u}))).δ_pred_comp
          sr tr (hj := hsr) (hk := htr) (hjk := hstr)
      simp only [Category.comp_id] at hc
      have hm := congrArg (join.obj (Δ[p + 1] : SSet.{u})).map hc
      exact congrArg (fun z => z ≫
        (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) (q + 1) j).inl) hm


end JoinHorn.Internal
end SSet
