/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftComparison

/-!
# Faces of the positive right-boundary left join--horn pushout
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

/-- The left-block face index in the smaller horn. -/
def joinHornBoundaryLeftFrontIndexSucc
    (p q : ℕ) (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : t.val ≤ p + 1) : Fin (p + 2) :=
  ⟨t.val, by omega⟩

lemma joinHornBoundaryLeftFrontIndexSucc_ne
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : t.val ≤ p + 1)
    (hne : t ≠ leftJoinHornIndex p (q + 1) i) :
    joinHornBoundaryLeftFrontIndexSucc p q t ht ≠ i := by
  intro h
  apply hne
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [joinHornBoundaryLeftFrontIndexSucc, leftJoinHornIndex] at hh ⊢
  exact hh

/-- A front-block inverse face for the positive right-dimensional left decomposition. -/
noncomputable def joinHornBoundaryLeftFrontFaceSucc
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : t.val ≤ p + 1)
    (hne : t ≠ leftJoinHornIndex p (q + 1) i) :
    (Δ[(p + 1) + (q + 1)] : SSet.{u}) ⟶
      (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).pt :=
  joinHornΔcastInv (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1)) ≫
    (joinStdSimplexIso p (q + 1)).inv ≫
      (join.map (horn.ι i (joinHornBoundaryLeftFrontIndexSucc p q t ht)
        (joinHornBoundaryLeftFrontIndexSucc_ne p q i t ht hne))).app
          (Δ[q + 1] : SSet.{u}) ≫
        (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inr

/-- A back-block inverse face for the positive right-dimensional left decomposition. -/
noncomputable def joinHornBoundaryLeftBackFaceSucc
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : ¬t.val ≤ p + 1) :
    (Δ[(p + 1) + (q + 1)] : SSet.{u}) ⟶
      (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).pt :=
  joinHornΔcastInv (by omega : (p + 1) + q + 1 = (p + 1) + (q + 1)) ≫
    (joinStdSimplexIso (p + 1) q).inv ≫
      (join.obj (Δ[p + 1] : SSet.{u})).map
        (boundary.ι (joinBackIndexSucc p q t ht)) ≫
        (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inl

/-- The inverse face family, selected by its join block. -/
noncomputable def joinHornBoundaryLeftFaceSucc
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p (q + 1) i) :
    (Δ[(p + 1) + (q + 1)] : SSet.{u}) ⟶
      (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).pt :=
  if ht : t.val ≤ p + 1 then
    joinHornBoundaryLeftFrontFaceSucc p q i t ht hne
  else
    joinHornBoundaryLeftBackFaceSucc p q i t ht

lemma joinHornBoundaryLeftFaceSucc_front
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p (q + 1) i)
    (ht : t.val ≤ p + 1) :
    joinHornBoundaryLeftFaceSucc p q i t hne =
      joinHornBoundaryLeftFrontFaceSucc p q i t ht hne :=
  dite_eq_left ht

lemma joinHornBoundaryLeftFaceSucc_back
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p (q + 1) i)
    (ht : ¬t.val ≤ p + 1) :
    joinHornBoundaryLeftFaceSucc p q i t hne =
      joinHornBoundaryLeftBackFaceSucc p q i t ht :=
  dite_eq_right ht

lemma joinHornBoundaryLeftFrontFaceSucc_δ
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : t.val ≤ p + 1)
    (hne : t ≠ leftJoinHornIndex p (q + 1) i)
    (d : Fin (((p + 1) + (q + 1)) + 1))
    (hd : d.val < p + (q + 1) + 2) :
    stdSimplex.δ d ≫ joinHornBoundaryLeftFrontFaceSucc p q i t ht hne =
      joinHornΔcast (by omega : (p + 1) + q = p + (q + 1)) ≫
        stdSimplex.δ (⟨d.val, hd⟩ : Fin (p + (q + 1) + 2)) ≫
          (joinStdSimplexIso p (q + 1)).inv ≫
            (join.map (horn.ι i (joinHornBoundaryLeftFrontIndexSucc p q t ht)
              (joinHornBoundaryLeftFrontIndexSucc_ne p q i t ht hne))).app
                (Δ[q + 1] : SSet.{u}) ≫
              (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inr := by
  unfold joinHornBoundaryLeftFrontFaceSucc
  rw [joinHornΔcastInv_eq]
  rw [← Category.assoc,
    joinHorn_δ_joinHornΔcast
      (by omega : ((p + 1) + q) + 1 = (p + (q + 1)) + 1)
      (by omega : (p + 1) + q = p + (q + 1))
      d (⟨d.val, hd⟩ : Fin (p + (q + 1) + 2)) rfl,
    Category.assoc]

lemma joinHornBoundaryLeftBackFaceSucc_δ
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : ¬t.val ≤ p + 1)
    (d : Fin (((p + 1) + (q + 1)) + 1))
    (hd : d.val < ((p + 1) + q) + 2) :
    stdSimplex.δ d ≫ joinHornBoundaryLeftBackFaceSucc p q i t ht =
      stdSimplex.δ (⟨d.val, hd⟩ : Fin (((p + 1) + q) + 2)) ≫
        (joinStdSimplexIso (p + 1) q).inv ≫
          (join.obj (Δ[p + 1] : SSet.{u})).map
            (boundary.ι (joinBackIndexSucc p q t ht)) ≫
            (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inl := by
  unfold joinHornBoundaryLeftBackFaceSucc
  rw [joinHornΔcastInv_eq]
  rw [← Category.assoc,
    joinHorn_δ_joinHornΔcast
      (rfl : ((p + 1) + q) + 1 = ((p + 1) + q) + 1)
      (rfl : (p + 1) + q = (p + 1) + q)
      d (⟨d.val, hd⟩ : Fin (((p + 1) + q) + 2)) rfl,
    joinHornΔcast_rfl, Category.id_comp]

lemma joinHornBoundaryLeftFaceSucc_compatible
    (p q : ℕ) (i : Fin (p + 2)) :
    horn.IsCompatible (joinHornBoundaryLeftFaceSucc.{u} p q i) := by
  rw [horn.isCompatible_iff]
  intro s t hs ht hst
  by_cases hsf : s.val ≤ p + 1 <;> by_cases htf : t.val ≤ p + 1
  · rw [joinHornBoundaryLeftFaceSucc_front p q i s hs hsf,
      joinHornBoundaryLeftFaceSucc_front p q i t ht htf]
    set sr := joinHornBoundaryLeftFrontIndexSucc p q s hsf
    set tr := joinHornBoundaryLeftFrontIndexSucc p q t htf
    have hsr : sr ≠ i := joinHornBoundaryLeftFrontIndexSucc_ne p q i s hsf hs
    have htr : tr ≠ i := joinHornBoundaryLeftFrontIndexSucc_ne p q i t htf ht
    have hstr : sr < tr := by
      rw [Fin.lt_def]
      dsimp [sr, tr, joinHornBoundaryLeftFrontIndexSucc]
      exact hst
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < p + (q + 1) + 2 := by
      have htbound : t.val < p + q + 4 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < p + (q + 1) + 2 := by
      have htbound : t.val < p + q + 4 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hstval : s.val < t.val := hst
      simp only [Fin.coe_castPred]
      omega
    rw [joinHornBoundaryLeftFrontFaceSucc_δ p q i s hsf hs
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinHornBoundaryLeftFrontFaceSucc_δ p q i t htf ht
          (s.castPred (Fin.ne_last_of_lt hst)) hdR]
    rw [cancel_epi]
    obtain _ | p := p
    · have hsrval : sr.val ≠ i.val := fun h => hsr (Fin.ext h)
      have htrval : tr.val ≠ i.val := fun h => htr (Fin.ext h)
      have hstrval : sr.val < tr.val := hstr
      have hsrlt := sr.isLt
      have htrlt := tr.isLt
      have hilt := i.isLt
      omega
    · have haL : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
          Fin ((p + 1) + (q + 1) + 2)).val =
          (tr.pred (Fin.ne_zero_of_lt hstr)).val := by
        change (t.pred (Fin.ne_zero_of_lt hst)).val =
          (tr.pred (Fin.ne_zero_of_lt hstr)).val
        have hp1 : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
        have hp2 : (tr.pred (Fin.ne_zero_of_lt hstr)).val = tr.val - 1 := rfl
        have htrval : tr.val = t.val := rfl
        omega
      have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin ((p + 1) + (q + 1) + 2)).val =
          (sr.castPred (Fin.ne_last_of_lt hstr)).val := by
        rfl
      rw [joinHorn_frontPush_assoc _ _ haL, joinHorn_frontPush_assoc _ _ haR]
      rw [cancel_epi, cancel_epi]
      simp only [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp]
      have hc := (horn.IsCompatible.of_hom
        (𝟙 (horn (p + 2) i : SSet.{u}))).δ_pred_comp
          sr tr (hj := hsr) (hk := htr) (hjk := hstr)
      simp only [Category.comp_id] at hc
      have hm := congrArg (fun z => (join.map z).app (Δ[q + 1] : SSet.{u})) hc
      exact congrArg (fun z => z ≫
        (joinHornBoundaryLeftPushoutObjObj.{u} (p + 1) (q + 1) i).inr) hm
  · rw [joinHornBoundaryLeftFaceSucc_front p q i s hs hsf,
      joinHornBoundaryLeftFaceSucc_back p q i t ht htf]
    set sr := joinHornBoundaryLeftFrontIndexSucc p q s hsf
    set tr := joinBackIndexSucc p q t htf
    have hsr : sr ≠ i :=
      joinHornBoundaryLeftFrontIndexSucc_ne p q i s hsf hs
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
    rw [joinHornBoundaryLeftFrontFaceSucc_δ p q i s hsf hs
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinHornBoundaryLeftBackFaceSucc_δ p q i t htf
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
      dsimp [sr, joinHornBoundaryLeftFrontIndexSucc]
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
    have hsface : horn.ι i
          (joinHornBoundaryLeftFrontIndexSucc p q s hsf)
          (joinHornBoundaryLeftFrontIndexSucc_ne p q i s hsf hs) =
        horn.ι i sr hsr := by rfl
    have htface : boundary.ι (joinBackIndexSucc p q t htf) =
        boundary.ι tr := by rfl
    rw [hsface, htface]
    simp only [← Category.assoc]
    rw [(join.map (horn.ι i sr hsr)).naturality]
    rw [← boundary.ι_ι tr, Functor.map_comp]
    rw [← horn.ι_ι i sr hsr, Functor.map_comp, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [← (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).isPushout.w]
    rw [(join.map (horn (p + 1) i).ι).naturality_assoc]
  · have : s.val < t.val := hst
    omega
  · rw [joinHornBoundaryLeftFaceSucc_back p q i s hs hsf,
      joinHornBoundaryLeftFaceSucc_back p q i t ht htf]
    set sr := joinBackIndexSucc p q s hsf
    set tr := joinBackIndexSucc p q t htf
    have hstr : sr < tr := by
      rw [Fin.lt_def]
      dsimp [sr, tr, joinBackIndexSucc]
      have : s.val < t.val := hst
      omega
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < ((p + 1) + q) + 2 := by
      have htbound : t.val < p + q + 4 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < ((p + 1) + q) + 2 := by
      have htbound : t.val < p + q + 4 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt
      have hstval : s.val < t.val := hst
      simp only [Fin.coe_castPred]
      rw [show ((p + 1) + q) + 2 = p + q + 3 by omega]
      omega
    rw [joinHornBoundaryLeftBackFaceSucc_δ p q i s hsf
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinHornBoundaryLeftBackFaceSucc_δ p q i t htf
          (s.castPred (Fin.ne_last_of_lt hst)) hdR]
    obtain _ | q := q
    · have hsr0 : sr = 0 := by
        apply Fin.ext
        change sr.val = 0
        have hsrlt := sr.isLt
        have htrlt := tr.isLt
        have := hstr
        omega
      have htr1 : tr = 1 := by
        apply Fin.ext
        change tr.val = 1
        have hsrlt := sr.isLt
        have htrlt := tr.isLt
        have := hstr
        omega
      have hsval : s.val = p + 2 := by
        have hslo : p + 2 ≤ s.val := by omega
        have hsrval : sr.val = s.val - (p + 2) := rfl
        have := congrArg Fin.val hsr0
        omega
      have htval : t.val = p + 3 := by
        have htlo : p + 2 ≤ t.val := by omega
        have htrval : tr.val = t.val - (p + 2) := rfl
        have := congrArg Fin.val htr1
        omega
      have haL : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
          Fin ((p + 1) + 0 + 2)) = Fin.last (p + 2) := by
        apply Fin.ext
        have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
        simp only [Fin.val_last]
        omega
      have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin ((p + 1) + 0 + 2)) = Fin.last (p + 2) := by
        apply Fin.ext
        simp only [Fin.coe_castPred, Fin.val_last]
        omega
      rw [haL, haR, joinHorn_backPush_zero_assoc, joinHorn_backPush_zero_assoc]
      simp only [← Category.assoc]
      rw [joinInl_comp_map, joinInl_comp_map]
    · have hslo : p + 2 ≤ s.val := by omega
      have htlo : p + 2 ≤ t.val := by omega
      have haL : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
          Fin (((p + 1) + (q + 1)) + 2)).val =
          p + 2 + (tr.pred (Fin.ne_zero_of_lt hstr)).val := by
        change (t.pred (Fin.ne_zero_of_lt hst)).val =
          p + 2 + (tr.pred (Fin.ne_zero_of_lt hstr)).val
        have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
        have hpred : (tr.pred (Fin.ne_zero_of_lt hstr)).val = tr.val - 1 := rfl
        have htrval : tr.val = t.val - (p + 2) := rfl
        have htrpos : 0 < tr.val := by have := hstr; omega
        have hdecomp : p + 2 + tr.val = t.val := by
          rw [htrval]
          exact Nat.add_sub_of_le htlo
        omega
      have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin (((p + 1) + (q + 1)) + 2)).val =
          p + 2 + (sr.castPred (Fin.ne_last_of_lt hstr)).val := by
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
          _ = p + 2 + (sr.castPred (Fin.ne_last_of_lt hstr)).val := by rw [hcast]
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
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [boundary.ι_isCompatible (q + 1) sr tr hstr]

end JoinHorn.Internal
end SSet
