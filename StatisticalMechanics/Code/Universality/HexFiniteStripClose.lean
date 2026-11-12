/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexInjections
import Code.Universality.HexBridge
import Code.Universality.HexBridgeRecon

namespace StatMech.Universality

open Complex HexWalk
open scoped BigOperators














noncomputable def hfs_stMid (m : ℂ) (h : ℤ) : List ℤ → ℂ
  | [] => m
  | t :: ts => hfs_stMid (m + halfStep h + halfStep (h + t)) (h + t) ts



def hfs_stHead (h : ℤ) : List ℤ → ℤ
  | [] => h
  | t :: ts => hfs_stHead (h + t) ts













theorem hfs_verticesAux_take (m : ℂ) (h : ℤ) (ts : List ℤ) (cp : ℕ) :
    verticesAux m h (ts.take cp) = (verticesAux m h ts).take (cp + 1) := by
  induction ts generalizing m h cp with
  | nil => simp [verticesAux]
  | cons t ts ih =>
    cases cp with
    | zero => simp [verticesAux]
    | succ k =>
      rw [List.take_succ_cons, verticesAux_cons, verticesAux_cons, List.take_succ_cons]
      congr 1
      exact ih _ _ k





theorem hfs_verticesAux_drop (m : ℂ) (h : ℤ) (ts : List ℤ) (cp : ℕ)
    (hcp : cp ≤ ts.length) :
    verticesAux (hfs_stMid m h (ts.take cp)) (hfs_stHead h (ts.take cp)) (ts.drop cp)
      = (verticesAux m h ts).drop cp := by
  induction ts generalizing m h cp with
  | nil => simp_all [hfs_stMid, hfs_stHead]
  | cons t ts ih =>
    cases cp with
    | zero => simp [hfs_stMid, hfs_stHead, verticesAux]
    | succ k =>
      simp only [List.take_succ_cons, List.drop_succ_cons, hfs_stMid, hfs_stHead,
        verticesAux_cons]
      apply ih
      simp only [List.length_cons] at hcp
      omega






theorem hfs_legalTurns_take (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hleg : (ofTurns a h0 ts).LegalTurns) :
    (ofTurns a h0 (ts.take cp)).LegalTurns := by
  unfold LegalTurns at hleg ⊢
  intro t ht
  simp only [ofTurns_turns] at ht ⊢
  exact hleg t (List.mem_of_mem_take ht)





theorem hfs_legalTurns_drop (a2 : ℂ) (h2 : ℤ) (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hleg : (ofTurns a h0 ts).LegalTurns) :
    (ofTurns a2 h2 (ts.drop cp)).LegalTurns := by
  unfold LegalTurns at hleg ⊢
  intro t ht
  simp only [ofTurns_turns] at ht ⊢
  exact hleg t (List.mem_of_mem_drop ht)






theorem hfs_isSAW_take (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (h : (ofTurns a h0 ts).IsSAW) :
    (ofTurns a h0 (ts.take cp)).IsSAW := by
  unfold IsSAW vertices at h ⊢
  simp only [ofTurns_startMid, ofTurns_h0, ofTurns_turns] at h ⊢
  rw [hfs_verticesAux_take]
  exact h.take





theorem hfs_isSAW_drop (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length)
    (h : (ofTurns a h0 ts).IsSAW) :
    (ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
      (ts.drop cp)).IsSAW := by
  unfold IsSAW vertices at h ⊢
  simp only [ofTurns_startMid, ofTurns_h0, ofTurns_turns] at h ⊢
  rw [hfs_verticesAux_drop a h0 ts cp hcp]
  exact h.drop







theorem hfs_isLegalSAW_take (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (h : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns a h0 (ts.take cp)).IsLegalSAW :=
  ⟨hfs_legalTurns_take a h0 ts cp h.1, hfs_isSAW_take a h0 ts cp h.2⟩







theorem hfs_isLegalSAW_drop (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hcp : cp ≤ ts.length) (h : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
      (ts.drop cp)).IsLegalSAW :=
  ⟨hfs_legalTurns_drop _ _ a h0 ts cp h.1, hfs_isSAW_drop a h0 ts cp hcp h.2⟩































noncomputable def hfs_hexHighestCutReconLegal (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (cpos : {ts // memD ts} → ℕ)
    (hcp : ∀ d : {ts // memD ts}, cpos d ≤ d.1.length)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 x (d.1.take (cpos d)))
    (hwtB2 : ∀ d, wtB (split d).2 = hexSAWwt
      (hfs_stMid a h0 (d.1.take (cpos d))) (hfs_stHead h0 (d.1.take (cpos d)))
      x (d.1.drop (cpos d)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable wtB) :
    HexHighestCut x⁻¹ :=
  hexHighestCutRecon a h0 hx memD B wtB wtB_nn cpos
    (fun d => hfs_stMid a h0 (d.1.take (cpos d)))
    (fun d => hfs_stHead h0 (d.1.take (cpos d)))
    hcp
    (fun d hd => hfs_isLegalSAW_take a h0 d.1 (cpos d) hd)
    (fun d hd => hfs_isLegalSAW_drop a h0 d.1 (cpos d) (hcp d) hd)
    split hwtB1 hwtB2 split_inj hDsum hBsum












theorem hfs_legality_fires :
    (ofTurns (0 : ℂ) 0 [1, -1]).LegalTurns ∧
    (ofTurns (0 : ℂ) 0 ([1, -1].take 1)).LegalTurns ∧
    (ofTurns (0 : ℂ) 0 [1, -1]).numVertices = 3 ∧
    (ofTurns (0 : ℂ) 0 ([1, -1].take 1)).numVertices = 2 ∧
    (ofTurns (0 : ℂ) 0 ([1, -1].drop 1)).numVertices = 2 := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro t ht; simp only [ofTurns_turns, List.mem_cons] at ht
    rcases ht with h | h | h <;> simp_all
  · intro t ht; simp only [ofTurns_turns, List.take, List.mem_cons] at ht
    rcases ht with h | h <;> simp_all

end StatMech.Universality
