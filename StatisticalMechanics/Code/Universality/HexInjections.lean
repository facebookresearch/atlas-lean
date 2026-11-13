/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexConnEndgame
import Code.Universality.HexBridge

namespace StatMech.Universality

open Complex
open scoped BigOperators












noncomputable def hexSAWwt (a : ℂ) (h0 : ℤ) (x : ℝ) (ts : List ℤ) : ℝ :=
  haveI := Classical.propDecidable ((HexWalk.ofTurns a h0 ts).IsLegalSAW)
  if (HexWalk.ofTurns a h0 ts).IsLegalSAW then x ^ (HexWalk.ofTurns a h0 ts).numVertices else 0


theorem hexSAWwt_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (ts : List ℤ) :
    0 ≤ hexSAWwt a h0 x ts := by
  unfold hexSAWwt
  split <;> positivity


theorem hexSAWwt_of_isLegalSAW (a : ℂ) (h0 : ℤ) (x : ℝ) {ts : List ℤ}
    (h : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    hexSAWwt a h0 x ts = x ^ (HexWalk.ofTurns a h0 ts).numVertices := by
  unfold hexSAWwt
  rw [if_pos h]












theorem hexHalfStep_re_abs (h : ℤ) : |(HexWalk.halfStep h).re| ≤ 1 / 2 := by
  unfold HexWalk.halfStep
  rw [Complex.mul_re]
  have hb : |(hexUnit h).re| ≤ 1 :=
    le_trans (Complex.abs_re_le_norm _) (le_of_eq (norm_hexUnit h))
  simp only [show ((1 : ℂ) / 2).re = 1 / 2 by norm_num,
    show ((1 : ℂ) / 2).im = 0 by norm_num]
  rw [abs_le] at hb ⊢
  constructor <;> nlinarith [hb.1, hb.2]






theorem hexVerticesAux_re_le (m : ℂ) (h : ℤ) (ts : List ℤ) :
    ∀ v ∈ HexWalk.verticesAux m h ts, v.re ≤ m.re + (ts.length + 1 : ℝ) := by
  induction ts generalizing m h with
  | nil =>
    intro v hv
    rw [HexWalk.verticesAux_nil] at hv
    simp only [List.mem_singleton] at hv
    subst hv
    have hh := hexHalfStep_re_abs h
    rw [abs_le] at hh
    simp only [Complex.add_re, List.length_nil]
    push_cast
    nlinarith [hh.1, hh.2]
  | cons t ts ih =>
    intro v hv
    rw [HexWalk.verticesAux_cons] at hv
    simp only [List.mem_cons] at hv
    rcases hv with hv | hv
    · subst hv
      have hh := hexHalfStep_re_abs h
      rw [abs_le] at hh
      simp only [Complex.add_re, List.length_cons]
      push_cast
      nlinarith [hh.1, hh.2]
    · have hih := ih (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) v hv
      have b1 := hexHalfStep_re_abs h
      have b2 := hexHalfStep_re_abs (h + t)
      rw [abs_le] at b1 b2
      simp only [Complex.add_re, List.length_cons] at hih ⊢
      push_cast at hih ⊢
      nlinarith [hih, b1.1, b1.2, b2.1, b2.2]






theorem hexReachWidth_len_ge (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ)
    (hreach : ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re) :
    T ≤ (HexWalk.ofTurns a h0 ts).numVertices := by
  obtain ⟨v, hv, hge⟩ := hreach
  
  have hle : v.re ≤ a.re + (ts.length + 1 : ℝ) := by
    have := hexVerticesAux_re_le a h0 ts v
    simpa [HexWalk.vertices, HexWalk.ofTurns] using this hv
  
  have : (T : ℝ) ≤ (ts.length + 1 : ℝ) := by linarith
  have hnat : T ≤ ts.length + 1 := by exact_mod_cast this
  simpa [HexWalk.numVertices, HexWalk.ofTurns] using hnat


















noncomputable def hexColumnOfWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (mem : List ℤ → Prop)
    (hreach : ∀ ts, mem ts →
      ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re)
    (hsummable : Summable (fun w : {ts // mem ts} =>
      χ ^ (HexWalk.ofTurns a h0 w.1).numVertices))
    (hle_one : (∑' w : {ts // mem ts},
      χ ^ (HexWalk.ofTurns a h0 w.1).numVertices) ≤ 1) :
    HexColumn T χ where
  W := {ts : List ℤ // mem ts}
  len := fun w => (HexWalk.ofTurns a h0 w.1).numVertices
  len_ge := fun w => hexReachWidth_len_ge a h0 T w.1 (hreach w.1 w.2)
  crit_summable := hsummable
  crit_le_one := hle_one



theorem hexColumnOfWidth_colSum (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (mem : List ℤ → Prop) (hreach hsummable hle_one) (y : ℝ) :
    (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum y
      = ∑' w : {ts // mem ts}, y ^ (HexWalk.ofTurns a h0 w.1).numVertices := rfl













noncomputable def hexContourEmbOfPred (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) :
    HexContourEmb (List ℤ) {ts : List ℤ // P ts} where
  wtSAW := hexSAWwt a h0 x
  emb := fun s => s.1
  emb_inj := Subtype.val_injective
  wtSAW_nn := hexSAWwt_nonneg a h0 hx



theorem hexContourEmbOfPred_wtSAW (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) :
    (hexContourEmbOfPred a h0 hx P).wtSAW = hexSAWwt a h0 x := rfl



theorem hexContourEmbOfPred_wtContour (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) (i : {ts : List ℤ // P ts}) :
    (hexContourEmbOfPred a h0 hx P).wtContour i = hexSAWwt a h0 x i.1 := rfl





noncomputable def hexColumnEmbOfPred (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) (scale : {ts : List ℤ // P ts} → ℕ) :
    HexColumnEmb (List ℤ) {ts : List ℤ // P ts} where
  wtSAW := hexSAWwt a h0 x
  emb := fun s => s.1
  emb_inj := Subtype.val_injective
  wtSAW_nn := hexSAWwt_nonneg a h0 hx
  scale := scale



theorem hexColumnEmbOfPred_wtSAW (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) (scale : {ts : List ℤ // P ts} → ℕ) :
    (hexColumnEmbOfPred a h0 hx P scale).wtSAW = hexSAWwt a h0 x := rfl













def hexSplitAt (cp : List ℤ → ℕ) (ts : List ℤ) : (List ℤ × ℕ) × (List ℤ × ℕ) :=
  ((ts.take (cp ts), cp ts), (ts.drop (cp ts), cp ts))






theorem hexSplitAt_injective (cp : List ℤ → ℕ) :
    Function.Injective (hexSplitAt cp) := by
  intro s t h
  unfold hexSplitAt at h
  have h1 : (s.take (cp s), cp s) = (t.take (cp t), cp t) := (Prod.mk.injEq _ _ _ _).mp h |>.1
  have h2 : (s.drop (cp s), cp s) = (t.drop (cp t), cp t) := (Prod.mk.injEq _ _ _ _).mp h |>.2
  have htake : s.take (cp s) = t.take (cp t) := (Prod.mk.injEq _ _ _ _).mp h1 |>.1
  have hdrop : s.drop (cp s) = t.drop (cp t) := (Prod.mk.injEq _ _ _ _).mp h2 |>.1
  calc s = s.take (cp s) ++ s.drop (cp s) := (List.take_append_drop _ _).symm
    _ = t.take (cp t) ++ t.drop (cp t) := by rw [htake, hdrop]
    _ = t := List.take_append_drop _ _














noncomputable def hexCutPos (a : ℂ) (h0 : ℤ) (ts : List ℤ) : ℕ :=
  haveI : DecidableLT ℝ := Classical.decRel _
  match (HexWalk.ofTurns a h0 ts).vertices.argmax (fun v => v.re) with
  | none => 0
  | some v => (HexWalk.ofTurns a h0 ts).vertices.idxOf v







theorem hexHighestCutSplit_injective (a : ℂ) (h0 : ℤ) :
    Function.Injective (hexSplitAt (hexCutPos a h0)) :=
  hexSplitAt_injective _













noncomputable def hexHWCutPos (a : ℂ) (h0 : ℤ) (ts : List ℤ) : ℕ :=
  haveI : DecidableLT ℝ := Classical.decRel _
  match (HexWalk.ofTurns a h0 ts).vertices.argmax (fun v => v.re) with
  | none => 0
  | some v => (HexWalk.ofTurns a h0 ts).vertices.length -
      ((HexWalk.ofTurns a h0 ts).vertices.reverse.idxOf v + 1)







theorem hexHWDecomp_injective (a : ℂ) (h0 : ℤ) :
    Function.Injective (hexSplitAt (hexHWCutPos a h0)) :=
  hexSplitAt_injective _

end StatMech.Universality
