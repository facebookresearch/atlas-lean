/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.FK.RandomCluster

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]




def openCount (ω : ConfigSpace (Sym2 V)) : ℕ :=
  (G.edgeFinset.filter (fun e => ω e = true)).card


def closedCount (ω : ConfigSpace (Sym2 V)) : ℕ :=
  (G.edgeFinset.filter (fun e => ω e = false)).card

omit [DecidableEq V] in

theorem openCount_add_closedCount (ω : ConfigSpace (Sym2 V)) :
    openCount G ω + closedCount G ω = G.edgeFinset.card := by
  unfold openCount closedCount
  have hfilt : G.edgeFinset.filter (fun e => ω e = false)
      = G.edgeFinset.filter (fun e => ¬ ω e = true) := by
    apply Finset.filter_congr; intro e _; simp [Bool.not_eq_true]
  rw [hfilt, Finset.card_filter_add_card_filter_not]

omit [DecidableEq V] in


theorem edgeProduct_eq_pow (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p ω = p ^ openCount G ω * (1 - p) ^ closedCount G ω := by
  unfold edgeProduct openCount closedCount
  rw [← Finset.prod_filter_mul_prod_filter_not G.edgeFinset (fun e => ω e = true)]
  congr 1
  · rw [Finset.prod_congr rfl (fun e he => if_pos (Finset.mem_filter.1 he).2),
      Finset.prod_const]
  · have hfilt : G.edgeFinset.filter (fun e => ¬ ω e = true)
        = G.edgeFinset.filter (fun e => ω e = false) := by
      apply Finset.filter_congr; intro e _; simp [Bool.not_eq_true]
    rw [Finset.prod_congr rfl (fun e he => if_neg (Finset.mem_filter.1 he).2),
      Finset.prod_const, hfilt]






noncomputable def tiltFactor (p1 p2 : ℝ) : ℝ := p2 * (1 - p1) / ((1 - p2) * p1)


theorem tiltFactor_pos {p1 p2 : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) : 0 < tiltFactor p1 p2 := by
  unfold tiltFactor
  apply div_pos
  · exact mul_pos hp2 (by linarith)
  · exact mul_pos (by linarith) hp1



theorem tiltFactor_lt_one {p1 p2 : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hlt : p2 < p1) : tiltFactor p1 p2 < 1 := by
  unfold tiltFactor
  rw [div_lt_one (mul_pos (by linarith) hp1)]
  nlinarith







theorem pow_tilt_aux {p1 p2 : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (o c : ℕ) :
    p2 ^ o * (1 - p2) ^ c
      = ((1 - p2) / (1 - p1)) ^ (o + c)
        * tiltFactor p1 p2 ^ o * (p1 ^ o * (1 - p1) ^ c) := by
  unfold tiltFactor
  have h1p1 : (1 - p1) ≠ 0 := by linarith
  have h1p2 : (1 - p2) ≠ 0 := by linarith
  have hp1n : p1 ≠ 0 := ne_of_gt hp1
  rw [div_pow, div_pow, mul_pow, mul_pow, pow_add]
  field_simp
  ring







theorem fkWeight_tilt {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p2 q ω
      = ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card
        * tiltFactor p1 p2 ^ openCount G ω * fkWeight G p1 q ω := by
  unfold fkWeight
  rw [edgeProduct_eq_pow G p2 ω, edgeProduct_eq_pow G p1 ω,
    ← openCount_add_closedCount G ω,
    pow_tilt_aux hp1 hp1' hp2 hp2' (openCount G ω) (closedCount G ω)]
  ring





noncomputable def fkExpect (p q : ℝ) (X : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), fkProb G p q ω * X ω



theorem fkExpect_tiltPow_pos {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hq : 0 < q) :
    0 < fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
  unfold fkExpect
  apply Finset.sum_pos
  · intro ω _
    exact mul_pos (fkProb_pos G hp1 hp1' hq ω)
      (pow_pos (tiltFactor_pos hp1 hp1' hp2 hp2') _)
  · exact Finset.univ_nonempty





theorem fkZ_tilt {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) :
    fkZ G p2 q
      = ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card
        * ∑ ω : ConfigSpace (Sym2 V),
            tiltFactor p1 p2 ^ openCount G ω * fkWeight G p1 q ω := by
  unfold fkZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [fkWeight_tilt G hp1 hp1' hp2 hp2' ω]
  ring







theorem fkProb_tilt {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    fkProb G p2 q ω
      = tiltFactor p1 p2 ^ openCount G ω * fkProb G p1 q ω
        / fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
  have hCpos : (0 : ℝ) < ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card :=
    pow_pos (div_pos (by linarith) (by linarith)) _
  have hC : ((1 - p2) / (1 - p1)) ^ G.edgeFinset.card ≠ 0 := ne_of_gt hCpos
  have hZ1 : fkZ G p1 q ≠ 0 := fkZ_ne_zero G hp1 hp1' hq
  
  have hExp : fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω)
      = (∑ ω : ConfigSpace (Sym2 V), tiltFactor p1 p2 ^ openCount G ω * fkWeight G p1 q ω)
        / fkZ G p1 q := by
    unfold fkExpect fkProb
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    rw [div_mul_eq_mul_div, mul_comm (fkWeight G p1 q ω)]
  rw [fkProb, fkProb, fkZ_tilt G hp1 hp1' hp2 hp2', fkWeight_tilt G hp1 hp1' hp2 hp2' ω,
    hExp]
  field_simp








theorem fkExpect_tilt {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hq : 0 < q) (X : ConfigSpace (Sym2 V) → ℝ) :
    fkExpect G p2 q X
      = fkExpect G p1 q (fun ω => X ω * tiltFactor p1 p2 ^ openCount G ω)
        / fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω) := by
  unfold fkExpect
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [fkProb_tilt G hp1 hp1' hp2 hp2' hq ω]
  rw [show fkExpect G p1 q (fun ω => tiltFactor p1 p2 ^ openCount G ω)
    = ∑ ω : ConfigSpace (Sym2 V), fkProb G p1 q ω * tiltFactor p1 p2 ^ openCount G ω from rfl]
  ring

end FK

end StatMech
