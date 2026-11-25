/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Derangements.Finite

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A sum rule for derangements

The weighted sum telescopes by the signed first-order recurrence for
`numDerangements`. Its parity correction agrees with the side from which the
normalized derangement count approaches `Real.exp (-1)`.

See [Pain, *A Sum Rule for Derangements*](https://math.colgate.edu/~integers/z84/z84.pdf).
-/

namespace MetaMathlibExt

open Filter
open scoped Topology

private noncomputable abbrev derangementRatio (n : ℕ) : ℝ :=
  (numDerangements n : ℝ) / n.factorial

private theorem derangementRatio_succ (n : ℕ) :
    derangementRatio (n + 1) =
      derangementRatio n - (-1 : ℝ) ^ n / (n + 1).factorial := by
  have hd : (numDerangements (n + 1) : ℝ) =
      ((n : ℝ) + 1) * numDerangements n - (-1 : ℝ) ^ n := by
    exact_mod_cast numDerangements_succ n
  change (numDerangements (n + 1) : ℝ) / _ = _
  rw [hd, sub_div, sub_left_inj, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem one_div_factorial_succ_lt (n : ℕ) :
    (1 : ℝ) / (n + 2).factorial < 1 / (n + 1).factorial := by
  apply one_div_lt_one_div_of_lt (by positivity)
  rw [Nat.factorial_succ (n + 1), Nat.cast_mul]
  have hn : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < n + 2 by omega)
  simpa only [one_mul] using
    mul_lt_mul_of_pos_right hn (by positivity : (0 : ℝ) < (n + 1).factorial)

-- The ratios at odd indices increase to exp(-1), and those at even indices decrease to it.
private theorem derangementRatio_bounds (k : ℕ) :
    derangementRatio (2 * k + 1) < Real.exp (-1) ∧ Real.exp (-1) < derangementRatio (2 * k) := by
  have hstep (n : ℕ) : derangementRatio (n + 2) = derangementRatio n -
      (-1 : ℝ) ^ n * (1 / (n + 1).factorial - 1 / (n + 2).factorial) := by
    rw [show n + 2 = (n + 1) + 1 by rfl, derangementRatio_succ, derangementRatio_succ, pow_succ]
    ring
  have hm : StrictMono fun i : ℕ ↦ derangementRatio (2 * i + 1) := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega, hstep]
    simp only [show (-1 : ℝ) ^ (2 * i + 1) = -1 by simp [pow_succ],
      neg_one_mul, sub_neg_eq_add, lt_add_iff_pos_right]
    exact sub_pos.mpr (one_div_factorial_succ_lt (2 * i + 1))
  have ha : StrictAnti fun i : ℕ ↦ derangementRatio (2 * i) := by
    apply strictAnti_nat_of_succ_lt
    intro i
    rw [show 2 * (i + 1) = (2 * i) + 2 by omega, hstep]
    simp only [show (-1 : ℝ) ^ (2 * i) = 1 by simp, one_mul, sub_lt_self_iff]
    exact sub_pos.mpr (one_div_factorial_succ_lt (2 * i))
  have hOdd : Tendsto (fun i : ℕ ↦ derangementRatio (2 * i + 1)) atTop (𝓝 (Real.exp (-1))) :=
    numDerangements_tendsto_inv_e.comp (tendsto_atTop_mono (fun i ↦ by dsimp; omega) tendsto_id)
  have hEven : Tendsto (fun i : ℕ ↦ derangementRatio (2 * i)) atTop (𝓝 (Real.exp (-1))) :=
    numDerangements_tendsto_inv_e.comp (tendsto_atTop_mono (fun i ↦ by dsimp; omega) tendsto_id)
  exact ⟨(hm (Nat.lt_succ_self k)).trans_le (hm.monotone.ge_of_tendsto hOdd (k + 1)),
    (ha.antitone.le_of_tendsto hEven (k + 1)).trans_lt (ha (Nat.lt_succ_self k))⟩

private theorem sum_mul_numDerangements (p : ℕ) :
    ((∑ n ∈ Finset.range (p + 1), n * numDerangements n : ℕ) : ℤ) =
      (numDerangements (p + 1) : ℤ) - (if Even p then 0 else 1) := by
  push_cast
  calc
    _ = ∑ n ∈ Finset.range (p + 1),
        ((numDerangements (n + 1) : ℤ) - numDerangements n + (-1 : ℤ) ^ n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [numDerangements_succ]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun n ↦ (numDerangements n : ℤ)),
        neg_one_geom_sum]
      by_cases h : Even p <;> simp [Nat.even_add_one, h]

/-- **A sum rule for derangements.** For every natural number $p$,
$\sum_{n=0}^{p} n\, D(n) = \lfloor (p + 1)!/e \rfloor$, where $D(n)$ is the number of
derangements of $n$ objects.

Source: Jean-Christophe Pain, *A Sum Rule for Derangements*, INTEGERS 25 (2025),
Article A84, Theorem 1 (`integers-2025-A84-thm-1`). -/
public theorem sum_mul_numDerangements_eq_floor (p : ℕ) :
    ((∑ n ∈ Finset.range (p + 1), n * numDerangements n : ℕ) : ℤ) =
      ⌊((p + 1).factorial : ℝ) / Real.exp 1⌋ := by
  rw [sum_mul_numDerangements, eq_comm, Int.floor_eq_iff, div_eq_mul_inv, ← Real.exp_neg, mul_comm]
  have hf : (0 : ℝ) < (p + 1).factorial := by positivity
  rw [← div_le_iff₀ hf, ← lt_div_iff₀ hf]
  -- Two consecutive ratios enclose exp(-1). Their gap is less than 1/(p+1)!.
  have hgap := one_div_factorial_succ_lt p
  have hstep := derangementRatio_succ (p + 1)
  rcases Nat.even_or_odd p with he | ho
  · simp only [ite_eq_left he, sub_zero, Int.cast_natCast, add_div]
    have hsign : (-1 : ℝ) ^ (p + 1) = -1 := (he.add_odd odd_one).neg_one_pow
    rw [hsign, neg_div, sub_neg_eq_add] at hstep
    obtain ⟨k, hk⟩ := he
    have hp : p = 2 * k := by omega
    have hlo : derangementRatio (p + 1) < Real.exp (-1) := by
      rw [hp]
      exact (derangementRatio_bounds k).1
    have hhi : Real.exp (-1) < derangementRatio (p + 2) := by
      rw [show p + 2 = 2 * (k + 1) by omega]
      exact (derangementRatio_bounds (k + 1)).2
    exact ⟨hlo.le, hhi.trans (hstep.trans_lt (add_lt_add_right hgap _))⟩
  · simp only [ite_eq_right (Nat.not_even_iff_odd.mpr ho), Int.cast_sub, Int.cast_natCast,
      Int.cast_one, sub_add_cancel, sub_div]
    have hsign : (-1 : ℝ) ^ (p + 1) = 1 := (ho.add_odd odd_one).neg_one_pow
    rw [hsign] at hstep
    obtain ⟨k, hk⟩ := ho
    have hp : p + 1 = 2 * (k + 1) := by omega
    have hlo : derangementRatio (p + 2) < Real.exp (-1) := by
      rw [show p + 2 = p + 1 + 1 by rfl, hp]
      exact (derangementRatio_bounds (k + 1)).1
    have hhi : Real.exp (-1) < derangementRatio (p + 1) := by
      rw [hp]
      exact (derangementRatio_bounds (k + 1)).2
    exact ⟨((sub_lt_sub_left hgap _).trans_eq hstep.symm).le.trans hlo.le, hhi⟩

end MetaMathlibExt
