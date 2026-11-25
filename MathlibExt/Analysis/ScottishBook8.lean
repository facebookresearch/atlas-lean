/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Mazur's Problem 8

`mazur8CauchyProduct_refuted` gives a negative answer to the factorization question for
convergent real sequences. The counterexample uses Rudin–Shapiro signs on blocks of increasing
length. The parallelogram identity bounds the correlation of these signs with a Cauchy product.
-/

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook8Wanted

/-- **The claim of Scottish Book Problem 8.** This is the statement, asked about in form (b) of
Mazur's Problem 8 in the Scottish Book typescript, that every convergent sequence
$(z_n)_{n \ge 0}$ of real numbers can be written as
$z_n = \frac{1}{n+1} \sum_{k=0}^{n} x_k y_{n-k}$ for all $n \ge 0$, where $(x_n)_{n \ge 0}$
and $(y_n)_{n \ge 0}$ are convergent sequences of real numbers.

Indices are shifted to start at $0$. -/
def ScottishBookProblem8Claim : Prop :=
  ∀ (z : ℕ → ℝ), (∃ L, Filter.Tendsto z Filter.atTop (nhds L)) →
    ∃ (x y : ℕ → ℝ), (∃ Lx, Filter.Tendsto x Filter.atTop (nhds Lx)) ∧
      (∃ Ly, Filter.Tendsto y Filter.atTop (nhds Ly)) ∧
      ∀ n, z n = (∑ k ∈ Finset.range (n + 1), x k * y (n - k)) / (n + 1 : ℝ)

open Finset Filter
open scoped Topology

-- The two Rudin–Shapiro sign blocks P and Q grow by concatenating (P, Q) and (P, -Q).
private def signs : ℕ → Bool → ℕ → ℝ
  | 0, _, _ => 1
  | m + 1, b, j =>
    if j < 2 ^ m then signs m false j
    else if b then -signs m true (j - 2 ^ m) else signs m true (j - 2 ^ m)

private lemma abs_signs (m : ℕ) (b : Bool) (j : ℕ) : |signs m b j| = 1 := by
  induction m generalizing b j with
  | zero => simp [signs]
  | succ m ih => cases b <;> simp [signs, apply_ite abs, ih]

private noncomputable def blockSum (m : ℕ) (b : Bool) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range (2 ^ m), signs m b j * f (i + j)

private lemma blockSum_succ (m : ℕ) (b : Bool) (f : ℕ → ℝ) (i : ℕ) :
    blockSum (m + 1) b f i = blockSum m false f i +
      (if b then -blockSum m true f (i + 2 ^ m) else blockSum m true f (i + 2 ^ m)) := by
  unfold blockSum
  rw [pow_succ, Nat.mul_two, sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro j hj
    simp [signs, mem_range.mp hj]
  · cases b <;> simp [signs, add_assoc, sum_neg_distrib]

-- Summing over the enlarged interval covers both the original and the translated terms.
private lemma energy_le (f : ℕ → ℝ) {B : ℝ} (hf : ∀ i, f i ^ 2 ≤ B) (m R : ℕ) :
    (∑ i ∈ range R, (blockSum m false f i ^ 2 + blockSum m true f i ^ 2)) ≤
      2 * (2 : ℝ) ^ m * (R + (2 : ℝ) ^ m) * B := by
  have hB := (sq_nonneg (f 0)).trans (hf 0)
  induction m generalizing R with
  | zero =>
    simp only [blockSum, pow_zero, sum_range_one, signs, Nat.add_zero, one_mul]
    calc
      _ ≤ ∑ _ ∈ range R, (B + B) := sum_le_sum fun i _ => add_le_add (hf i) (hf i)
      _ ≤ _ := by simp; nlinarith
  | succ m ih =>
    let N := 2 ^ m
    let P := blockSum m false f
    let Q := blockSum m true f
    have hP : (∑ i ∈ range R, P i ^ 2) ≤ ∑ i ∈ range (R + N), P i ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_add_right R N)) (fun i _ _ => sq_nonneg _)
    have hQ : (∑ i ∈ range R, Q (i + N) ^ 2) ≤ ∑ i ∈ range (R + N), Q i ^ 2 := by
      rw [Nat.add_comm R N, sum_range_add]
      have h₀ : 0 ≤ ∑ i ∈ range N, Q i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
      simpa [Nat.add_comm] using le_add_of_nonneg_left
        (a := ∑ i ∈ range R, Q (N + i) ^ 2) h₀
    calc
      _ = 2 * ((∑ i ∈ range R, P i ^ 2) + ∑ i ∈ range R, Q (i + N) ^ 2) := by
        rw [← sum_add_distrib, mul_sum]
        apply sum_congr rfl
        intro i _
        simp [blockSum_succ, P, Q, N]
        ring
      _ ≤ 2 * ∑ i ∈ range (R + N), (P i ^ 2 + Q i ^ 2) := by
        rw [sum_add_distrib]
        linarith
      _ ≤ _ := by
        have h := ih (R + N)
        dsimp [N] at h ⊢
        push_cast at h
        rw [pow_succ]
        dsimp [P, Q]
        linarith

-- Pad y on the left so that the same summation interval works for every antidiagonal in a block.
private def padded (N : ℕ) (y : ℕ → ℝ) (i : ℕ) : ℝ := if N ≤ i then y (i - N) else 0

private lemma padded_sum (x y : ℕ → ℝ) {N j : ℕ} (hj : j < N) :
    ∑ i ∈ range (2 * N + 1), x (2 * N - i) * padded N y (i + j) =
      ∑ k ∈ range (N + j + 1), x k * y (N + j - k) := by
  rw [← sum_range_reflect (fun i => x (2 * N - i) * padded N y (i + j))]
  simp only [Nat.add_one_sub_one]
  rw [eventually_constant_sum (N := N + j + 1) (n := 2 * N + 1) _ (by omega)]
  · apply sum_congr rfl
    intro k hk
    have hk' := mem_range.mp hk
    simp [padded, show N ≤ 2 * N - k + j by omega,
      show 2 * N - (2 * N - k) = k by omega, show 2 * N - k + j - N = N + j - k by omega]
  · intro k hk
    simp [padded, show ¬N ≤ 2 * N - k + j by omega]

-- A block of unnormalized product coefficients equal to c times the signs forces c² = O(N).
private lemma block_bound (x y : ℕ → ℝ) {A B c : ℝ}
    (hx : ∀ i, x i ^ 2 ≤ A) (hy : ∀ i, y i ^ 2 ≤ B) (m : ℕ)
    (hc : ∀ j < 2 ^ m, (∑ k ∈ range (2 ^ m + j + 1), x k * y (2 ^ m + j - k)) =
      c * signs m false j) : c ^ 2 ≤ 24 * (2 : ℝ) ^ m * A * B := by
  let N := 2 ^ m
  let R := 2 * N + 1
  let f := padded N y
  let g := fun i => x (2 * N - i)
  have hB := (sq_nonneg (y 0)).trans (hy 0)
  have hA := (sq_nonneg (x 0)).trans (hx 0)
  have hf (i) : f i ^ 2 ≤ B := by
    dsimp [f, padded]
    split
    · apply hy
    · simpa using hB
  have hdot : (∑ i ∈ range R, g i * blockSum m false f i) = N * c := by
    simp only [blockSum, mul_sum]
    rw [sum_comm]
    calc
      _ = ∑ j ∈ range N, signs m false j * (∑ i ∈ range R, g i * f (i + j)) := by
        apply sum_congr rfl
        intro j _
        rw [mul_sum]
        exact sum_congr rfl (fun i _ => by ring)
      _ = ∑ _ ∈ range N, c := by
        apply sum_congr rfl
        intro j hj
        rw [show (∑ i ∈ range R, g i * f (i + j)) = c * signs m false j from
          (padded_sum x y (mem_range.mp hj)).trans (hc j (mem_range.mp hj))]
        have hs := congrArg (fun a : ℝ => a ^ 2) (abs_signs m false j)
        simp only [sq_abs, one_pow] at hs
        linear_combination c * hs
      _ = _ := by simp
  have hg : (∑ i ∈ range R, g i ^ 2) ≤ R * A := by
    simpa using sum_le_sum (s := range R) (g := fun _ => A) fun i _ => hx (2 * N - i)
  have hsum : (∑ i ∈ range R, blockSum m false f i ^ 2) ≤
      2 * (N : ℝ) * (R + (N : ℝ)) * B := by
    apply le_trans (sum_le_sum fun i _ => le_add_of_nonneg_right (sq_nonneg (blockSum m true f i)))
    simpa [N] using energy_le f hf m R
  have hcs := sum_mul_sq_le_sq_mul_sq (range R) g (blockSum m false f)
  rw [hdot] at hcs
  have h := hcs.trans (mul_le_mul hg hsum (sum_nonneg fun i _ => sq_nonneg _) (by positivity))
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_two_pow
  have hR : (R : ℝ) ≤ 3 * N := by dsimp [R]; push_cast; linarith
  have h' : (N * c) ^ 2 ≤ (3 * (N : ℝ) * A) * (2 * N * (4 * N) * B) := by
    apply h.trans
    gcongr
    linarith
  have hn : (0 : ℝ) < N := by linarith
  apply le_of_mul_le_mul_left (a := (N : ℝ) ^ 2) _ (sq_pos_of_pos hn)
  push_cast [N] at h' ⊢
  linarith only [h']

-- For N = 16^m the coefficients (n+1)zₙ have amplitude 8^m on [N, 2N).
-- This exceeds any fixed multiple of √N, although z itself tends to zero.
private noncomputable def witness (n : ℕ) : ℝ :=
  let m := Nat.log 16 n
  8 ^ m * signs (4 * m) false (n - 16 ^ m) / (n + 1)

private lemma witness_tendsto : Tendsto witness atTop (𝓝 0) := by
  have hlog : Tendsto (Nat.log 16) atTop atTop :=
    tendsto_atTop_atTop.mpr fun k => ⟨16 ^ k, fun _ hn => Nat.le_log_of_pow_le (by decide) hn⟩
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)).comp hlog
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun _ => abs_nonneg _) _ hlim
  intro n
  let m := Nat.log 16 n
  have hn : (16 : ℝ) ^ m ≤ n + 1 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [m]
    · have h : (16 : ℝ) ^ m ≤ n := by exact_mod_cast Nat.pow_log_le_self 16 hn
      linarith
  dsimp [Function.comp_def, witness]
  rw [abs_div, abs_mul, abs_signs, mul_one, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  calc
    (8 : ℝ) ^ m = (1 / 2 : ℝ) ^ m * 16 ^ m := by rw [← mul_pow]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

/--
**Mazur's Problem 8 has a negative answer.** There is a convergent sequence
$(z_n)_{n \ge 0}$ of real numbers that cannot be written as
$z_n = \frac{1}{n+1} \sum_{k=0}^{n} x_k y_{n-k}$ for all $n \ge 0$ with convergent sequences
$(x_n)_{n \ge 0}$ and $(y_n)_{n \ge 0}$ of real numbers. That is, the claim of Scottish Book
Problem 8 is false.

Source: S. Mazur, Problem 8 of the Scottish Book; negative
solution by V. V. Peller, "On S. Mazur's Problems 8 and 88 from the Scottish
Book", arXiv:math/0703716, building on Peller, J. Operator Theory 7 (1982)
341-372; independently Kwapien-Pelczynski and Eggermont-Leung, Proc. Amer.
Math. Soc. 96 (1986) 269-274.
-/
theorem mazur8CauchyProduct_refuted : ¬ ScottishBookProblem8Claim := by
  intro claim
  obtain ⟨x, y, ⟨Lx, hx⟩, ⟨Ly, hy⟩, hxy⟩ := claim witness ⟨0, witness_tendsto⟩
  obtain ⟨A, hA⟩ := (hx.pow 2).bddAbove_range
  obtain ⟨B, hB⟩ := (hy.pow 2).bddAbove_range
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (24 * A * B) (show (1 : ℝ) < 4 by norm_num)
  have hN : 2 ^ (4 * m) = 16 ^ m := by rw [pow_mul]; norm_num
  have hc (j) (hj : j < 2 ^ (4 * m)) :
      (∑ k ∈ range (2 ^ (4 * m) + j + 1), x k * y (2 ^ (4 * m) + j - k)) =
        8 ^ m * signs (4 * m) false j := by
    rw [hN] at hj ⊢
    have hl : Nat.log 16 (16 ^ m + j) = m :=
      Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
    have h := hxy (16 ^ m + j)
    simp only [witness, hl, Nat.add_sub_cancel_left] at h
    exact (div_left_inj₀ (by positivity)).mp h.symm
  have h := block_bound x y (fun i => hA ⟨i, rfl⟩) (fun i => hB ⟨i, rfl⟩) (4 * m) hc
  have hpow : ((8 : ℝ) ^ m) ^ 2 = (16 : ℝ) ^ m * 4 ^ m := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← mul_pow]
    norm_num
  rw [hpow, pow_mul] at h
  norm_num at h
  have hlt := mul_lt_mul_of_pos_left hm (show 0 < (16 : ℝ) ^ m by positivity)
  linarith only [h, hlt]

end MathlibExt.Analysis.ScottishBook8Wanted
