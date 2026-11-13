/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Nat.Choose.Sum

/-!
# The binomial upper tail as a function of the success probability

The upper tail `P(Bin(n, p) ≥ k) = ∑_{i = k}^{n} C(n, i) p^i (1 - p)^(n - i)` as an explicit
polynomial in `p`, with its boundary values, its derivative in `p`, and its monotonicity in
`p` and in `k`. `upperTail_binomial` (`MathlibExt.Probability.Statistics.ExactTests`) identifies
it with the upper tail of Mathlib's `binomial` measure for `p ∈ [0, 1]`.

## Main results

* `binomTail_zero`, `binomTail_of_lt`: `P(X ≥ 0) = 1` and `P(X ≥ k) = 0` for `k > n`.
* `binomTail_zero_right`, `binomTail_one_right`: the values `0` at `p = 0` (for `k ≥ 1`) and
  `1` at `p = 1` (for `k ≤ n`).
* `binomTail_succ_le`: the tail is nonincreasing in `k` (for `p ∈ [0, 1]`).
* `continuous_binomTail`, `hasDerivAt_binomTail`:
  `d/dp P(Bin(n, p) ≥ k) = n C(n - 1, k - 1) p^(k-1) (1 - p)^(n-k)` for `1 ≤ k ≤ n`.
* `monotoneOn_binomTail`, `strictMonoOn_binomTail`: the tail is (strictly, for `1 ≤ k ≤ n`)
  increasing in `p` on `[0, 1]`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, 3rd ed.,
  Wiley, 1968 (binomial tails).
-/

@[expose] public section

open Finset

namespace ProbabilityTheory

/-- The upper tail `P(X ≥ k) = ∑_{i = k}^{n} C(n, i) p^i (1 - p)^(n - i)` of the binomial law
`Bin(n, p)`. -/
noncomputable def binomTail (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ Icc k n, (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

/-- `P(X ≥ 0) = 1`, for every real `p` (the binomial theorem). -/
theorem binomTail_zero (n : ℕ) (p : ℝ) : binomTail n 0 p = 1 := by
  have h := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at h
  have hI : Icc 0 n = range (n + 1) := by ext i; simp
  rw [binomTail, hI]
  exact (sum_congr rfl fun i _ => by ring).trans h

/-- `P(X ≥ k) = 0` for `k > n`. -/
theorem binomTail_of_lt {n k : ℕ} (h : n < k) (p : ℝ) : binomTail n k p = 0 := by
  rw [binomTail, Icc_eq_empty (not_le.2 h), sum_empty]

/-- The binomial upper tail vanishes at `p = 0` when the cutoff is positive. -/
theorem binomTail_zero_right {n x : ℕ} (hx : 1 ≤ x) : binomTail n x 0 = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [zero_pow (by have := (Finset.mem_Icc.mp hi).1; omega)]
  ring

/-- The binomial upper tail is `1` at `p = 1` when the cutoff is at most `n`. -/
theorem binomTail_one_right {n x : ℕ} (hx : x ≤ n) : binomTail n x 1 = 1 := by
  rw [binomTail, Finset.sum_eq_single_of_mem n (Finset.mem_Icc.mpr ⟨hx, le_rfl⟩)]
  · simp
  · intro i hi hin
    have : i < n := lt_of_le_of_ne (Finset.mem_Icc.mp hi).2 hin
    rw [sub_self, zero_pow (by omega)]
    ring

/-- The binomial upper tail is continuous in `p`. -/
theorem continuous_binomTail (n x : ℕ) : Continuous (binomTail n x) := by
  unfold binomTail
  fun_prop

/-- **The tail is nonincreasing in `k`** for `p ∈ [0, 1]`. -/
theorem binomTail_succ_le (n k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomTail n (k + 1) p ≤ binomTail n k p :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (Nat.le_succ k)) fun _ _ _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
      (pow_nonneg (sub_nonneg.2 hp1) _)

private theorem sum_Icc_pred_sub {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (f : ℕ → ℝ) :
    (∑ i ∈ Icc k n, (f (i - 1) - f i)) = f (k - 1) - f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : k ≤ n
    · rw [sum_Icc_succ_top (by omega), ih h]
      simp only [Nat.add_sub_cancel]
      ring
    · have he : k = n + 1 := by omega
      subst k
      simp

private theorem hasDerivAt_binomTerm {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (p : ℝ) :
    HasDerivAt (fun p : ℝ => (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i))
      ((n : ℝ) * (((n - 1).choose (i - 1) : ℝ) * p ^ (i - 1) * (1 - p) ^ (n - i) -
        ((n - 1).choose i : ℝ) * p ^ i * (1 - p) ^ (n - 1 - i))) p := by
  have hn : n - 1 + 1 = n := by omega
  have hi' : i - 1 + 1 = i := by omega
  have hc₁ : (n.choose i : ℝ) * (i : ℝ) =
      (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (i - 1)
    rw [hn, hi'] at h
    exact_mod_cast h.symm
  have hc₂ : (n.choose i : ℝ) * (n - i : ℕ) =
      (n : ℝ) * ((n - 1).choose i : ℝ) := by
    have h := Nat.choose_mul_succ_eq (n - 1) i
    rw [hn] at h
    exact_mod_cast h.symm.trans (Nat.mul_comm _ _)
  have he : n - i - 1 = n - 1 - i := by omega
  convert ((hasDerivAt_pow i p).const_mul (n.choose i : ℝ)).mul
    (((hasDerivAt_id p).const_sub 1).pow (n - i)) using 1
  · rfl
  · simp only [he, Pi.pow_apply, id_eq]
    symm
    calc
      _ = ((n.choose i : ℝ) * (i : ℝ)) * p ^ (i - 1) * (1 - p) ^ (n - i) -
          ((n.choose i : ℝ) * (n - i : ℕ)) * p ^ i * (1 - p) ^ (n - 1 - i) := by
        ring
      _ = _ := by rw [hc₁, hc₂]; ring

/-- **Derivative of the binomial upper tail** in the success probability: for `1 ≤ k ≤ n`,
`d/dp P(Bin(n, p) ≥ k) = n C(n - 1, k - 1) p^(k-1) (1-p)^(n-k)` at every real `p` (the sum
telescopes). -/
theorem hasDerivAt_binomTail {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (p : ℝ) :
    HasDerivAt (binomTail n k)
      (n * ((n - 1).choose (k - 1) : ℝ) * p ^ (k - 1) * (1 - p) ^ (n - k)) p := by
  let A : ℕ → ℝ := fun i =>
    ((n - 1).choose i : ℝ) * p ^ i * (1 - p) ^ (n - 1 - i)
  have hd : HasDerivAt (binomTail n k)
      (∑ i ∈ Icc k n, (n : ℝ) * (A (i - 1) - A i)) p := by
    unfold binomTail
    apply HasDerivAt.fun_sum
    intro i hi
    have hki := (mem_Icc.mp hi).1
    have hin := (mem_Icc.mp hi).2
    have hi' : 1 ≤ i := hk.trans hki
    have he : n - 1 - (i - 1) = n - i := by omega
    simpa only [A, he] using hasDerivAt_binomTerm hi' hin p
  have hn : n - 1 < n := by omega
  have he : n - 1 - (k - 1) = n - k := by omega
  have hsum : (∑ i ∈ Icc k n, (n : ℝ) * (A (i - 1) - A i)) =
      n * ((n - 1).choose (k - 1) : ℝ) * p ^ (k - 1) * (1 - p) ^ (n - k) := by
    rw [← mul_sum, sum_Icc_pred_sub hk hkn]
    simp only [A, Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, zero_mul, sub_zero, he]
    ring
  exact hsum ▸ hd

/-- **The binomial upper tail is nondecreasing in `p` on `[0, 1]`**, for every `n` and `k`. -/
theorem monotoneOn_binomTail (n k : ℕ) : MonotoneOn (binomTail n k) (Set.Icc 0 1) := by
  by_cases hk : k = 0
  · subst k
    intro x hx y hy hxy
    simp only [binomTail_zero]
    exact le_rfl
  by_cases hkn : k ≤ n
  · have hk' : 1 ≤ k := by omega
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro p hp
      exact (hasDerivAt_binomTail hk' hkn p).continuousAt.continuousWithinAt
    · intro p hp
      exact (hasDerivAt_binomTail hk' hkn p).differentiableAt.differentiableWithinAt
    · intro p hp
      rw [interior_Icc] at hp
      rw [(hasDerivAt_binomTail hk' hkn p).deriv]
      have hp₀ : 0 ≤ p := le_of_lt hp.1
      have hp₁ : 0 ≤ 1 - p := sub_nonneg.mpr (le_of_lt hp.2)
      positivity
  · have he : Icc k n = ∅ := Icc_eq_empty_of_lt (by omega)
    intro x hx y hy hxy
    simp only [binomTail, he, sum_empty]
    exact le_rfl

/-- **The binomial upper tail is strictly increasing in `p` on `[0, 1]`** when `1 ≤ k ≤ n`. -/
theorem strictMonoOn_binomTail {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    StrictMonoOn (binomTail n k) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · intro p hp
    exact (hasDerivAt_binomTail hk hkn p).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hasDerivAt_binomTail hk hkn p).deriv]
    have hn : 0 < n := by omega
    have hc : 0 < (n - 1).choose (k - 1) := Nat.choose_pos (by omega)
    have hp₀ : 0 < p := hp.1
    have hp₁ : 0 < 1 - p := sub_pos.mpr hp.2
    positivity

end ProbabilityTheory
