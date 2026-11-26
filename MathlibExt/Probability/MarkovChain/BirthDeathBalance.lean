/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Birth–death balance weights

We characterize the probability weights on `ℕ` that satisfy the birth–death balance equations.
The balance equations and product formula appear in J. Figueroa-O'Farrill,
[*Mathematics for Informatics 4a*, Lecture 21, slides 2–3][lecture].

[lecture]: https://webhomes.maths.ed.ac.uk/~jmf/Teaching/mi4a/Lecture21-2012.04.04.pdf
-/

open scoped BigOperators

namespace ProbabilityTheory

/-- For nonnegative birth rates and strictly positive death rates at every positive index, put
`θ n = ∏ i ∈ Finset.range n, birth i / death (i + 1)`, so `θ 0 = 1`. A sequence is
nonnegative, sums to one, and satisfies the balance equations if and only if `θ` is summable and
each coordinate is `θ n / ∑' i, θ i`. In particular, the solution is unique whenever it exists. If a
birth rate vanishes at `k`, all weights past `k` vanish and the weights are summable, so the
normalized sequence exists. No conditions are imposed on `death 0`. This is a statement about
balance equations, not about a stochastic process. -/
public theorem birthDeathBalanceWeights_normalized (birth death : ℕ → ℝ)
    (hbirth : ∀ n, 0 ≤ birth n) (hdeath : ∀ n, 0 < death (n + 1)) :
    let θ : ℕ → ℝ := fun n ↦ ∏ i ∈ Finset.range n, birth i / death (i + 1)
    (∀ π : ℕ → ℝ,
      ((∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧ (∀ n, birth n * π n = death (n + 1) * π (n + 1))) ↔
        Summable θ ∧ ∀ n, π n = θ n / (∑' i, θ i)) ∧
    (∀ k, birth k = 0 → (∀ n, k < n → θ n = 0) ∧ Summable θ) := by
  intro θ
  have hθ_zero : θ 0 = 1 := Finset.prod_range_zero _
  have hθ_succ (n : ℕ) : θ (n + 1) = θ n * (birth n / death (n + 1)) :=
    Finset.prod_range_succ _ n
  have hθ_balance (n : ℕ) : birth n * θ n = death (n + 1) * θ (n + 1) := by
    rw [hθ_succ, mul_left_comm (death (n + 1)), ← mul_div_assoc,
      mul_div_cancel_left₀ _ (hdeath n).ne', mul_comm]
  refine ⟨?_, ?_⟩
  · intro π
    constructor
    · rintro ⟨_, hsum, hbalance⟩
      have hπ (n : ℕ) : π n = θ n * π 0 := by
        induction n with
        | zero => rw [hθ_zero, one_mul]
        | succ n ih =>
          apply mul_left_cancel₀ (hdeath n).ne'
          calc
            death (n + 1) * π (n + 1) = birth n * π n := (hbalance n).symm
            _ = (birth n * θ n) * π 0 := by rw [ih, mul_assoc]
            _ = death (n + 1) * (θ (n + 1) * π 0) := by rw [hθ_balance, mul_assoc]
      have hπ0 : π 0 ≠ 0 := by
        intro h
        have hzero : π = fun _ ↦ 0 := funext fun n ↦ by rw [hπ n, h, mul_zero]
        rw [hzero] at hsum
        exact one_ne_zero (hsum.unique hasSum_zero)
      have hθsum : HasSum θ (1 / π 0) := (hsum.div_const (π 0)).congr_fun fun n ↦ by
        rw [hπ n, mul_div_cancel_right₀ _ hπ0]
      refine ⟨hθsum.summable, fun n ↦ ?_⟩
      rw [hθsum.tsum_eq, div_div_eq_mul_div, div_one, ← hπ n]
    · rintro ⟨hθsum, hπ⟩
      have hθ_nonneg (n : ℕ) : 0 ≤ θ n :=
        Finset.prod_nonneg fun i _ ↦ div_nonneg (hbirth i) (hdeath i).le
      have hS : 0 < ∑' n, θ n := by
        have hle := hθsum.le_tsum 0 (fun n _ ↦ hθ_nonneg n)
        rw [hθ_zero] at hle
        exact zero_lt_one.trans_le hle
      refine ⟨fun n ↦ ?_, ?_, fun n ↦ ?_⟩
      · rw [hπ n]
        exact div_nonneg (hθ_nonneg n) hS.le
      · simpa only [div_self hS.ne'] using
          (hθsum.hasSum.div_const (∑' n, θ n)).congr_fun hπ
      · simp only [hπ, ← mul_div_assoc, hθ_balance]
  · intro k hk
    have htail (n : ℕ) (hn : k < n) : θ n = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by rw [hk, zero_div])
    refine ⟨htail, ?_⟩
    exact (hasSum_sum_of_ne_finset_zero (s := Finset.range (k + 1)) fun n hn ↦
      htail n (by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hn)).summable

end ProbabilityTheory
