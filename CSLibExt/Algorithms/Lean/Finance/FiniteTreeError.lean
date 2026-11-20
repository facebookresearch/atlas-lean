/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.ODE.DiscreteGronwall
public import MathlibExt.Economics.Finance.BinomialOptimalStopping

/-!
# Backward-induction error bound on a finite binomial tree

Let `E` follow the exact Snell update for an exercise payoff `g` on
`List Bool` histories, with up probability `p ∈ [0, 1]` and discount factor
`disc > 0` (the reciprocal of a positive gross return), and let `V` start
from the same terminal values while each computed backward update deviates
from the exact update by at most `ε ≥ 0`. Then after `N` steps the computed
and exact values differ by at most `ε * ∑ j ∈ Finset.range N, disc ^ j` at
every node (`finite_tree_error_bound`). The corollary
`snell_computed_abs_le` instantiates the exact recursion to the native
`MathlibExt.Economics.Finance.BinomialOptimalStopping.snell` envelope.

The proof is the concrete one-step Lipschitz estimate for the tree update,
a pointwise error-sequence induction (no supremum over histories), and
Mathlib's `discrete_gronwall_prod_general`. No floating-point, CRR-rate, or
continuous-time limit claim is made.

## References

* S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset
  Pricing Model*, Springer (2004), Chapter 4.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Finance.FiniteTreeError

/-- Error-sequence majorant: `e 0 = 0`, `e (k+1) = disc * e k + ε`. -/
private noncomputable def err (disc ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => disc * err disc ε n + ε

private theorem err_zero (disc ε : ℝ) : err disc ε 0 = 0 := rfl

private theorem err_succ (disc ε : ℝ) (n : ℕ) :
    err disc ε (n + 1) = disc * err disc ε n + ε := rfl

/-- `max` with a common left argument is 1-Lipschitz in the other argument. -/
private theorem abs_max_left_le (g x y : ℝ) :
    |max g x - max g y| ≤ |x - y| := by
  rw [max_comm g x, max_comm g y]
  exact abs_max_sub_max_le_abs x y g

/-- A convex combination with weights `p`, `1 - p` is 1-Lipschitz in max norm. -/
private theorem abs_convex_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a b a' b' : ℝ) :
    |p * a + (1 - p) * b - (p * a' + (1 - p) * b')|
      ≤ max |a - a'| |b - b'| := by
  have hEq : p * a + (1 - p) * b - (p * a' + (1 - p) * b')
      = p * (a - a') + (1 - p) * (b - b') := by ring
  rw [hEq]
  have h1p : 0 ≤ 1 - p := by linarith
  have g1 : p * |a - a'| ≤ p * max |a - a'| |b - b'| :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hp0
  have g2 : (1 - p) * |b - b'| ≤ (1 - p) * max |a - a'| |b - b'| :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) h1p
  calc |p * (a - a') + (1 - p) * (b - b')|
        ≤ |p * (a - a')| + |(1 - p) * (b - b')| := abs_add_le _ _
      _ = p * |a - a'| + (1 - p) * |b - b'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg h1p]
      _ ≤ p * max |a - a'| |b - b'|
          + (1 - p) * max |a - a'| |b - b'| := by linarith
      _ = max |a - a'| |b - b'| := by ring

/-- One-step estimate: the exact Snell update is `disc`-Lipschitz in max norm. -/
private theorem onestep_le (p disc : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hdisc : 0 < disc) (g a b a' b' : ℝ) :
    |max g (disc * (p * a + (1 - p) * b))
      - max g (disc * (p * a' + (1 - p) * b'))|
      ≤ disc * max |a - a'| |b - b'| := by
  calc |max g (disc * (p * a + (1 - p) * b))
          - max g (disc * (p * a' + (1 - p) * b'))|
        ≤ |disc * (p * a + (1 - p) * b)
          - disc * (p * a' + (1 - p) * b')| := abs_max_left_le _ _ _
      _ = disc * |p * a + (1 - p) * b - (p * a' + (1 - p) * b')| := by
          rw [← mul_sub, abs_mul, abs_of_pos hdisc]
      _ ≤ disc * max |a - a'| |b - b'| :=
          mul_le_mul_of_nonneg_left (abs_convex_le p hp0 hp1 _ _ _ _) hdisc.le

/-- The error sequence bounds the pointwise error at every node. -/
private theorem pointwise_le (p disc ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hdisc : 0 < disc) (_hε : 0 ≤ ε) (g : List Bool → ℝ)
    (E V : ℕ → List Bool → ℝ) (hE0 : E 0 = g)
    (hEsucc : ∀ k s, E (k + 1) s =
      max (g s) (disc * (p * E k (true :: s) + (1 - p) * E k (false :: s))))
    (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (disc * (p * V k (true :: s) + (1 - p) * V k (false :: s)))| ≤ ε)
    (k : ℕ) (s : List Bool) : |E k s - V k s| ≤ err disc ε k := by
  induction k generalizing s with
  | zero =>
      have hE := congrFun hE0 s
      have hV := congrFun hV0 s
      simp [err_zero, hE, hV]
  | succ k ih =>
      rw [err_succ]
      have hE := hEsucc k s
      have hV := hVerr k s
      set U : ℝ :=
        max (g s) (disc * (p * V k (true :: s) + (1 - p) * V k (false :: s)))
        with hU
      have hsplit : E (k + 1) s - V (k + 1) s
          = (E (k + 1) s - U) + (U - V (k + 1) s) := by ring
      have htri : |E (k + 1) s - V (k + 1) s|
          ≤ |E (k + 1) s - U| + |U - V (k + 1) s| := by
        rw [hsplit]
        exact abs_add_le _ _
      have hexact : |E (k + 1) s - U| ≤ disc * err disc ε k := by
        rw [hE, hU]
        have h1 := onestep_le p disc hp0 hp1 hdisc (g s)
          (E k (true :: s)) (E k (false :: s))
          (V k (true :: s)) (V k (false :: s))
        have hmax : max |E k (true :: s) - V k (true :: s)|
            |E k (false :: s) - V k (false :: s)| ≤ err disc ε k :=
          max_le_iff.mpr ⟨ih _, ih _⟩
        exact le_trans h1 (mul_le_mul_of_nonneg_left hmax hdisc.le)
      have hres : |U - V (k + 1) s| ≤ ε := by
        rw [abs_sub_comm]
        exact hV
      linarith

/-- Backward-induction error bound on a finite binomial tree.

Let `E` follow the exact Snell update for exercise payoff `g` with up
probability `p ∈ [0, 1]` and discount factor `disc > 0`, and let `V` start
from the same terminal values while each backward update deviates from the
exact update by at most `ε ≥ 0`. Then after `N` steps the values differ by at
most `ε * ∑ j ∈ Finset.range N, disc ^ j` at every node. -/
theorem finite_tree_error_bound (p disc ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hdisc : 0 < disc) (hε : 0 ≤ ε) (g : List Bool → ℝ)
    (E V : ℕ → List Bool → ℝ) (hE0 : E 0 = g)
    (hEsucc : ∀ k s, E (k + 1) s =
      max (g s) (disc * (p * E k (true :: s) + (1 - p) * E k (false :: s))))
    (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (disc * (p * V k (true :: s) + (1 - p) * V k (false :: s)))| ≤ ε)
    (N : ℕ) (s : List Bool) :
    |E N s - V N s| ≤ ε * ∑ j ∈ Finset.range N, disc ^ j := by
  have hu : ∀ n ≥ 0, err disc ε (n + 1) ≤ disc * err disc ε n + ε := by
    intro n _
    exact le_of_eq (err_succ disc ε n)
  have hc : ∀ n ≥ 0, 0 ≤ disc := fun n _ => hdisc.le
  have hgr := discrete_gronwall_prod_general (u := err disc ε)
    (c := fun _ => disc) (b := fun _ => ε) (n₀ := 0) (n := N) hu hc
    (Nat.zero_le N)
  rw [err_zero, zero_mul, zero_add] at hgr
  simp only [Finset.prod_const, Nat.card_Ico] at hgr
  rw [← Finset.range_eq_Ico] at hgr
  have hsum : (∑ k ∈ Finset.range N, ε * disc ^ (N - (k + 1)))
      = ε * ∑ j ∈ Finset.range N, disc ^ j := by
    calc (∑ k ∈ Finset.range N, ε * disc ^ (N - (k + 1)))
          = ∑ k ∈ Finset.range N, ε * disc ^ (N - 1 - k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_range] at hk
            have hkk : N - (k + 1) = N - 1 - k := by omega
            rw [hkk]
        _ = ε * ∑ k ∈ Finset.range N, disc ^ (N - 1 - k) :=
            (Finset.mul_sum _ _ _).symm
        _ = ε * ∑ j ∈ Finset.range N, disc ^ j := by
            have hrefl : (∑ k ∈ Finset.range N, disc ^ (N - 1 - k))
                = ∑ j ∈ Finset.range N, disc ^ j :=
              Finset.sum_range_reflect (fun j => disc ^ j) N
            rw [hrefl]
  calc |E N s - V N s| ≤ err disc ε N :=
        pointwise_le p disc ε hp0 hp1 hdisc hε g E V hE0 hEsucc hV0 hVerr N s
      _ ≤ ε * ∑ j ∈ Finset.range N, disc ^ j := by
          rw [← hsum]
          exact hgr

/-- The error bound instantiated to the native Snell envelope: any computed
recursion `V` with exact terminal values and per-update deviation at most
`ε` from the exact update stays within `ε * ∑ j ∈ Finset.range N, disc ^ j`
of `snell p disc g` after `N` steps, at every node and in particular at
the root. -/
theorem snell_computed_abs_le (p disc ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hdisc : 0 < disc) (hε : 0 ≤ ε) (g : List Bool → ℝ)
    (V : ℕ → List Bool → ℝ) (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (disc * (p * V k (true :: s) + (1 - p) * V k (false :: s)))| ≤ ε)
    (N : ℕ) (s : List Bool) :
    |MathlibExt.Economics.Finance.BinomialOptimalStopping.snell p disc g N s
      - V N s| ≤ ε * ∑ j ∈ Finset.range N, disc ^ j :=
  finite_tree_error_bound p disc ε hp0 hp1 hdisc hε g
    (MathlibExt.Economics.Finance.BinomialOptimalStopping.snell p disc g) V
    (funext fun _ => rfl) (fun _ _ => rfl) hV0 hVerr N s

end Cslib.Algorithms.Lean.Finance.FiniteTreeError
