/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HyperLeonardo
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehavior
import MathlibExt.NumberTheory.HyperLeonardoHyperFibonacci
import MathlibExt.NumberTheory.HyperLeonardoLogConvex

/-!
# Eventual log-concavity of the hyper-Leonardo numbers

The hyper-Leonardo numbers are log-concave at every index `n ≥ 2` for every order `r ≥ 1`.
Order one is the partial-sum sequence of the ordinary Leonardo numbers, so Zhao's partial-sum
inequality gives the base case. For the order step, log-concavity at index one starts an induction
on the index using the consecutive-order recurrence, without applying the paper's convolution
lemma to a sequence that is only eventually log-concave.

## References

* Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
  *A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, pp. 1–18,
  Definition 1 and Propositions 3, 6, 12, 13, and 14 (with the order-zero exception below).
* Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the Generalized Leonardo
  Numbers*, INTEGERS 24 (2024), Article A82, pp. 1–9, Theorem 2, for the order-one base case
  at indices `n ≥ 2`.
-/

namespace MetaMathlibExt

private theorem hyperLeonardo_pos (r : ℕ) : ∀ n, 0 < hyperLeonardo r n := by
  induction r with
  | zero =>
    intro n
    rw [hyperLeonardo_eq_hyperFibonacci, hyperFibonacci_zero, Nat.choose_zero_right, Nat.cast_one]
    have h : (0 : ℤ) < Nat.fib (n + 1) := by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
    omega
  | succ r ih =>
    intro n
    rw [hyperLeonardo_succ]
    exact Finset.sum_pos (fun k _ => ih k) ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩

-- The next order is log-concave from index one, even when the preceding order starts at two.
private theorem hyperLeonardo_logConcave_succ (r : ℕ) (hr : 1 ≤ r)
    (h : ∀ n, hyperLeonardo r (n + 1) * hyperLeonardo r (n + 3) ≤
      hyperLeonardo r (n + 2) ^ 2) (n : ℕ) :
    hyperLeonardo (r + 1) n * hyperLeonardo (r + 1) (n + 2) ≤
      hyperLeonardo (r + 1) (n + 1) ^ 2 := by
  let x := hyperLeonardo r
  let S := hyperLeonardo (r + 1)
  have hstep (i : ℕ) : S (i + 1) = S i + x (i + 1) := hyperLeonardo_succ_succ r i
  have gap (i : ℕ) : S (i + 1) ^ 2 - S i * S (i + 2) =
      S (i + 1) * x (i + 1) - S i * x (i + 2) := by
    rw [hstep (i + 1)]
    linear_combination S (i + 1) * hstep i
  have cross (i : ℕ) : S i * x (i + 2) ≤ S (i + 1) * x (i + 1) := by
    induction i with
    | zero =>
      apply sub_nonneg.mp
      rw [← gap]
      exact sub_nonneg.mpr (hyperLeonardo_logConvex_logConcave_one.2 (r + 1) (by omega))
    | succ i ih =>
      -- Compare the next lower-order ratio to the preceding partial-sum ratio by cross products.
      have hcross : S i * x (i + 3) ≤ S (i + 1) * x (i + 2) := by
        apply le_of_mul_le_mul_right ?_ (hyperLeonardo_pos r (i + 2))
        calc
          (S i * x (i + 3)) * x (i + 2) = (S i * x (i + 2)) * x (i + 3) := by ring
          _ ≤ (S (i + 1) * x (i + 1)) * x (i + 3) :=
            mul_le_mul_of_nonneg_right ih (hyperLeonardo_pos r (i + 3)).le
          _ = S (i + 1) * (x (i + 1) * x (i + 3)) := by ring
          _ ≤ S (i + 1) * x (i + 2) ^ 2 :=
            mul_le_mul_of_nonneg_left (h i) (hyperLeonardo_pos (r + 1) (i + 1)).le
          _ = (S (i + 1) * x (i + 2)) * x (i + 2) := by ring
      calc
        S (i + 1) * x (i + 3) = S i * x (i + 3) + x (i + 1) * x (i + 3) := by
          rw [hstep i, add_mul]
        _ ≤ S (i + 1) * x (i + 2) + x (i + 2) ^ 2 := add_le_add hcross (h i)
        _ = S (i + 2) * x (i + 2) := by rw [hstep (i + 1), add_mul, pow_two]
  exact sub_nonneg.mp (by rw [gap]; exact sub_nonneg.mpr (cross n))

/-- **Eventual log-concavity of the hyper-Leonardo numbers of positive order.** For all natural
numbers $r \ge 1$ and $n \ge 2$, the hyper-Leonardo numbers $Le^{(r)}_n$ of order $r$ satisfy
$Le^{(r)}_{n-1} Le^{(r)}_{n+1} \le (Le^{(r)}_n)^2$.

The source states this for $r \ge 0$, but it fails for the Leonardo numbers $Le_n = Le^{(0)}_n$
at $n = 3$, where $Le_2 Le_4 = 27 > 25 = Le_3^2$; the source's proof starts its induction at
$r = 1$ (Proposition 13).

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 14
(`integers-2026-A48-prop-14`). -/
public theorem hyperLeonardo_logConcave {r : ℕ} (hr : 1 ≤ r) {n : ℕ} (hn : 2 ≤ n) :
    hyperLeonardo r (n - 1) * hyperLeonardo r (n + 1) ≤ hyperLeonardo r n ^ 2 := by
  obtain ⟨r, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  clear hr
  induction r generalizing n with
  | zero =>
    simp only [hyperLeonardo_succ, hyperLeonardo_zero, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    exact genLeonardo_partialSum_logConcave 1 le_rfl n hn
  | succ r ih =>
    obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    refine hyperLeonardo_logConcave_succ (r + 1) (by omega) (fun j => ?_) i
    simpa only [Nat.add_sub_cancel] using ih (n := j + 1 + 1) (by omega)

end MetaMathlibExt
