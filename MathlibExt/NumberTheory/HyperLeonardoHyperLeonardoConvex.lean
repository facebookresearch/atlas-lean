/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HyperLeonardo
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Convexity of the hyper-Leonardo numbers

The hyper-Leonardo numbers are convex in the index `n`: `hyperLeonardo_convex` states that
`2 * hyperLeonardo r n ≤ hyperLeonardo r (n - 1) + hyperLeonardo r (n + 1)` for all natural
numbers `r` and `n ≥ 1`.

Statements from Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
*A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The Leonardo numbers at index `n + 2` unfold by their recurrence. -/
private theorem genLeonardo_one_add_two (n : ℕ) :
    genLeonardo 1 (n + 2) = genLeonardo 1 (n + 1) + genLeonardo 1 n + 1 := rfl

/-- The Leonardo numbers are nonnegative. -/
private theorem genLeonardo_one_nonneg : ∀ n : ℕ, 0 ≤ genLeonardo 1 n
  | 0 => by simp [genLeonardo]
  | 1 => by simp [genLeonardo]
  | n + 2 => by
    have h0 := genLeonardo_one_nonneg n
    have h1 := genLeonardo_one_nonneg (n + 1)
    have e := genLeonardo_one_add_two n
    omega

/-- The Leonardo numbers are monotone. -/
private theorem genLeonardo_one_mono : ∀ n : ℕ, genLeonardo 1 n ≤ genLeonardo 1 (n + 1)
  | 0 => by simp [genLeonardo]
  | n + 1 => by
    have h := genLeonardo_one_nonneg n
    have e : genLeonardo 1 (n + 1 + 1) = genLeonardo 1 (n + 1) + genLeonardo 1 n + 1 :=
      genLeonardo_one_add_two n
    omega

/-- Each Leonardo number is at most twice the previous one plus one. -/
private theorem genLeonardo_one_succ_le (m : ℕ) :
    genLeonardo 1 (m + 1) ≤ 2 * genLeonardo 1 m + 1 := by
  cases m with
  | zero => simp [genLeonardo]
  | succ m =>
    have h := genLeonardo_one_mono m
    have e : genLeonardo 1 (m + 1 + 1) = genLeonardo 1 (m + 1) + genLeonardo 1 m + 1 :=
      genLeonardo_one_add_two m
    omega

/-- The Leonardo numbers are convex in the index. -/
private theorem genLeonardo_one_convex (m : ℕ) :
    2 * genLeonardo 1 (m + 1) ≤ genLeonardo 1 m + genLeonardo 1 (m + 2) := by
  have h := genLeonardo_one_succ_le m
  have e := genLeonardo_one_add_two m
  omega

/-- The hyper-Leonardo numbers are nonnegative. -/
private theorem hyperLeonardo_nonneg : ∀ r n : ℕ, 0 ≤ hyperLeonardo r n
  | 0, n => genLeonardo_one_nonneg n
  | r + 1, n => by
    rw [hyperLeonardo_succ]
    exact Finset.sum_nonneg (fun k _ => hyperLeonardo_nonneg r k)

/-- Consecutive hyper-Leonardo numbers differ by one lower-order term. -/
private theorem hyperLeonardo_step (r n : ℕ) :
    hyperLeonardo (r + 1) (n + 1) = hyperLeonardo (r + 1) n + hyperLeonardo r (n + 1) := by
  rw [hyperLeonardo_succ r (n + 1), hyperLeonardo_succ r n, Finset.sum_range_succ _ (n + 1)]

/-- The hyper-Leonardo numbers are monotone in the index. -/
private theorem hyperLeonardo_mono (r n : ℕ) :
    hyperLeonardo r n ≤ hyperLeonardo r (n + 1) := by
  cases r with
  | zero => exact genLeonardo_one_mono n
  | succ r =>
    have h := hyperLeonardo_nonneg r (n + 1)
    have e := hyperLeonardo_step r n
    omega

/-- **Convexity of the hyper-Leonardo numbers.** For all natural numbers $r$ and $n \ge 1$, the
hyper-Leonardo numbers $\mathrm{Le}^{(r)}_n$ satisfy
$2 \mathrm{Le}^{(r)}_n \le \mathrm{Le}^{(r)}_{n-1} + \mathrm{Le}^{(r)}_{n+1}$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Theorem 3, with the definition
of convexity displayed before it (`integers-2026-A48-thm-3`). -/
public theorem hyperLeonardo_convex (r n : ℕ) (hn : 1 ≤ n) :
    2 * hyperLeonardo r n ≤ hyperLeonardo r (n - 1) + hyperLeonardo r (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  cases r with
  | zero =>
    simp only [hyperLeonardo_zero]
    exact genLeonardo_one_convex m
  | succ r =>
    have e1 := hyperLeonardo_step r m
    have e2 := hyperLeonardo_step r (m + 1)
    have h := hyperLeonardo_mono r (m + 1)
    omega

end

end MetaMathlibExt
