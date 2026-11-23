/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Binomial coefficients at prime multiples

The ATLAS wiki attributes these two product formulas to Walid Kehila,
*An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026).
-/

namespace MetaMathlibExt

/-- Count successive choices of blocks of size `p`, with `d * p` elements left over. -/
private theorem choose_blocks_eq_quotient (d m p : ℕ) :
    (((d + m) * p).choose (m * p) : ℚ) =
      (∏ j ∈ Finset.range m, (((d + j + 1) * p).choose p : ℚ)) /
        ∏ j ∈ Finset.range m, (((j + 1) * p).choose p : ℚ) := by
  apply (eq_div_iff ?_).2
  · norm_cast
    induction m with
    | zero => simp
    | succ m ih =>
      have step : ((d + m + 1) * p).choose ((m + 1) * p) * ((m + 1) * p).choose p =
          ((d + m + 1) * p).choose p * ((d + m) * p).choose (m * p) := by
        simpa [Nat.succ_mul] using
          (Nat.choose_mul (n := (d + m + 1) * p) (k := (m + 1) * p) (s := p)
            (by simp [Nat.succ_mul]))
      simp only [Finset.prod_range_succ]
      rw [← Nat.add_assoc, mul_left_comm, step, ← ih]
      ac_rfl
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast Nat.choose_ne_zero (show p ≤ (j + 1) * p by simp [Nat.succ_mul])

/-- For prime `p` and `1 ≤ m ≤ n`, the binomial coefficient at `(n * p, m * p)` is a
quotient of products of binomial coefficients with lower index `p - 1` or `p`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 6
(`integers-2026-A32-lem-6`). -/
public theorem choose_mul_prime_eq_prod_div_prod (p m n : ℕ) (hp : p.Prime) (_hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ((n * p).choose (m * p) : ℚ) =
        (n.choose m : ℚ) * (∏ j ∈ Finset.range m, (((n - m + j + 1) * p - 1).choose (p - 1) : ℚ)) /
          ∏ j ∈ Finset.range m, (((j + 1) * p - 1).choose (p - 1) : ℚ) ∧
      ((n * p).choose (m * p) : ℚ) =
        (∏ j ∈ Finset.range m, (((n - m + j + 1) * p).choose p : ℚ)) /
          ∏ j ∈ Finset.range m, (((j + 1) * p).choose p : ℚ) := by
  have block (q : ℕ) := choose_blocks_eq_quotient (n - m) m q
  simp only [Nat.sub_add_cancel hmn] at block
  refine ⟨(block p).trans ?_, block p⟩
  -- The case of blocks of size one collects the linear factors into `n.choose m`.
  have linearFactors := block 1
  simp only [Nat.mul_one, Nat.choose_one_right] at linearFactors
  simp_rw [Nat.choose_mul_right hp.ne_zero, Nat.cast_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_div_mul_comm, ← linearFactors,
    mul_div_assoc]

end MetaMathlibExt
