/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.WolstenholmeBinomialExtension

/-!
# Block products for the Helou–Terjanian congruences

For a prime `p`, an offset `a : ℕ`, and `0 < k`, the block quotient formula compares
`((a + k) * p).choose (k * p)` with `(a + k).choose k`. Clearing its denominator gives a
natural-number identity between the two binomial coefficients multiplied by products of blocks.

## References

* Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS
  26 (2026), Article A32, pp. 1–28, Lemma 6.
* `MathlibExt.NumberTheory.HelouTerjanianLargePrime`: original location of the block product
  and the proof of its binomial identity.
-/

namespace MetaMathlibExt.HelouTerjanian

/-- The product of the integers strictly between `c * p` and `(c + 1) * p`. -/
public def blockProd (p c : ℕ) : ℕ :=
  ∏ r ∈ Finset.Ico 1 p, (c * p + r)

/-- The block product is the product of the shifted indices `c * p + r` for `1 ≤ r < p`. -/
public theorem blockProd_eq_prod (p c : ℕ) :
    blockProd p c = ∏ r ∈ Finset.Ico 1 p, (c * p + r) := by
  simp only [blockProd]

-- A block product is `(p - 1)!` times a binomial coefficient with lower index `p - 1`.
private theorem blockProd_eq (p c : ℕ) (hp : 0 < p) :
    blockProd p c = (p - 1).factorial * ((c + 1) * p - 1).choose (p - 1) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose (c * p) (p - 1)
  rw [Nat.ascFactorial_eq_prod_range,
    show c * p + (p - 1) = (c + 1) * p - 1 by rw [Nat.add_mul, one_mul]; omega] at h
  rw [← h, blockProd, Finset.prod_Ico_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ => by ring

/-- For a prime `p` and `0 < k`, the binomial coefficient with indices `((a + k) * p, k * p)`
times the product of the first `k` blocks equals `(a + k).choose k` times the product of those
blocks shifted by `a`. This is the block quotient formula with its denominator cleared. -/
public theorem choose_mul_prod_blockProd (p a k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ((a + k) * p).choose (k * p) * ∏ j ∈ Finset.range k, blockProd p j =
      (a + k).choose k * ∏ j ∈ Finset.range k, blockProd p (a + j) := by
  have h := (choose_mul_prime_eq_prod_div_prod p k (a + k) hp hk (Nat.le_add_left k a)).1
  simp only [Nat.add_sub_cancel] at h
  have hd : (∏ j ∈ Finset.range k, (((j + 1) * p - 1).choose (p - 1) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by
      have hle : p ≤ (j + 1) * p := Nat.le_mul_of_pos_left p (Nat.succ_pos j)
      exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hle 1)).ne'
  rw [eq_div_iff hd] at h
  have hnat : ((a + k) * p).choose (k * p) *
      ∏ j ∈ Finset.range k, ((j + 1) * p - 1).choose (p - 1) =
        (a + k).choose k * ∏ j ∈ Finset.range k, ((a + j + 1) * p - 1).choose (p - 1) := by
    exact_mod_cast h
  simp only [blockProd_eq p _ hp.pos, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range]
  rw [mul_left_comm, hnat, mul_left_comm]

end MetaMathlibExt.HelouTerjanian
