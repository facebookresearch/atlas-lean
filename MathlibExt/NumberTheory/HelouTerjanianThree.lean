/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.PadicValNat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Ring
import all MathlibExt.NumberTheory.HelouTerjanianLargePrime

/-!
# The Helou–Terjanian congruence at three

For natural numbers `0 < m < n`, the difference between `choose (3 * n) (3 * m)` and
`choose n m` is divisible by `3 ^ (2 + max (ν₃ m) (ν₃ (n - m)) + ν₃ (choose n m))`, where `ν₃`
is the 3-adic valuation. The remaining cases of the source's range `0 ≤ m ≤ n` have both
binomial coefficients equal to `1`.

## Proof idea

The product of the two terms in the `j`-th block not divisible by three is
`(3 * j + 1) * (3 * j + 2) = 2 + 9 * j * (j + 1)`. Shifting the block by `a` changes its product
by `9 * a * (2 * j + a + 1)`. The block product identity then gives the congruence with
`ν₃ (n - m)` in the exponent, and binomial symmetry gives the bound with the maximum.

## References

* Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer Sequences
  27 (2024), Article 24.3.3, pp. 1–25, Lemma 26 (2).
* Charles Helou and Guy Terjanian, *On Wolstenholme's theorem and its converse*, Journal of Number
  Theory 128 (2008), pp. 475–499, Corollary on p. 490 (the result cited by Zhang).
* Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS
  26 (2026), Article A32, pp. 1–28, Lemma 6 (the quotient formula for the block products).
* `MathlibExt.NumberTheory.HelouTerjanianLargePrime`: the proof reuses `blockProd` and
  `choose_mul_prod_blockProd` and specializes the congruence argument of `choose_mul_modEq_add`
  and `choose_mul_prime_modEq_of_five_le` to the two factors at three.
-/

namespace MetaMathlibExt

open choose_mul_prime_modEq_of_five_le (blockProd choose_mul_prod_blockProd)

private theorem blockProd_three_eq (j : ℕ) : blockProd 3 j = 2 + 3 ^ 2 * j * (j + 1) := by
  norm_num [blockProd, Finset.prod_Ico_eq_prod_range, Finset.prod_range_succ]
  ring

-- First use only the valuation of the complementary index `a`.
private theorem choose_three_mul_modEq_add (a k : ℕ) (hk : 0 < k) :
    (3 * (a + k)).choose (3 * k) ≡ (a + k).choose k
      [MOD 3 ^ (2 + padicValNat 3 a + padicValNat 3 ((a + k).choose k))] := by
  have shift (j : ℕ) : blockProd 3 (a + j) = blockProd 3 j + 3 ^ 2 * a * (2 * j + a + 1) := by
    simp only [blockProd_three_eq]
    ring
  have hprod : (∏ j ∈ Finset.range k, blockProd 3 (a + j)) ≡
      (∏ j ∈ Finset.range k, blockProd 3 j) [MOD 3 ^ (2 + padicValNat 3 a)] := by
    refine Nat.ModEq.prod fun j _ => ?_
    rw [shift, Nat.add_modEq_left_iff, pow_add, mul_assoc, Nat.padicValNat_def]
    exact mul_dvd_mul_left _ ((pow_multiplicity_dvd 3 a).trans (dvd_mul_right a _))
  have hcop : Nat.Coprime 3 (∏ j ∈ Finset.range k, blockProd 3 j) := by
    refine Nat.Coprime.prod_right fun j _ => ?_
    rw [blockProd_three_eq, show (3 : ℕ) ^ 2 * j * (j + 1) = 3 * (3 * j * (j + 1)) by ring,
      Nat.coprime_add_mul_left_right]
    decide
  have hblocks := choose_mul_prod_blockProd 3 a k Nat.prime_three hk
  rw [Nat.mul_comm (a + k) 3, Nat.mul_comm k 3] at hblocks
  apply Nat.ModEq.cancel_right_of_coprime (hcop.pow_left _)
  rw [hblocks]
  -- The valuation of the unscaled binomial coefficient gives the remaining power of three.
  refine (hprod.mul_left' _).of_dvd ?_
  rw [pow_add, mul_comm, Nat.padicValNat_def (n := (a + k).choose k)]
  exact mul_dvd_mul_right (pow_multiplicity_dvd 3 _) _

/-- **Helou–Terjanian congruence for $p = 3$.** Let $m$ and $n$ be integers with $0 < m < n$.
Then $\binom{3n}{3m} \equiv \binom{n}{m} \pmod{3^e}$, where
$e = 2 + \max(\nu_3(m), \nu_3(n - m)) + \nu_3\big(\binom{n}{m}\big)$ and $\nu_3$ is the $3$-adic
valuation.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 26 (2) (`jis-2024-24.3.3-lem-26`). -/
public theorem choose_three_mul_modEq (n m : ℕ) (hm : 0 < m) (hmn : m < n) :
    (3 * n).choose (3 * m) ≡ n.choose m
      [MOD 3 ^ (2 + max (padicValNat 3 m) (padicValNat 3 (n - m)) +
        padicValNat 3 (n.choose m))] := by
  rcases le_total (padicValNat 3 m) (padicValNat 3 (n - m)) with h | h
  · rw [max_eq_right h]
    simpa only [Nat.sub_add_cancel hmn.le] using choose_three_mul_modEq_add (n - m) m hm
  · rw [max_eq_left h]
    have hchoose := Nat.choose_symm hmn.le
    have htriple : (3 * n).choose (3 * (n - m)) = (3 * n).choose (3 * m) := by
      rw [Nat.mul_sub, Nat.choose_symm (Nat.mul_le_mul_left 3 hmn.le)]
    simpa only [Nat.add_sub_of_le hmn.le, hchoose, htriple] using
      choose_three_mul_modEq_add m (n - m) (Nat.sub_pos_of_lt hmn)

end MetaMathlibExt
