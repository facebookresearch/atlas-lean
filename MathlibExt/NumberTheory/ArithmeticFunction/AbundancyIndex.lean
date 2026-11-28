/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The abundancy index of natural numbers

The abundancy index of a positive natural number is at least one. It is multiplicative on
coprime pairs and on finite families of pairwise coprime factors. At a prime power, the index
is given by a geometric sum, yielding a formula for the change between consecutive powers.

## References

* The prime-power proofs adapt arguments from `MathlibExt.NumberTheory.PrimitiveNondeficient`
  and `MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndexDiv`, respectively the
  geometric formula `abundancyIndex_prime_pow_eq` and `abundancyIndex_prime_pow_succ`.
* Coprime multiplicativity adapts the private `abundancyIndex_mul_of_coprime` from
  `MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndexDiv`.
-/

open scoped Function

public section

namespace Nat

/-- The abundancy index of a positive natural number is at least one. -/
lemma one_le_abundancyIndex {n : ℕ} (hn : 0 < n) : 1 ≤ n.abundancyIndex := by
  calc
    1 = (1 : ℕ).abundancyIndex := by simp [abundancyIndex]
    _ ≤ n.abundancyIndex := abundancyIndex_le_of_dvd hn.ne' (one_dvd n)

/-- The abundancy index is multiplicative on coprime pairs. -/
lemma abundancyIndex_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    (m * n).abundancyIndex = m.abundancyIndex * n.abundancyIndex := by
  simp only [abundancyIndex, h.sum_divisors_mul, Nat.cast_mul, mul_div_mul_comm]

/-- The abundancy index of a product of pairwise coprime factors is the product of their indices. -/
lemma abundancyIndex_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : (s : Set ι).Pairwise (Nat.Coprime on f)) :
    (∏ i ∈ s, f i).abundancyIndex = ∏ i ∈ s, (f i).abundancyIndex := by
  simp only [abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_prod f s h, Nat.cast_prod,
    Finset.prod_div_distrib]

/-- For a prime `p`, the abundancy index of `p ^ a` is `p / (p - 1)` times `1 - 1 / p ^ (a + 1)`,
with the divisions taken in `ℚ`. -/
lemma abundancyIndex_prime_pow_eq (p a : ℕ) (hp : p.Prime) :
    (p ^ a).abundancyIndex = (p : ℚ) / ((p : ℚ) - 1) * (1 - 1 / (p : ℚ) ^ (a + 1)) := by
  have hgeom : ((∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) : ℚ) * ((p : ℚ) - 1)
      = (p : ℚ) ^ (a + 1) - 1 := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using geom_sum_mul (p : ℚ) (a + 1)
  have hdiv : (p ^ a).abundancyIndex
      = ((∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) : ℚ) / (p : ℚ) ^ a := by
    simp only [abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.cast_pow]
  rw [hdiv]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
    linarith
  have hpa : (p : ℚ) ^ a ≠ 0 := pow_ne_zero _ hp0
  have hpa1 : (p : ℚ) ^ (a + 1) ≠ 0 := pow_ne_zero _ hp0
  have hps : (p : ℚ) ^ (a + 1) = (p : ℚ) * (p : ℚ) ^ a := _root_.pow_succ' _ _
  field_simp
  linear_combination (p : ℚ) ^ (a + 1) * hgeom + ((p : ℚ) ^ (a + 1) - 1) * hps

/-- For prime `p`, the abundancy of `p ^ (k + 1)` exceeds that of `p ^ k` by `1 / p ^ (k + 1)`. -/
lemma abundancyIndex_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ (k + 1)).abundancyIndex = (p ^ k).abundancyIndex + 1 / (p : ℚ) ^ (k + 1) := by
  simp only [abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.cast_pow]
  rw [geom_sum_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_div, _root_.pow_succ']
  rw [mul_div_mul_left _ _ (by exact_mod_cast hp.ne_zero : (p : ℚ) ≠ 0)]

end Nat
