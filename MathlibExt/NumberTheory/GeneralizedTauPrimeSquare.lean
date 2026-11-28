/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
public import MathlibExt.NumberTheory.GeneralizedTau
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Generalized tau at a prime square plus one

The coefficient `τ_{p²+1}(n+1)` modulo `p` is a signed count of representations of `n`
as a pentagonal number plus `p²` times a pentagonal number.
-/

namespace MetaMathlibExt

open PowerSeries
open scoped Finset

namespace generalizedTau_prime_sq_add_one_succ_modEq

private theorem mem_interval {r : ℤ} {n : ℕ} (h : pentagonal r ≤ n) :
    r ∈ Finset.Icc (-(n : ℤ)) n := by
  have hformula := two_mul_natCast_pentagonal r
  have hle : (pentagonal r : ℤ) ≤ n := by exact_mod_cast h
  rw [Finset.mem_Icc]
  constructor <;> nlinarith

/-- Reindex the coefficient convolution by the two pentagonal indices. -/
private theorem coeff_pentagonal_mul_expand (d : ℕ) (hd : 0 < d) (n : ℕ) :
    coeff n (pentagonalSeries ℤ * expand d hd.ne' (pentagonalSeries ℤ)) =
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
        if n = pentagonal r + d * pentagonal s then ((r + s).negOnePow : ℤ) else 0 := by
  rw [coeff_mul, ← Finset.sum_product', ← Finset.sum_filter]
  symm
  apply Finset.sum_of_injOn (fun (x : ℤ × ℤ) => (pentagonal x.1, d * pentagonal x.2))
  · intro x _ y _ h
    exact Prod.ext (pentagonal_injective (congrArg Prod.fst h))
      (pentagonal_injective (Nat.eq_of_mul_eq_mul_left hd (congrArg Prod.snd h)))
  · intro x hx
    exact Finset.mem_antidiagonal.mpr (Finset.mem_filter.mp hx).2.symm
  · -- Every nonzero summand comes from a pair of pentagonal indices in the interval.
    rintro ⟨i, j⟩ hij hout
    by_contra h
    obtain ⟨hi, hj⟩ := mul_ne_zero_iff.mp h
    obtain ⟨r, rfl⟩ : i ∈ Set.range pentagonal := by
      by_contra hn
      exact hi (coeff_pentagonalSeries_eq_zero ℤ hn)
    obtain ⟨k, rfl⟩ : d ∣ j := by
      by_contra hn
      exact hj (coeff_expand_of_not_dvd d hd.ne' _ hn)
    rw [coeff_expand_mul] at hj
    obtain ⟨s, rfl⟩ : k ∈ Set.range pentagonal := by
      by_contra hn
      exact hj (coeff_pentagonalSeries_eq_zero ℤ hn)
    have hsum : pentagonal r + d * pentagonal s = n := Finset.mem_antidiagonal.mp hij
    have hs := Nat.le_mul_of_pos_left (pentagonal s) hd
    exact hout ⟨(r, s), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨mem_interval (r := r) (by omega),
        mem_interval (r := s) (by omega)⟩, hsum.symm⟩, rfl⟩
  · intro x _
    simp only [coeff_expand_mul, coeff_pentagonalSeries_pentagonal, Int.cast_id,
      Int.negOnePow_add, Units.val_mul]

end generalizedTau_prime_sq_add_one_succ_modEq

open generalizedTau_prime_sq_add_one_succ_modEq

/-- **Generalized tau at $p^2 + 1$ modulo $p$.** Let $p$ be an odd prime and $n$ a natural number,
and for an integer $j$ let $P(j) = j(3j - 1)/2$ be the generalized pentagonal number. Then
$\tau_{p^2 + 1}(n + 1)$ is congruent modulo $p$ to the sum of $(-1)^{r + s}$ over the pairs of
integers $(r, s)$ with $-n \le r, s \le n$ and $n = P(r) + p^2 P(s)$.

The record prints the condition as $n + 1 = P(r) + p^2 P(s)$; that is false, and the proof's
identity $\sum \tau_{p^2+1}(n + 1) q^n \equiv \prod (1 - q^m)(1 - q^{p^2 m}) \pmod{p}$ gives the
index $n$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Theorem 18 (`integers-2024-A39-thm-18`). -/
public theorem generalizedTau_prime_sq_add_one_succ_modEq (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (n : ℕ) :
    generalizedTau (p ^ 2 + 1) (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
        if n = pentagonal r + p ^ 2 * pentagonal s then ((r + s).negOnePow : ℤ) else 0
      [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have hd : 0 < p ^ 2 := pow_pos hodd.pos _
  rw [show (p : ℤ) ^ 2 + 1 = ((p ^ 2 + 1 : ℕ) : ℤ) by simp,
    generalizedTau_natCast, coeff_succ_X_mul, ← coeff_pentagonal_mul_expand _ hd,
    ← ZMod.intCast_eq_intCast_iff]
  change Int.castRingHom (ZMod p) _ = Int.castRingHom (ZMod p) _
  rw [← coeff_map, ← coeff_map]
  apply congrArg (coeff n)
  -- Over the prime field, Frobenius squared dilates all degrees by p².
  rw [pow_succ', map_mul, map_mul, map_expand, map_pow,
    ← map_iterateFrobenius_expand p hp.ne_zero _ 2,
    RingHom.ext_zmod (iterateFrobenius (ZMod p) p 2) (RingHom.id _), map_id, id_eq]

end MetaMathlibExt
