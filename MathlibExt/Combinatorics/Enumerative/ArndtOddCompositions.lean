/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ArndtNegativeEven
import MathlibExt.Combinatorics.Enumerative.KArndtTotalGFNonneg
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Arndt compositions and compositions into odd parts

The two counts agree in every weight. If `P` is the generating function for one odd part,
the generating function for Arndt compositions is the geometric series in `P`.
-/

namespace MetaMathlibExt

namespace kArndtTotalCount_zero_eq_odd_compositions

open PowerSeries Finset

private noncomputable def oddParts : PowerSeries ℤ :=
  mk fun d => if Odd d then 1 else 0

-- The coefficient of the m-th power counts ordered m-tuples of odd parts.
private lemma coeff_oddParts_pow (n m : ℕ) :
    coeff n (oddParts ^ m) = (((Nat.antidiagonalTuple m n).filter fun c =>
      ∀ i, Odd (c i)).card : ℤ) := by
  rw [← show (∏ _ : Fin m, oddParts) = oddParts ^ m by simp, coeff_prod]
  have htuples : (finsuppAntidiag (univ : Finset (Fin m)) n).map
      Finsupp.equivFunOnFinite.toEmbedding = Nat.antidiagonalTuple m n := by
    ext c
    simp [mem_map_equiv, Nat.mem_antidiagonalTuple]
  simp [oddParts, Finset.prod_boole, ← htuples, filter_map]

-- P = X + X³ + X⁵ + ⋯, so (1 - X²)P = X.
private lemma oddParts_mul : oddParts * (1 - X ^ 2) = X := by
  ext n
  simp only [mul_sub, mul_one, map_sub, coeff_mul_X_pow', oddParts, coeff_mk, coeff_X, Nat.odd_iff]
  split_ifs <;> omega

end kArndtTotalCount_zero_eq_odd_compositions

open PowerSeries Finset kArndtTotalCount_zero_eq_odd_compositions in
/-- **Arndt compositions and compositions into odd parts are equinumerous.** For every natural
number $n$, the number $a(n, 0)$ of Arndt compositions of $n$ (compositions $(c_1, \dots, c_m)$
of $n$ with $c_{2i-1} > c_{2i}$ whenever $2i \le m$) equals the number $c^0_o(n)$ of compositions
of $n$ into odd parts. This includes $n = 0$, where both counts are $1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 1 (`integers-2026-A64-thm-1`). -/
public theorem kArndtTotalCount_zero_eq_odd_compositions (n : ℕ) :
    kArndtTotalCount 0 n = oddOrSmallEvenCompositionCount 0 n := by
  let A : PowerSeries ℤ := mk fun d => (kArndtTotalCount 0 d : ℤ)
  have hA : A * (1 - X - X ^ 2) = 1 - X ^ 2 := by
    simpa [A, kArndtTotalCount] using kArndtComposition_total_gf_nonneg 0
  have hgeom : A * (1 - oddParts) = 1 := by
    have hne : (1 - X ^ 2 : PowerSeries ℤ) ≠ 0 := by
      intro h
      simpa using congrArg constantCoeff h
    apply mul_right_cancel₀ hne
    rw [mul_assoc, sub_mul, one_mul, oddParts_mul, sub_right_comm, hA]
  -- The geometric sum through length n already gives the full coefficient at weight n.
  have hsum : A - A * oddParts ^ (n + 1) = ∑ m ∈ range (n + 1), oddParts ^ m := by
    rw [← mul_one_sub, ← geom_sum_mul_neg, mul_left_comm, hgeom, mul_one]
  have hdiv : (X : PowerSeries ℤ) ∣ oddParts := by
    simp [X_dvd_iff, oddParts, constantCoeff_mk]
  have htail := X_pow_dvd_iff.mp ((pow_dvd_pow_of_dvd hdiv (n + 1)).mul_left A) n (by omega)
  have h := congrArg (coeff (R := ℤ) n) hsum
  have allowed (d : ℕ) : (0 < d ∧ (Odd d ∨ d ≤ 2 * 0)) ↔ Odd d := by
    rw [Nat.odd_iff]
    omega
  apply Int.ofNat_inj.mp
  simpa only [map_sub, htail, sub_zero, A, coeff_mk, map_sum, coeff_oddParts_pow,
    oddOrSmallEvenCompositionCount, Nat.cast_sum, allowed] using h

end MetaMathlibExt
