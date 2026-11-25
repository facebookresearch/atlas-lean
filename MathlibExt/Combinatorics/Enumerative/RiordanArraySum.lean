/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Fundamental theorem of Riordan arrays

The row with entries `[tⁿ] d(t) h(t)ᵏ` acts on the coefficients of `f` by extracting
the coefficient of degree `n` from `d(t) f(h(t))`.
-/

open PowerSeries Finset.HasAntidiagonal

namespace MetaMathlibExt

/-- **Fundamental theorem of Riordan arrays.** Write $[t^m]F$ for the coefficient of $t^m$ in a
power series $F$. Let $R$ be a commutative ring and let $d$, $h$, $f$ be power series over
$R$ with $h(0) = 0$. Then for every $n \in \mathbb{N}$,

$$\sum_{k=0}^{n} \left([t^n]\,d(t)\,h(t)^k\right) [t^k]\,f = [t^n]\,d(t)\,f(h(t)).$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 1 (`jis-2025-25.3.5-thm-1`). -/
public theorem riordan_array_sum_eq_coeff_subst {R : Type*} [CommRing R]
    (d h f : PowerSeries R) (hh : constantCoeff h = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), coeff n (d * h ^ k) * coeff k f = coeff n (d * f.subst h) := by
  have hcoeff (j : ℕ) (hj : j ≤ n) :
      coeff j (f.subst h) = ∑ k ∈ Finset.range (n + 1), coeff k f * coeff j (h ^ k) := by
    rw [coeff_subst' (.of_constantCoeff_zero' hh)]
    simp only [smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hkn
    have hjk : j < k := lt_of_le_of_lt hj (by simpa using hkn)
    have hz := coeff_of_lt_order j <| (ENat.natCast_lt_natCast.mpr hjk).trans_le
      (le_order_pow_of_constantCoeff_eq_zero k hh)
    exact hk (by simp [hz])
  simp_rw [coeff_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [hcoeff p.2 (antidiagonal.snd_le hp), Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ac_rfl

end MetaMathlibExt
