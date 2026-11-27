/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst
public import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKind
import all MathlibExt.NumberTheory.BernoulliSecondKindBernoulliSecondEqNegSum
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Bernoulli numbers of the second kind as a signed Stirling sum

We substitute the formal logarithm into the shifted exponential series and read off its
coefficients using the signed Stirling numbers of the first kind.

## References

* Bakir Farhi, *Formulas Involving Bernoulli and Stirling Numbers of Both Kinds*,
  Journal of Integer Sequences 28 (2025), Article 25.2.6, pp. 1–16, Proposition 11.
* Steven M. Roman and Gian-Carlo Rota, *The umbral calculus*, Advances in Mathematics
  27 (1978), pp. 95–188, §9, p. 145. Farhi credits them with the Stirling sum.
* Steven Roman, *The Umbral Calculus*, Academic Press, 1984, §3.2, pp. 113–114,
  for the normalization of the Bernoulli numbers of the second kind.
-/

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

open PowerSeries MetaMathlibExt

-- The shifted exponential composed with the logarithm is the second-kind generating function.
private theorem subst_exp_shift_log :
    (mk fun k : ℕ => (1 : ℚ) / (k + 1).factorial).subst (log ℚ) =
      bernoulliSecondPowerSeries := by
  have hlog : log ℚ = X * mk fun k : ℕ => (-1 : ℚ) ^ k / (k + 1) := by
    simpa [pow_succ, Nat.cast_add] using sub_const_eq_X_mul_shift (log ℚ)
  have hexp : exp ℚ - 1 = X * mk fun k : ℕ => (1 : ℚ) / (k + 1).factorial := by
    simpa [coeff_exp] using sub_const_eq_X_mul_shift (exp ℚ)
  have hne : log ℚ ≠ 0 := by
    intro h
    have hc := congrArg (coeff 1) h
    norm_num at hc
  apply mul_left_cancel₀ hne
  calc
    log ℚ * (mk fun k : ℕ => (1 : ℚ) / (k + 1).factorial).subst (log ℚ) =
        (exp ℚ - 1).subst (log ℚ) := by
      rw [hexp, subst_mul HasSubst.log, subst_X HasSubst.log]
    _ = X := by
      rw [subst_sub HasSubst.log, subst_exp_log, ← coe_substAlgHom HasSubst.log, map_one]
      simp
    _ = log ℚ * bernoulliSecondPowerSeries := by
      rw [hlog, mul_assoc, mul_comm (mk _) bernoulliSecondPowerSeries,
        bernoulliSecondPowerSeries_mul_mk, mul_one]

/-- **Bernoulli numbers of the second kind via Stirling numbers of the first kind.** Let $B_m^*$
be the Bernoulli numbers of the second kind and $s(m, j)$ the signed Stirling numbers of the
first kind. For every natural number $n$,
$$B_n^* = \sum_{i=0}^{n} \frac{s(n, i)}{i+1}.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Proposition 11. -/
public theorem bernoulliSecond_eq_sum (n : ℕ) :
    MetaMathlibExt.bernoulliSecond n =
      ∑ i ∈ Finset.range (n + 1),
        (MetaMathlibExt.signedStirlingFirst n i : ℚ) / (i + 1) := by
  rw [bernoulliSecond_eq, ← subst_exp_shift_log, coeff_subst' HasSubst.log]
  simp only [coeff_mk, smul_eq_mul, coeff_log_pow]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    have hk' : n < k := by omega
    exact hk (by simp [signedStirlingFirst_eq_zero_of_lt hk'])

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
