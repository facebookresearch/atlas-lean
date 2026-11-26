/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.NumberTheory.CotangentPowerSums
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.LinearCombination

/-!
# Cotangent power coefficients through even Bernoulli numbers

The main result is `cotangentPowerCoeff_eq_bernoulli_tuple_sum`: for `1 ≤ j ≤ r` with
`j ≡ r (mod 2)`, Girstmair's cotangent power coefficient `c_{r,j}` equals
`(-1)^{r+1} 2^{r-j} / (j-1)!` times the sum over `r`-tuples of even Bernoulli
numbers whose doubled indices sum to `r - j`.
-/

namespace MetaMathlibExt

@[expose] public section

namespace cotangentPowerCoeff_eq_bernoulli_tuple_sum

open PowerSeries Finset Finset.Nat

/-- The coefficient of the even Bernoulli power series: `B_{2n} / (2n)!`. -/
private noncomputable def evenBernoulliCoeff (n : ℕ) : ℚ :=
  bernoulli (2 * n) / ((2 * n).factorial : ℚ)

/-- The power series `∑ B_{2n} X^n / (2n)!`. -/
private noncomputable def evenBernoulliSeries : PowerSeries ℚ :=
  PowerSeries.mk evenBernoulliCoeff

/-- The even Bernoulli series with `X` replaced by `X^2`. -/
private noncomputable abbrev expandedEvenSeries : PowerSeries ℚ :=
  expand 2 (by norm_num : (2 : ℕ) ≠ 0) evenBernoulliSeries

/-- The sum over `r`-tuples of even Bernoulli coefficients whose indices sum to `m`,
as it appears in the statement of the main theorem. -/
private noncomputable def tupleSum (r m : ℕ) : ℚ :=
  ∑ a ∈ Finset.Nat.antidiagonalTuple r m,
    ∏ t, bernoulli (2 * a t) / ((2 * a t).factorial : ℚ)

/-- The differential equation for the Bernoulli power series, obtained by differentiating
`B * (exp - 1) = X`. -/
private theorem bernoulliPowerSeries_ode :
    X * (d⁄dX (bernoulliPowerSeries ℚ)) =
      bernoulliPowerSeries ℚ * (1 - X - bernoulliPowerSeries ℚ) := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one (A := ℚ)
  have key : d⁄dX (bernoulliPowerSeries ℚ) * (exp ℚ - 1) = 1 - X - bernoulliPowerSeries ℚ := by
    have h1 : d⁄dX (bernoulliPowerSeries ℚ * (exp ℚ - 1)) = 1 := by
      rw [hB]
      simp
    rw [Derivation.leibniz] at h1
    have h2 : d⁄dX (exp ℚ - 1 : ℚ⟦X⟧) = exp ℚ := by
      simp [derivative_exp]
    rw [h2] at h1
    have h3 : bernoulliPowerSeries ℚ * exp ℚ
        + (exp ℚ - 1) * d⁄dX (bernoulliPowerSeries ℚ) = 1 := by
      simpa [smul_eq_mul] using h1
    have h4 : bernoulliPowerSeries ℚ * exp ℚ = X + bernoulliPowerSeries ℚ := by
      calc bernoulliPowerSeries ℚ * exp ℚ
          = bernoulliPowerSeries ℚ * (exp ℚ - 1) + bernoulliPowerSeries ℚ := by ring
        _ = X + bernoulliPowerSeries ℚ := by rw [hB]
    rw [h4] at h3
    linear_combination h3
  calc X * d⁄dX (bernoulliPowerSeries ℚ)
      = (bernoulliPowerSeries ℚ * (exp ℚ - 1)) * d⁄dX (bernoulliPowerSeries ℚ) := by rw [hB]
    _ = bernoulliPowerSeries ℚ * ((exp ℚ - 1) * d⁄dX (bernoulliPowerSeries ℚ)) := by ring
    _ = bernoulliPowerSeries ℚ * (1 - X - bernoulliPowerSeries ℚ) := by
      rw [mul_comm (exp ℚ - 1) (d⁄dX (bernoulliPowerSeries ℚ)), key]

/-- The even Bernoulli series, expanded by a factor of two, is the Bernoulli power series
with its linear term removed. -/
private theorem expand_evenBernoulliSeries :
    expandedEvenSeries = bernoulliPowerSeries ℚ + C (1 / 2 : ℚ) * X := by
  change expand 2 (by norm_num : (2 : ℕ) ≠ 0) evenBernoulliSeries =
    bernoulliPowerSeries ℚ + C (1 / 2 : ℚ) * X
  ext n
  rw [coeff_expand]
  split_ifs with h2
  · obtain ⟨m, rfl⟩ := h2
    simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), evenBernoulliSeries,
      coeff_mk, evenBernoulliCoeff]
    by_cases hm : m = 0
    · subst hm
      simp [bernoulliPowerSeries]
    · have hne : 2 * m ≠ 1 := by omega
      simp [bernoulliPowerSeries, coeff_X, hne]
  · rcases Nat.even_or_odd n with hev | hodd
    · obtain ⟨k, hk⟩ := hev
      omega
    · by_cases hn1 : n = 1
      · subst hn1
        simp [bernoulliPowerSeries]
        norm_num
      · have hlt : 1 < n := by
          rcases hodd with ⟨k, hk⟩
          omega
        simp [bernoulliPowerSeries, bernoulli_eq_zero_of_odd hodd hlt, coeff_X, hn1]

/-- The differential equation for the even Bernoulli series: with `E` the expansion of the
even series, `X * E' = E - E^2 + X^2 / 4`. -/
private theorem evenBernoulliSeries_ode :
    X * d⁄dX expandedEvenSeries =
      expandedEvenSeries - expandedEvenSeries ^ 2 + C (1 / 4 : ℚ) * X ^ 2 := by
  rw [expand_evenBernoulliSeries]
  have hder : d⁄dX (bernoulliPowerSeries ℚ + C (1 / 2 : ℚ) * X) =
      d⁄dX (bernoulliPowerSeries ℚ) + C (1 / 2 : ℚ) := by
    simp
  rw [hder]
  have hC : (C (1 / 4 : ℚ) : ℚ⟦X⟧) = (C (1 / 2 : ℚ)) ^ 2 := by
    rw [← map_pow]
    norm_num
  rw [hC]
  have hhalf : (2 : ℚ⟦X⟧) * C (1 / 2 : ℚ) = 1 := by
    have h2 : (C (2 : ℚ) : ℚ⟦X⟧) = 2 := map_ofNat _ _
    rw [← h2, ← map_mul]
    norm_num
  linear_combination bernoulliPowerSeries_ode
    + X * bernoulliPowerSeries ℚ * hhalf

/-- The coefficient of a power of the even Bernoulli series is the corresponding
tuple sum. -/
private theorem coeff_pow_eq_tupleSum (r m : ℕ) :
    coeff m (evenBernoulliSeries ^ r) = tupleSum r m := by
  rw [PowerSeries.coeff_pow, tupleSum]
  refine sum_bij (fun f _ (i : Fin r) => f i) ?_ ?_ ?_ ?_
  · intro f hf
    exact mem_antidiagonalTuple.mpr
      ((Finset.sum_range f).symm.trans (mem_finsuppAntidiag.mp hf).1)
  · intro f hf g hg h
    ext i
    by_cases hi : i ∈ range r
    · exact congrFun h ⟨i, mem_range.mp hi⟩
    · rw [Finsupp.notMem_support_iff.mp (mt ((mem_finsuppAntidiag.mp hf).2 ·) hi),
        Finsupp.notMem_support_iff.mp (mt ((mem_finsuppAntidiag.mp hg).2 ·) hi)]
  · intro a ha
    let f := Finsupp.embDomain Fin.valEmbedding (Finsupp.equivFunOnFinite.symm a)
    have hf (i : Fin r) : f i = a i :=
      Finsupp.embDomain_apply_self Fin.valEmbedding _ i
    refine ⟨f, mem_finsuppAntidiag.mpr ⟨?_, ?_⟩, funext hf⟩
    · simpa only [Finset.sum_range, hf] using mem_antidiagonalTuple.mp ha
    · intro i hi
      obtain ⟨j, _, rfl⟩ := mem_map.mp hi
      exact mem_range.mpr j.isLt
  · intro f _
    simp only [Finset.prod_range, evenBernoulliSeries, coeff_mk, evenBernoulliCoeff]

/-- The coefficient of a power of the expanded series is the corresponding tuple sum. -/
private theorem coeff_expandedPow_eq_tupleSum (r m : ℕ) :
    coeff (2 * m) (expandedEvenSeries ^ r) = tupleSum r m := by
  have hpow : expandedEvenSeries ^ r =
      expand 2 (by norm_num : (2 : ℕ) ≠ 0) (evenBernoulliSeries ^ r) := by
    change (expand 2 (by norm_num : (2 : ℕ) ≠ 0) evenBernoulliSeries) ^ r = _
    rw [← map_pow]
  rw [hpow, coeff_expand_mul, coeff_pow_eq_tupleSum]

/-- The differential equation for a power of the expanded even Bernoulli series,
obtained from the equation for the series itself. -/
private theorem expandedEvenSeries_pow_deriv (r : ℕ) (hr : 1 ≤ r) :
    X * d⁄dX (expandedEvenSeries ^ r) =
      C (r : ℚ) * expandedEvenSeries ^ r - C (r : ℚ) * expandedEvenSeries ^ (r + 1)
        + C ((r : ℚ) / 4) * X ^ 2 * expandedEvenSeries ^ (r - 1) := by
  have hE1 : expandedEvenSeries ^ r = expandedEvenSeries ^ (r - 1) * expandedEvenSeries := by
    conv_lhs => rw [← Nat.sub_add_cancel hr]
    rw [pow_add, pow_one]
  have hE2 : expandedEvenSeries ^ (r + 1) =
      expandedEvenSeries ^ (r - 1) * expandedEvenSeries ^ 2 := by
    conv_lhs => rw [show r + 1 = (r - 1) + 2 by omega]
    rw [pow_add]
  have hC : (C ((r : ℚ) / 4) : ℚ⟦X⟧) = C (r : ℚ) * C (1 / 4 : ℚ) := by
    rw [show ((r : ℚ) / 4) = (r : ℚ) * (1 / 4) by ring, map_mul]
  rw [derivative_pow, ← map_natCast C r, hE1, hE2, hC]
  linear_combination
    (C (r : ℚ) * expandedEvenSeries ^ (r - 1)) * evenBernoulliSeries_ode

/-- The recurrence for tuple sums coming from the differential equation: for `r ≥ 1`
and `m ≥ 1`,
`r * D_{r+1,m} = (r - 2m) * D_{r,m} + (r/4) * D_{r-1,m-1}`. -/
private theorem tupleSum_recurrence (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (r : ℚ) * tupleSum (r + 1) m =
      ((r : ℚ) - 2 * m) * tupleSum r m + ((r : ℚ) / 4) * tupleSum (r - 1) (m - 1) := by
  have hcoeff := congrArg (fun F : PowerSeries ℚ => coeff (2 * m) F)
    (expandedEvenSeries_pow_deriv r hr)
  have hLHS : coeff (2 * m) (X * d⁄dX (expandedEvenSeries ^ r))
      = (2 * (m : ℚ)) * tupleSum r m := by
    have h1 : 2 * m = (2 * m - 1) + 1 := by omega
    have h2 : 2 * m - 1 + 1 = 2 * m := by omega
    rw [mul_comm (X : ℚ⟦X⟧) (d⁄dX (expandedEvenSeries ^ r)),
      ← pow_one (X : ℚ⟦X⟧), h1, coeff_mul_X_pow, coeff_derivative, h2,
      coeff_expandedPow_eq_tupleSum]
    rw [show ((2 * m - 1 : ℕ) : ℚ) + 1 = 2 * (m : ℚ) from by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
      push_cast
      ring]
    ring
  have hthird : coeff (2 * m) (C ((r : ℚ) / 4) * X ^ 2 * expandedEvenSeries ^ (r - 1))
      = ((r : ℚ) / 4) * tupleSum (r - 1) (m - 1) := by
    rw [mul_assoc, coeff_C_mul, show 2 * m = 2 * (m - 1) + 2 by omega, coeff_X_pow_mul,
      coeff_expandedPow_eq_tupleSum]
  have hRHS : coeff (2 * m)
      (C (r : ℚ) * expandedEvenSeries ^ r - C (r : ℚ) * expandedEvenSeries ^ (r + 1)
        + C ((r : ℚ) / 4) * X ^ 2 * expandedEvenSeries ^ (r - 1))
      = (r : ℚ) * tupleSum r m - (r : ℚ) * tupleSum (r + 1) m
        + ((r : ℚ) / 4) * tupleSum (r - 1) (m - 1) := by
    simp only [map_add, map_sub, coeff_C_mul, coeff_expandedPow_eq_tupleSum, hthird]
  rw [hLHS, hRHS] at hcoeff
  linear_combination hcoeff

/-- The defining sum for `cotangentPowerCoeff`, rewritten as a sum over `range (r + 1)`. -/
private noncomputable def definingSum (r j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (r + 1),
    (-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
      (Nat.stirlingFirst k j : ℚ)

/-- The defining sum with `k!` in place of `(k - 1)!`. -/
private noncomputable def weightedSum (r j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (r + 1),
    (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * (r.choose k : ℚ) *
      (Nat.stirlingFirst k j : ℚ)

/-- The coefficient is the sign times its defining sum. -/
private theorem cotangentPowerCoeff_eq_definingSum {r j : ℕ} :
    cotangentPowerCoeff r j = (-1 : ℚ) ^ (r - 1) * definingSum r j := by
  rw [cotangentPowerCoeff, definingSum]
  congr 1
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (by omega)
  · intro k hk hk2
    rw [Finset.mem_range] at hk
    have hkj : k < j := by
      by_contra h
      exact hk2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp [Nat.stirlingFirst_eq_zero_of_lt hkj]

/-- Extending a range sum by one, when the new term vanishes. -/
private theorem sum_range_extend (f : ℕ → ℚ) (n : ℕ) (h : f n = 0) :
    ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f k := by
  rw [Finset.sum_range_succ]
  simp [h]

/-- A binomial identity over the rationals used to compare the defining and weighted sums. -/
private theorem choose_key {r K : ℕ} (hr : 1 ≤ r) (hK : K ≤ r) :
    (r.choose K : ℚ) * ((r : ℚ) - K) = (r : ℚ) * ((r - 1).choose K : ℚ) := by
  have h := (Nat.choose_mul_succ_eq (r - 1) K).symm
  rw [Nat.sub_add_cancel hr, Nat.mul_comm _ r] at h
  simpa only [Nat.cast_mul, Nat.cast_sub hK] using congrArg (fun n : ℕ => (n : ℚ)) h

/-- The difference between the two factorial weights of a binomial term. -/
private theorem choose_diff {r k : ℕ} (hr : 1 ≤ r) (hk : k + 1 ≤ r) :
    (r.choose (k + 1) : ℚ) / ((k + 1).factorial : ℚ)
        - (r.choose (k + 1) : ℚ) / ((r : ℚ) * (k.factorial : ℚ))
      = ((r - 1).choose (k + 1) : ℚ) / ((k + 1).factorial : ℚ) := by
  have hrne : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hf1 : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hkey := choose_key hr hk
  simp only [Nat.cast_add, Nat.cast_one] at hkey
  rw [Nat.factorial_succ]
  field_simp
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  linear_combination (k.factorial : ℚ) * hkey

/-- Moving the factor `k` from a Stirling term into the factorial denominator. -/
private theorem term_factor (r k j : ℕ) :
    (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * (r.choose k : ℚ) *
        ((k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ))
      = -2 * ((-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) *
          (r.choose k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ)) := by
  cases k with
  | zero => simp [Nat.stirlingFirst]
  | succ k =>
    by_cases hkj : k + 1 < j + 1
    · simp [Nat.stirlingFirst_eq_zero_of_lt hkj]
    · have h1 : (k + 1) - (j + 1) = k - j := Nat.succ_sub_succ k j
      have h5 : (k + 1) - j = (k - j) + 1 := by omega
      rw [show (k + 1) - 1 = k from Nat.add_sub_cancel k 1, h1, h5, pow_succ,
        Nat.factorial_succ]
      field_simp
      push_cast
      ring

/-- Pascal's identity and the Stirling recurrence give the first step of the
diagonal recurrence for the defining sums. -/
private theorem definingSum_succ (r j : ℕ) :
    definingSum (r + 1) (j + 1) = -definingSum r (j + 1) + weightedSum r j := by
  have hextend : definingSum r (j + 1)
      = ∑ k ∈ Finset.range (r + 2),
          (-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
            (Nat.stirlingFirst k (j + 1) : ℚ) := by
    rw [definingSum]
    conv_rhs => rw [Finset.sum_range_succ]
    simp
  have hsplit : definingSum (r + 1) (j + 1)
      = (∑ k ∈ Finset.range (r + 2),
          (-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
            (Nat.stirlingFirst k (j + 1) : ℚ))
        + ∑ k ∈ Finset.range (r + 2),
          (-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) *
            (r.choose (k - 1) : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ) := by
    rw [definingSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    cases k with
    | zero => simp [Nat.stirlingFirst]
    | succ k =>
      have h1 : (k + 1) - (j + 1) = k - j := Nat.succ_sub_succ k j
      have h2 : (k + 1) - 1 = k := Nat.add_sub_cancel k 1
      rw [h1, h2, Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one, Nat.cast_add]
      ring
  rw [hsplit, ← hextend]
  have hsecond : (∑ k ∈ Finset.range (r + 2),
          (-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) *
            (r.choose (k - 1) : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ))
      = -2 * definingSum r (j + 1) + weightedSum r j := by
    rw [Finset.sum_range_succ']
    simp only [Nat.stirlingFirst, Nat.cast_zero, mul_zero, add_zero]
    have hterm : ∀ k ∈ Finset.range (r + 1),
        (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * (r.choose k : ℚ) *
            ((k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ))
          = -2 * ((-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) *
              (r.choose k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ)) := by
      intro k _
      exact term_factor r k j
    have hshift : (∑ k ∈ Finset.range (r + 1),
            (-2 : ℚ) ^ (k + 1 - (j + 1)) / ((k + 1 - 1).factorial : ℚ) *
              (r.choose (k + 1 - 1) : ℚ) *
              ((k * Nat.stirlingFirst k (j + 1) + Nat.stirlingFirst k j : ℕ) : ℚ))
        = ∑ k ∈ Finset.range (r + 1),
            (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * (r.choose k : ℚ) *
              ((k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ)) +
            ∑ k ∈ Finset.range (r + 1),
              (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * (r.choose k : ℚ) *
                (Nat.stirlingFirst k j : ℚ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : (k + 1) - (j + 1) = k - j := by omega
      have h2 : (k + 1) - 1 = k := by omega
      rw [h1, h2]
      cases k with
      | zero => simp [Nat.stirlingFirst]
      | succ k =>
        push_cast
        ring
    rw [hshift]
    have hfirst : (∑ k ∈ Finset.range (r + 1),
            (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * (r.choose k : ℚ) *
              ((k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ)))
        = -2 * definingSum r (j + 1) := by
      rw [definingSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k hk => hterm k hk
    rw [hfirst]
    rfl
  rw [hsecond]
  ring

/-- The weighted sum in terms of defining sums. -/
private theorem weightedSum_eq (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    weightedSum r j
      = definingSum r (j + 1) + definingSum (r - 1) (j + 1) + definingSum r j / r := by
  have hstep1 : weightedSum r j - definingSum r j / r
      = ∑ k ∈ Finset.range (r + 1),
          (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
            (Nat.stirlingFirst k j : ℚ) := by
    have hdiv : definingSum r j / (r : ℚ) = ∑ k ∈ Finset.range (r + 1),
        ((-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
          (Nat.stirlingFirst k j : ℚ)) * (r : ℚ)⁻¹ := by
      rw [definingSum, div_eq_mul_inv, Finset.sum_mul]
    rw [weightedSum, hdiv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    cases k with
    | zero =>
      rw [Nat.stirlingFirst_eq_zero_of_lt (show 0 < j by omega)]
      simp
    | succ k =>
      by_cases hkr : k + 1 ≤ r
      · have h1 : (k + 1) - 1 = k := Nat.add_sub_cancel k 1
        rw [h1]
        have hd := choose_diff hr hkr
        have hmul : (-2 : ℚ) ^ ((k + 1) - j) * (Nat.stirlingFirst (k + 1) j : ℚ) *
              ((r.choose (k + 1) : ℚ) / ((k + 1).factorial : ℚ)
                - (r.choose (k + 1) : ℚ) / ((r : ℚ) * (k.factorial : ℚ)))
            = (-2 : ℚ) ^ ((k + 1) - j) * (Nat.stirlingFirst (k + 1) j : ℚ) *
              (((r - 1).choose (k + 1) : ℚ) / ((k + 1).factorial : ℚ)) := by rw [hd]
        linear_combination hmul
      · have h1 : r.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have h2 : (r - 1).choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [h1, h2]
  have hstep2 : (∑ k ∈ Finset.range (r + 1),
          (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
            (Nat.stirlingFirst k j : ℚ))
      = definingSum r (j + 1) + definingSum (r - 1) (j + 1) := by
    have hU : (∑ k ∈ Finset.range (r + 1),
            (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
              (Nat.stirlingFirst k j : ℚ))
        = (∑ k ∈ Finset.range (r + 1),
            (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
              (Nat.stirlingFirst (k + 1) (j + 1) : ℚ))
          - ∑ k ∈ Finset.range (r + 1),
            (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
              ((k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hS : (Nat.stirlingFirst k j : ℚ)
          = (Nat.stirlingFirst (k + 1) (j + 1) : ℚ)
            - (k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ) := by
        rw [Nat.stirlingFirst_succ_succ]
        push_cast
        ring
      rw [hS]
      ring
    have hU2 : (∑ k ∈ Finset.range (r + 1),
            (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
              ((k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ)))
        = -2 * definingSum (r - 1) (j + 1) := by
      rw [definingSum, show r - 1 + 1 = r by omega, Finset.mul_sum, Finset.sum_range_succ]
      simp only [Nat.choose_eq_zero_of_lt (show r - 1 < r by omega), Nat.cast_zero,
        mul_zero, zero_mul, add_zero]
      exact Finset.sum_congr rfl fun k _ => term_factor (r - 1) k j
    have hU1 : (∑ k ∈ Finset.range (r + 1),
            (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
              (Nat.stirlingFirst (k + 1) (j + 1) : ℚ))
        = definingSum r (j + 1) - definingSum (r - 1) (j + 1) := by
      have hext : definingSum (r - 1) (j + 1)
          = ∑ k ∈ Finset.range (r + 1),
              (-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) *
                ((r - 1).choose k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ) := by
        rw [definingSum, show r - 1 + 1 = r by omega, Finset.sum_range_succ]
        simp [Nat.choose_eq_zero_of_lt (show r - 1 < r by omega)]
      have hdiff : (∑ k ∈ Finset.range (r + 1),
              (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
                (Nat.stirlingFirst (k + 1) (j + 1) : ℚ))
          = ∑ k ∈ Finset.range r,
              ((-2 : ℚ) ^ ((k + 1) - (j + 1)) / (((k + 1) - 1).factorial : ℚ) *
                  (r.choose (k + 1) : ℚ) * (Nat.stirlingFirst (k + 1) (j + 1) : ℚ)
                - (-2 : ℚ) ^ ((k + 1) - (j + 1)) / (((k + 1) - 1).factorial : ℚ) *
                  ((r - 1).choose (k + 1) : ℚ) *
                  (Nat.stirlingFirst (k + 1) (j + 1) : ℚ)) := by
        rw [sum_range_extend _ r (by
          simp [Nat.choose_eq_zero_of_lt (show r - 1 < r by omega)])]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (k + 1) - (j + 1) = k - j by omega, show (k + 1) - 1 = k by omega,
          show r = (r - 1) + 1 by omega, Nat.choose_succ_succ]
        push_cast
        ring
      have hdiff0 : (-2 : ℚ) ^ (0 - (j + 1)) / ((0 - 1).factorial : ℚ) *
            (r.choose 0 : ℚ) * (Nat.stirlingFirst 0 (j + 1) : ℚ)
          - (-2 : ℚ) ^ (0 - (j + 1)) / ((0 - 1).factorial : ℚ) *
            ((r - 1).choose 0 : ℚ) * (Nat.stirlingFirst 0 (j + 1) : ℚ) = 0 := by
        simp [Nat.stirlingFirst_zero_succ]
      calc (∑ k ∈ Finset.range (r + 1),
              (-2 : ℚ) ^ (k - j) / (k.factorial : ℚ) * ((r - 1).choose k : ℚ) *
                (Nat.stirlingFirst (k + 1) (j + 1) : ℚ))
          = ∑ k ∈ Finset.range r,
              ((-2 : ℚ) ^ ((k + 1) - (j + 1)) / (((k + 1) - 1).factorial : ℚ) *
                  (r.choose (k + 1) : ℚ) * (Nat.stirlingFirst (k + 1) (j + 1) : ℚ)
                - (-2 : ℚ) ^ ((k + 1) - (j + 1)) / (((k + 1) - 1).factorial : ℚ) *
                  ((r - 1).choose (k + 1) : ℚ) *
                  (Nat.stirlingFirst (k + 1) (j + 1) : ℚ)) := hdiff
        _ = ∑ k ∈ Finset.range (r + 1),
              ((-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) *
                  (r.choose k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ)
                - (-2 : ℚ) ^ (k - (j + 1)) / ((k - 1).factorial : ℚ) *
                  ((r - 1).choose k : ℚ) * (Nat.stirlingFirst k (j + 1) : ℚ)) := by
          rw [Finset.sum_range_succ', hdiff0, add_zero]
        _ = definingSum r (j + 1) - definingSum (r - 1) (j + 1) := by
          rw [Finset.sum_sub_distrib, definingSum, hext]
    rw [hU, hU1, hU2]
    ring
  linear_combination hstep1 + hstep2

/-- The diagonal recurrence for the coefficients, stepping `r` by one and `j` by one:
`c_{r+1,j+1} = c_{r-1,j+1} - c_{r,j} / r`. -/
private theorem cotangentPowerCoeff_step (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    cotangentPowerCoeff (r + 1) (j + 1)
      = cotangentPowerCoeff (r - 1) (j + 1) - cotangentPowerCoeff r j / r := by
  have hA := definingSum_succ r j
  have hT := weightedSum_eq r j hr hj
  have hA2 : definingSum (r + 1) (j + 1)
      = definingSum (r - 1) (j + 1) + definingSum r j / r := by
    linear_combination hA + hT
  have hsgnA : cotangentPowerCoeff (r + 1) (j + 1)
      = (-1 : ℚ) ^ r * definingSum (r + 1) (j + 1) := by
    rw [cotangentPowerCoeff_eq_definingSum]
    simp only [Nat.add_sub_cancel]
  have hsgnB : cotangentPowerCoeff r j = -(-1 : ℚ) ^ r * definingSum r j := by
    have hsgn : (-1 : ℚ) ^ (r - 1) = -(-1 : ℚ) ^ r := by
      have h := pow_succ (-1 : ℚ) (r - 1)
      rw [Nat.sub_add_cancel hr] at h
      linear_combination h
    rw [cotangentPowerCoeff_eq_definingSum, hsgn]
  have hsgnC : cotangentPowerCoeff (r - 1) (j + 1)
      = (-1 : ℚ) ^ r * definingSum (r - 1) (j + 1) := by
    by_cases hr1 : r = 1
    · subst hr1
      simp [cotangentPowerCoeff, definingSum, Nat.stirlingFirst]
    · have hsgn : (-1 : ℚ) ^ ((r - 1) - 1) = (-1 : ℚ) ^ r := by
        have h2 : (-1 : ℚ) ^ ((r - 1) - 1) * (-1 : ℚ) ^ 2 = (-1 : ℚ) ^ r := by
          rw [← pow_add]
          congr 1
          omega
        simpa using h2
      rw [cotangentPowerCoeff_eq_definingSum, hsgn]
  rw [hsgnA, hsgnB, hsgnC]
  linear_combination ((-1 : ℚ) ^ r) * hA2

/-- The right-hand side of the main theorem, as a function of `r` and `j`. -/
private noncomputable def rhsExpr (r j : ℕ) : ℚ :=
  (-1 : ℚ) ^ (r + 1) * 2 ^ (r - j) / ((j - 1).factorial : ℚ) *
    tupleSum r ((r - j) / 2)

/-- The diagonal recurrence for the right-hand side, following from the tuple-sum
recurrence. -/
private theorem rhs_step {r j m : ℕ} (hrm : r = j + 2 * m) (hj : 1 ≤ j) (hm : 1 ≤ m) :
    rhsExpr (r + 1) (j + 1) = rhsExpr (r - 1) (j + 1) - rhsExpr r j / r := by
  subst hrm
  have hrec := tupleSum_recurrence (j + 2 * m) m (by omega) hm
  have hi1 : (j + 2 * m + 1 - (j + 1)) / 2 = m := by omega
  have hi2 : (j + 2 * m - 1 - (j + 1)) / 2 = m - 1 := by omega
  have hi3 : (j + 2 * m - j) / 2 = m := by omega
  have hsign : ∀ k : ℕ, (-1 : ℚ) ^ (j + 2 * m + k) = (-1 : ℚ) ^ (j + k) := by
    intro k
    rw [show j + 2 * m + k = (j + k) + 2 * m by ring, pow_add]
    simp
  have hfac : (j.factorial : ℚ) = (j : ℚ) * ((j - 1).factorial : ℚ) := by
    conv_lhs => rw [← Nat.sub_add_cancel hj]
    rw [Nat.factorial_succ]
    push_cast
    rw [Nat.cast_sub hj]
    ring
  have hpow : (2 : ℚ) ^ (2 * m) = 4 * (2 : ℚ) ^ (2 * (m - 1)) := by
    rw [show 2 * m = 2 * (m - 1) + 2 by omega, pow_add]
    ring
  have hs2 : (-1 : ℚ) ^ (j + 2 * m - 1 + 1) = (-1 : ℚ) ^ j := by
    rw [show j + 2 * m - 1 + 1 = j + 2 * m by omega]
    exact hsign 0
  have hexp1 : j + 2 * m + 1 - (j + 1) = 2 * m := by omega
  have hexp2 : j + 2 * m - 1 - (j + 1) = 2 * (m - 1) := by omega
  have hexp3 : j + 2 * m - j = 2 * m := by omega
  rw [rhsExpr, rhsExpr, rhsExpr, hi1, hi2, hi3]
  simp only [Nat.add_sub_cancel]
  have hsj2 : (-1 : ℚ) ^ (j + 2) = (-1 : ℚ) ^ j := by
    rw [pow_add]
    simp
  have hsj1 : (-1 : ℚ) ^ (j + 1) = -(-1 : ℚ) ^ j := by
    rw [pow_add, pow_one]
    ring
  rw [hsign 2, hs2, hsign 1, hsj2, hsj1, hfac, hexp1, hexp2, hexp3, hpow]
  have hrne : ((j + 2 * m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : j + 2 * m ≠ 0)
  have hf1 : (((j - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hjne : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  field_simp
  push_cast at hrec ⊢
  linear_combination 4 * hrec

/-- The tuple sum on the first column at odd row: `D_{2m+1,m} = 4^{-m}`. -/
private theorem tupleSum_odd (m : ℕ) : tupleSum (2 * m + 1) m = (1 / 4 : ℚ) ^ m := by
  induction m with
  | zero => simp [tupleSum, antidiagonalTuple_zero_right]
  | succ m ih =>
    have hrec := tupleSum_recurrence (2 * m + 2) (m + 1) (by omega) (by omega)
    have hi : 2 * m + 2 + 1 = 2 * (m + 1) + 1 := by omega
    rw [hi] at hrec
    rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega, show m + 1 - 1 = m by omega] at hrec
    rw [ih] at hrec
    push_cast at hrec
    apply mul_left_cancel₀ (show (2 : ℚ) * m + 2 ≠ 0 by positivity)
    rw [pow_succ]
    linear_combination hrec

/-- The right-hand side equals `1` in the first column at odd row. -/
private theorem rhsExpr_one_of_odd {r : ℕ} (hr : Odd r) :
    rhsExpr r 1 = 1 := by
  obtain ⟨m, rfl⟩ := hr
  have hi : (2 * m + 1 - 1) / 2 = m := by omega
  rw [rhsExpr, hi, tupleSum_odd]
  have hsign : (-1 : ℚ) ^ (2 * m + 1 + 1) = 1 := by
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    norm_num
  have hpow : (2 : ℚ) ^ (2 * m + 1 - 1) = 4 ^ m := by
    rw [show 2 * m + 1 - 1 = 2 * m by omega, pow_mul]
    norm_num
  rw [hsign, hpow]
  simp

/-- The coefficient equals `1` in the first column at odd row. -/
private theorem coeff_one_of_odd {r : ℕ} (hr : Odd r) :
    cotangentPowerCoeff r 1 = 1 := by
  have hbin : ∑ k ∈ Finset.range (r + 1), (r.choose k : ℚ) * (-2 : ℚ) ^ k = (-1 : ℚ) ^ r := by
    have h := add_pow (-2 : ℚ) (1 : ℚ) r
    rw [show (-2 : ℚ) + 1 = -1 by norm_num] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
    ring
  have hshift : ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℚ) * (-2 : ℚ) ^ k = 1 := by
    have h2 := Finset.sum_range_succ' (fun k => (r.choose k : ℚ) * (-2 : ℚ) ^ k) r
    rw [hbin] at h2
    have hodd : (-1 : ℚ) ^ r = -1 := hr.neg_one_pow
    rw [hodd] at h2
    have hmul : (∑ k ∈ Finset.range r, (r.choose (k + 1) : ℚ) * (-2 : ℚ) ^ (k + 1))
        = -2 * ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℚ) * (-2 : ℚ) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ]
      ring
    rw [hmul] at h2
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h2
    linear_combination (1 / 2 : ℚ) * h2
  rw [cotangentPowerCoeff_eq_definingSum, definingSum]
  rw [Finset.sum_range_succ']
  have h0 : (-2 : ℚ) ^ (0 - 1) / ((0 - 1).factorial : ℚ) * (r.choose 0 : ℚ) *
      (Nat.stirlingFirst 0 1 : ℚ) = 0 := by
    simp [Nat.stirlingFirst]
  rw [h0, add_zero]
  have hterm : ∀ k ∈ Finset.range r,
      (-2 : ℚ) ^ (k + 1 - 1) / ((k + 1 - 1).factorial : ℚ) * (r.choose (k + 1) : ℚ) *
          (Nat.stirlingFirst (k + 1) 1 : ℚ)
        = (r.choose (k + 1) : ℚ) * (-2 : ℚ) ^ k := by
    intro k _
    rw [Nat.stirlingFirst_one_right, show k + 1 - 1 = k by omega]
    have hfac : ((k.factorial : ℚ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  rw [Finset.sum_congr rfl hterm, hshift]
  have hsgn : (-1 : ℚ) ^ (r - 1) = 1 := by
    rcases hr with ⟨m, hm⟩
    rw [hm, show 2 * m + 1 - 1 = 2 * m by omega]
    exact Even.neg_one_pow ⟨m, by omega⟩
  rw [hsgn, one_mul]

/-- The diagonal case: both sides equal `(-1)^{r-1} / (r-1)!`. -/
private theorem diag (r : ℕ) (hr : 1 ≤ r) :
    cotangentPowerCoeff r r = rhsExpr r r := by
  have hsum : definingSum r r = 1 / ((r - 1).factorial : ℚ) := by
    rw [definingSum]
    rw [Finset.sum_eq_single r]
    · simp [Nat.stirlingFirst_self]
    · intro k hk hkr
      have hlt : k < r := by
        rw [Finset.mem_range] at hk
        omega
      simp [Nat.stirlingFirst_eq_zero_of_lt hlt]
    · simp
  have htup : tupleSum r 0 = 1 := by
    simp [tupleSum, antidiagonalTuple_zero_right]
  rw [cotangentPowerCoeff_eq_definingSum, hsum, rhsExpr]
  have hi : (r - r) / 2 = 0 := by omega
  have hsgn : (-1 : ℚ) ^ (r + 1) = (-1 : ℚ) ^ (r - 1) := by
    rw [show r + 1 = (r - 1) + 2 by omega, pow_add]
    simp
  rw [hi, htup, hsgn]
  simp only [Nat.sub_self, pow_zero, mul_one]
  rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]

/-- The main identity, proved by two-step induction on `r` using the diagonal
recurrences for both sides. -/
private theorem main_aux (r j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) (hpar : j % 2 = r % 2) :
    cotangentPowerCoeff r j = rhsExpr r j := by
  induction r using Nat.twoStepInduction generalizing j with
  | zero =>
    omega
  | one =>
    have hj1 : j = 1 := by omega
    subst hj1
    rw [cotangentPowerCoeff_one_one]
    have htup : tupleSum 1 0 = 1 := by
      simp [tupleSum, antidiagonalTuple_zero_right]
    rw [rhsExpr]
    simp [htup]
  | more r ih0 ih1 =>
    by_cases hj1 : j = 1
    · subst hj1
      have hodd : Odd (r + 2) := by
        rw [Nat.odd_iff]
        omega
      rw [coeff_one_of_odd hodd, rhsExpr_one_of_odd hodd]
    · by_cases hdiag : j = r + 2
      · subst hdiag
        exact diag (r + 2) (by omega)
      · have hj2 : 2 ≤ j := by omega
        have hjr' : j ≤ r := by
          by_contra h
          omega
        have hC : cotangentPowerCoeff (r + 2) j = cotangentPowerCoeff r j
            - cotangentPowerCoeff (r + 1) (j - 1) / ((r + 1 : ℕ) : ℚ) := by
          have h := cotangentPowerCoeff_step (r + 1) (j - 1) (by omega) (by omega)
          rwa [show r + 1 + 1 = r + 2 by omega, show j - 1 + 1 = j by omega,
            show r + 1 - 1 = r by omega] at h
        obtain ⟨m, hm_eq, hm_pos⟩ :
            ∃ m, r + 1 = (j - 1) + 2 * m ∧ 1 ≤ m :=
          ⟨(r + 2 - j) / 2, by omega, by omega⟩
        have hR : rhsExpr (r + 2) j
            = rhsExpr r j - rhsExpr (r + 1) (j - 1) / ((r + 1 : ℕ) : ℚ) := by
          have h := rhs_step hm_eq (by omega) hm_pos
          rwa [show r + 1 + 1 = r + 2 by omega, show j - 1 + 1 = j by omega,
            show r + 1 - 1 = r by omega] at h
        have ih0' : cotangentPowerCoeff r j = rhsExpr r j :=
          ih0 j hj hjr' (by omega)
        have ih1' : cotangentPowerCoeff (r + 1) (j - 1) = rhsExpr (r + 1) (j - 1) :=
          ih1 (j - 1) (by omega) (by omega) (by omega)
        rw [hC, hR, ih0', ih1']

end cotangentPowerCoeff_eq_bernoulli_tuple_sum

/-- **Cotangent power coefficients through even Bernoulli numbers.** Let $c_{r,j}$ be
Girstmair's cotangent power coefficients and $B_m$ the $m$-th Bernoulli number. For natural
numbers $j$ and $r$ with $1 \le j \le r$ and $j \equiv r \pmod 2$,
$$c_{r,j} = \frac{(-1)^{r+1} 2^{r-j}}{(j-1)!} \, d_{r,j},$$
where
$$d_{r,j} = \sum_{(j_1, \dots, j_r)} \prod_{t=1}^{r} \frac{B_{2 j_t}}{(2 j_t)!}$$
and the sum runs over all $r$-tuples $(j_1, \dots, j_r)$ of natural numbers with
$j + 2 j_1 + \dots + 2 j_r = r$. This is Theorem 2 of the source, relating $c_{r,j}$ to the
coefficients $d_{r,j}$ of the earlier literature (Equations (13) and (15)).

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Theorem 2 with Equations (13) and (15) (`integers-2025-A63-thm-2`). -/
public theorem cotangentPowerCoeff_eq_bernoulli_tuple_sum {r j : ℕ} (hj : 1 ≤ j)
    (hjr : j ≤ r) (hpar : j % 2 = r % 2) :
    cotangentPowerCoeff r j =
      (-1) ^ (r + 1) * 2 ^ (r - j) / ((j - 1).factorial : ℚ) *
        ∑ a ∈ Finset.Nat.antidiagonalTuple r ((r - j) / 2),
          ∏ t, bernoulli (2 * a t) / ((2 * a t).factorial : ℚ) := by
  change cotangentPowerCoeff r j =
    cotangentPowerCoeff_eq_bernoulli_tuple_sum.rhsExpr r j
  exact cotangentPowerCoeff_eq_bernoulli_tuple_sum.main_aux r j hj hjr hpar

end

end MetaMathlibExt
