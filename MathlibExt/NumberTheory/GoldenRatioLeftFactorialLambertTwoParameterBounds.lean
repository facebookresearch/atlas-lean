/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Analysis.SpecialFunctions.LambertWFunction
public import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralGoldenFactorialExponentBounds
import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds

/-!
# Two-parameter Lambert bounds for the left factorial

For natural numbers `n ≥ 5` and `m ≥ 1`, let `A ≥ n - 1` be the real number satisfying
`lambertMap (-A / (n - 1)) = -(1 / (n - 1)) * (4 / (7 * m)) ^ (1 / (n - 1))`, with
real division and exponentiation. The left factorial minus Kurepa's partial integral at `A`
is strictly between `0` and `1 / m`. The proof compares the remainder, scaled by `m`,
term by term with the remainder at the one-parameter cutoff.

## References

* Aleksandar Petojević, Marjana Gorjanac Ranitović, Dragan Rastovac, and Milinko Mandić,
  *The Golden Ratio, Factorials, and the Lambert W Function*, Journal of Integer Sequences
  27 (2024), Article 24.5.7, pp. 1–11, Theorems 10 and 14 (Sections 3.1 and 3.3).
* Đ. Kurepa, *On the left factorial function !n*, Mathematica Balkanica 1 (1971), pp. 147–153,
  especially p. 151 for the integral representation.
* The proof reuses `kurepaPartialIntegral_lambertSequence_bounds` from the `MathlibExt.NumberTheory`
  module `GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds`, and
  `sum_factorial_sub_kurepaPartialIntegral` and `kurepaPartialIntegral_lt_sum_factorial` from
  `GoldenRatioLeftFactorialLambertKurepaPartialIntegralGoldenFactorialExponentBounds`.
  It uses `exists_lambertSequence`, `lambertCutoff_pow_mul_exp`, and `lambertMap_strictAntiOn_Iic`
  from `MathlibExt.Analysis.SpecialFunctions.LambertWFunction`.
-/

namespace MetaMathlibExt

open Real

/-- **Two-parameter Lambert bounds for the left factorial.** Let $n \ge 5$ and $m \ge 1$ be
integers, let $!n = \sum_{k=0}^{n-1} k!$ be the left factorial, let
$K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt$ be Kurepa's partial integral, let
$h(y) = y e^y$ be the Lambert map, and let $A$ be a real number with $A \ge n - 1$ and
$$h\left(-\frac{A}{n-1}\right) = -\frac{1}{n-1}\left(\frac{4}{7m}\right)^{1/(n-1)}.$$
Then $K_n(A) < {!n} < K_n(A) + \frac{1}{m}$.

The two conditions on $A$ say exactly that
$A = -(n-1)\, W_{-1}\left(-\frac{1}{n-1}\left(\frac{4}{7m}\right)^{1/(n-1)}\right)$, where $W_{-1}$
is the lower real branch of the Lambert $W$ function; this is the paper's $A(n, m)$, and
$K_n(A)$ is its $B(n, m)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 14 (`jis-2024-24.5.7-thm-14`). -/
public theorem kurepaPartialIntegral_lambertSequence_two_bounds (n m : ℕ)
    (hn : 5 ≤ n) (hm : 1 ≤ m) (A : ℝ) (hA : (n : ℝ) - 1 ≤ A)
    (hW : lambertMap (-A / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / (7 * m) : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    kurepaPartialIntegral n A < ∑ k ∈ Finset.range n, (k.factorial : ℝ) ∧
      ∑ k ∈ Finset.range n, (k.factorial : ℝ) < kurepaPartialIntegral n A + 1 / m := by
  let d : ℝ := (n : ℝ) - 1
  let c : ℝ := 4 / (7 * m)
  change d ≤ A at hA
  change lambertMap (-A / d) = -(1 / d) * c ^ (1 / d) at hW
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < d := by dsimp [d]; linarith
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) < m := by linarith
  have hc₀ : 0 < c := by dsimp [c]; positivity
  have hc : c ≤ 4 / 7 := by
    dsimp [c]
    gcongr
    linarith
  obtain ⟨a, ha, haW⟩ := exists_lambertSequence (n := n) (by omega)
    (c := 4 / 7) (by norm_num) (by norm_num)
  -- The smaller Lambert target magnitude puts `A` at least as far out on the lower branch.
  have htarget : -(1 / d) * (4 / 7 : ℝ) ^ (1 / d) ≤ -(1 / d) * c ^ (1 / d) :=
    mul_le_mul_of_nonpos_left (rpow_le_rpow hc₀.le hc (one_div_nonneg.mpr hd.le))
      (neg_nonpos.mpr (one_div_nonneg.mpr hd.le))
  have haA : a ≤ A := by
    have ha' : -a / d ∈ Set.Iic (-1 : ℝ) := by
      rw [Set.mem_Iic, neg_div, neg_le_neg_iff, one_le_div hd]
      exact ha
    have hA' : -A / d ∈ Set.Iic (-1 : ℝ) := by
      rw [Set.mem_Iic, neg_div, neg_le_neg_iff, one_le_div hd]
      exact hA
    have hmap : lambertMap (-a / d) ≤ lambertMap (-A / d) := by
      rw [haW, hW]
      exact htarget
    have hle := (lambertMap_strictAntiOn_Iic.le_iff_ge ha' hA').mp hmap
    rwa [div_le_div_iff_of_pos_right hd, neg_le_neg_iff] at hle
  -- Scaling the remainder by `m` makes its highest-power factor match the `m = 1` case.
  have htopA : (m : ℝ) * (exp (-A) * A ^ (n - 1)) = 4 / 7 := by
    rw [mul_comm (exp (-A)), lambertCutoff_pow_mul_exp n (by omega) A hc₀.le hW]
    dsimp [c]
    field_simp
  have htopa : exp (-a) * a ^ (n - 1) = 4 / 7 := by
    rw [mul_comm]
    exact lambertCutoff_pow_mul_exp n (by omega) a (by norm_num) haW
  have ha₀ := hd.trans_le ha
  have hA₀ := hd.trans_le hA
  have hterm (j : ℕ) (hj : j ≤ n - 1) :
      (m : ℝ) * exp (-A) * A ^ j ≤ exp (-a) * a ^ j := by
    apply le_of_mul_le_mul_right _ (pow_pos ha₀ (n - 1 - j))
    calc
      _ ≤ ((m : ℝ) * exp (-A) * A ^ j) * A ^ (n - 1 - j) := by gcongr
      _ = _ := by
        simp only [mul_assoc, ← pow_add, Nat.add_sub_of_le hj, htopA, htopa]
  have htail : (m : ℝ) * ((∑ k ∈ Finset.range n, (k.factorial : ℝ)) -
      kurepaPartialIntegral n A) ≤ (∑ k ∈ Finset.range n, (k.factorial : ℝ)) -
      kurepaPartialIntegral n a := by
    rw [sum_factorial_sub_kurepaPartialIntegral n A, sum_factorial_sub_kurepaPartialIntegral n a,
      ← mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [mul_left_comm ((m : ℝ) * exp (-A)), mul_left_comm (exp (-a))]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [← mul_div_assoc, ← mul_div_assoc]
    have hjk := Finset.mem_range.mp hj
    have hkn := Finset.mem_range.mp hk
    exact div_le_div_of_nonneg_right (hterm j (by omega)) (Nat.cast_nonneg _)
  refine ⟨kurepaPartialIntegral_lt_sum_factorial n (by omega) A hA₀.le, ?_⟩
  have hb := (kurepaPartialIntegral_lambertSequence_bounds n hn a ha haW).2
  have hlt := htail.trans_lt (show (∑ k ∈ Finset.range n, (k.factorial : ℝ)) -
      kurepaPartialIntegral n a < 1 by linarith only [hb])
  have hdiv : (∑ k ∈ Finset.range n, (k.factorial : ℝ)) - kurepaPartialIntegral n A < 1 / m :=
    (lt_div_iff₀ hm₀).mpr (by simpa only [mul_comm (m : ℝ)] using hlt)
  linarith only [hdiv]

end MetaMathlibExt
