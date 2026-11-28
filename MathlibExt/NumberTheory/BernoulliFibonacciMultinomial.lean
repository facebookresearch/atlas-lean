/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Choose.Cast

/-!
# A multinomial Bernoulli–Fibonacci sum

Binet's formula and the Bernoulli generating series identify a product of two series
with the exponential at the conjugate golden ratio. Squaring this product gives the
four indices of the multinomial sum.
-/

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open PowerSeries Finset
open scoped goldenRatio

private noncomputable def fibSeries : PowerSeries ℝ :=
  mk fun j => (Nat.fib (j + 1) : ℝ) / (j + 1 : ℕ) / j.factorial

private noncomputable abbrev bernSeries :=
  rescale (Real.sqrt 5) (bernoulliPowerSeries ℝ)

private noncomputable abbrev expSeries (a : ℝ) := rescale a (exp ℝ)

private theorem fibSeries_mul_scaled_X :
    fibSeries * (C (Real.sqrt 5) * X) = expSeries φ - expSeries ψ := by
  rw [← mul_assoc]
  ext n
  cases n with
  | zero =>
    simp only [coeff_zero_mul_X, map_sub, expSeries, coeff_rescale, pow_zero, one_mul, sub_self]
  | succ n =>
    rw [coeff_succ_mul_X, coeff_mul_C, fibSeries, coeff_mk, Real.coe_fib_eq]
    simp [expSeries, Nat.factorial_succ, field]

private theorem fibSeries_mul_bernSeries : fibSeries * bernSeries = expSeries ψ := by
  have hB : bernSeries * (expSeries (Real.sqrt 5) - 1) = C (Real.sqrt 5) * X := by
    simpa [bernSeries, expSeries] using
      congrArg (rescale (Real.sqrt 5)) (bernoulliPowerSeries_mul_exp_sub_one ℝ)
  have hφ : expSeries (Real.sqrt 5) * expSeries ψ = expSeries φ := by
    rw [expSeries, expSeries, exp_mul_exp_eq_exp_add, ← Real.goldenRatio_sub_goldenConj,
      sub_add_cancel]
  have hne : C (Real.sqrt 5) * (X : PowerSeries ℝ) ≠ 0 :=
    mul_ne_zero (by simp [Real.sqrt_ne_zero'.mpr (by norm_num : 0 < (5 : ℝ))]) X_ne_zero
  apply mul_right_cancel₀ hne
  calc
    _ = (expSeries φ - expSeries ψ) * bernSeries := by rw [← fibSeries_mul_scaled_X]; ring
    _ = expSeries ψ * (bernSeries * (expSeries (Real.sqrt 5) - 1)) := by rw [← hφ]; ring
    _ = _ := by rw [hB]

private theorem generating_identity :
    (fibSeries ^ 2 * bernSeries ^ 2) * expSeries (Real.sqrt 5) = exp ℝ := by
  rw [← mul_pow, fibSeries_mul_bernSeries, sq, expSeries, expSeries,
    exp_mul_exp_eq_exp_add, exp_mul_exp_eq_exp_add]
  have h : ψ + ψ + Real.sqrt 5 = 1 := by unfold Real.goldenConj; ring
  rw [h]
  simp

/-- Expand a four-factor Cauchy product using two pairs of bounded indices. -/
private theorem sum_four_coeff (f b : PowerSeries ℝ) (n : ℕ) :
    (∑ p ∈ (univ : Finset ((Fin 2 → Fin (n + 1)) × (Fin 2 → Fin (n + 1)))).filter
        (fun p => (∑ i, (p.1 i).val) + (∑ i, (p.2 i).val) = n),
        (∏ i, coeff (p.1 i).val f) * ∏ i, coeff (p.2 i).val b) =
      coeff n (f ^ 2 * b ^ 2) := by
  classical
  let series : Fin 2 ⊕ Fin 2 → PowerSeries ℝ := Sum.elim (fun _ => f) (fun _ => b)
  have hprod : ∏ i, series i = f ^ 2 * b ^ 2 := by
    simp [Fintype.prod_sum_type, series]
  rw [← hprod, coeff_prod]
  let degrees (p : (Fin 2 → Fin (n + 1)) × (Fin 2 → Fin (n + 1))) :
      (Fin 2 ⊕ Fin 2) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (Sum.elim (fun i => (p.1 i).val) (fun i => (p.2 i).val))
  apply sum_bij (fun p _ => degrees p)
  · intro p hp
    simpa [degrees, Fintype.sum_sum_type] using (mem_filter.mp hp).2
  · intro p hp q hq h
    refine Prod.ext (funext fun i => Fin.ext ?_) (funext fun i => Fin.ext ?_)
    · exact DFunLike.congr_fun h (Sum.inl i)
    · exact DFunLike.congr_fun h (Sum.inr i)
  · intro d hd
    have hsum := (mem_finsuppAntidiag.mp hd).1
    let k (i) : Fin (n + 1) := ⟨d i, Nat.lt_succ_of_le
      (hsum ▸ single_le_sum (f := fun i => d i) (fun _ _ => Nat.zero_le _) (mem_univ i))⟩
    refine ⟨(fun i => k (.inl i), fun i => k (.inr i)), ?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_univ _, (Fintype.sum_sum_type (fun i => d i)).symm.trans hsum⟩
    · ext (i | i) <;> rfl
  · intro p hp
    simp [degrees, series, Fintype.prod_sum_type]

/-- **A multinomial sum of Bernoulli and Fibonacci numbers equal to one.** Let $F_n$ be the
Fibonacci numbers and let $B_k$ be the Bernoulli numbers, with $B_1 = -\tfrac{1}{2}$. For every
natural number $m$,
$$\sum_{n=0}^{m} \sum_{j_1 + j_2 + \ell_1 + \ell_2 = n} \sqrt{5}^{\,\ell_1 + \ell_2 + m - n}
\frac{n!}{j_1!\, j_2!\, \ell_1!\, \ell_2!} \binom{m}{n} B_{\ell_1} B_{\ell_2}
\frac{F_{j_1+1}}{j_1+1} \cdot \frac{F_{j_2+1}}{j_2+1} = 1,$$
where the inner sum runs over all quadruples $(j_1, j_2, \ell_1, \ell_2)$ of natural numbers with
sum $n$.

This is the case $q = 2$, $x = \sqrt{5}$ of Theorem 15, since $\sqrt{5} + 2\beta = 1$ for
$\beta = (1 - \sqrt{5})/2$. The paper's displayed multinomial coefficient omits the factors
$\ell_1!\, \ell_2!$; with that coefficient the sum at $m = 2$ is $8/3$, not $1$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 17. -/
public theorem sum_bernoulli_fib_two_eq_one (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1),
        ∑ jℓ ∈ (Finset.univ :
            Finset ((Fin 2 → Fin (n + 1)) ×
              (Fin 2 → Fin (n + 1)))).filter
            (fun jℓ => (∑ i, (jℓ.1 i).val) +
              (∑ i, (jℓ.2 i).val) = n),
          (Real.sqrt 5) ^ ((∑ i, (jℓ.2 i).val) + m - n) *
            ((n.factorial : ℝ) /
              ((∏ i, ((jℓ.1 i).val.factorial : ℝ)) *
                ∏ i, ((jℓ.2 i).val.factorial : ℝ))) *
            (Nat.choose m n : ℝ) *
            (∏ i, (bernoulli (jℓ.2 i).val : ℝ)) *
            (∏ i, ((Nat.fib ((jℓ.1 i).val + 1) : ℝ) /
              ((jℓ.1 i).val + 1 : ℕ))) = 1 := by
  classical
  calc
    _ = (m.factorial : ℝ) * coeff m
          ((fibSeries ^ 2 * bernSeries ^ 2) * expSeries (Real.sqrt 5)) := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
      apply sum_congr rfl
      intro n hn
      have hnm := mem_range_succ_iff.mp hn
      rw [← sum_four_coeff, sum_mul, mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [Nat.add_sub_assoc hnm, pow_add, Nat.cast_choose ℝ hnm]
      simp only [Fin.prod_univ_two, Fin.sum_univ_two, fibSeries, bernSeries, expSeries,
        bernoulliPowerSeries, coeff_mk, coeff_rescale, coeff_exp, map_div₀, map_one,
        map_natCast, eq_ratCast, pow_add]
      field_simp
    _ = 1 := by simp [generating_identity, Nat.factorial_ne_zero]

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
