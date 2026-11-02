/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace MathlibExt.Probability

/-- **Variance of the sample mean of i.i.d. samples.** Let $X_0, X_1, X_2, \dots$ be real-valued
random variables on a measure space $(\Omega, \mu)$ that are mutually independent and each have
the same distribution as $X_0$, and suppose $X_0$ is square-integrable. Then for every integer
$n \ge 1$, with variances taken with respect to $\mu$,
$$
\operatorname{Var}\Big(\frac{1}{n} \sum_{i=0}^{n-1} X_i\Big) = \frac{\operatorname{Var}(X_0)}{n}.
$$

Square-integrability is required only of $X_0$; identical distribution transfers it to every
sample. -/
theorem variance_sample_mean_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ)
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    (n : ℕ) (hn : n ≠ 0) :
    variance (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) μ
      = variance (X 0) μ / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hMemLp' : ∀ i, MemLp (X i) 2 μ := fun i => (hIdent i).memLp_iff.mpr hMemLp
  have hfun : (∑ i ∈ Finset.range n, X i)
      = fun ω => ∑ i ∈ Finset.range n, X i ω :=
    funext fun ω => Finset.sum_apply _ _ _
  have hsum : variance (fun ω => ∑ i ∈ Finset.range n, X i ω) μ
      = ∑ i ∈ Finset.range n, variance (X i) μ := by
    rw [← hfun]
    exact IndepFun.variance_sum (fun i _ => hMemLp' i)
      (fun i _ j _ hij => hIndep.indepFun hij)
  have hcongr : ∑ i ∈ Finset.range n, variance (X i) μ
      = n * variance (X 0) μ := by
    rw [Finset.sum_congr rfl (fun i _ => (hIdent i).variance_eq),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hshape : (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
      = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i ω) := by
    funext ω
    rw [div_eq_inv_mul]
  rw [hshape, variance_const_mul, hsum, hcongr]
  field_simp

end MathlibExt.Probability
