/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Classical orthogonal polynomial family.** A classical orthogonal polynomial family consists
of real polynomials $P_0, P_1, P_2, \dots$, each $P_n$ monic of degree exactly $n$, a measure
$\mu$ on $\mathbb{R}$, a measurable set $D \subseteq \mathbb{R}$ that is an interval with
nonempty interior, and a function $w : \mathbb{R} \to \mathbb{R}$ (the weight), such that
$w(x) \ge 0$ for every $x \in D$; $\mu$ is the measure with density $w$ with respect to
Lebesgue measure restricted to $D$; $\int P_m P_n \, d\mu = 0$ whenever $m \ne n$;
$\int P_n^2 \, d\mu \ne 0$ for every $n$; and there are real numbers $u_0, u_1, v_0, v_1, v_2$,
with $v_0, v_1, v_2$ not all zero, such that at every interior point $x$ of $D$ the weight is
differentiable and $(v_0 + v_1 x + v_2 x^2) \, w'(x) = (u_0 + u_1 x) \, w(x)$ (the Pearson
equation).

Source: concept `jis_sem_6573fe45e3bbd4f163aed756`, source block
`jis_srcblock_e90c95146a5fe658`, lines 208-221. -/
structure ClassicalOrthogonalPolynomialFamily where
  /-- Sequence of real polynomials (concept `jis_sem_6573fe45e3bbd4f163aed756`). -/
  P : ℕ → Polynomial ℝ
  /-- The source uses the monic normalization of the polynomial family. -/
  monic : ∀ n : ℕ, (P n).Monic
  /-- The `n`th member has degree exactly `n`. -/
  natDegree_eq : ∀ n : ℕ, (P n).natDegree = n
  /-- Orthogonalizing measure (concept `jis_sem_6573fe45e3bbd4f163aed756`). -/
  μ : MeasureTheory.Measure ℝ
  /-- Supporting domain for the weight density (source block `jis_srcblock_e90c95146a5fe658`). -/
  domain : Set ℝ
  /-- The domain is measurable (source block `jis_srcblock_e90c95146a5fe658`). -/
  measurable_domain : MeasurableSet domain
  /-- The support domain is an interval, as in the classical families. -/
  ordConnected_domain : Set.OrdConnected domain
  /-- The support interval has nonempty interior, so the Pearson equation is not vacuous. -/
  interior_domain_nonempty : (interior domain).Nonempty
  /-- Distinct members are orthogonal with respect to `μ`
      (concept `jis_sem_6573fe45e3bbd4f163aed756`). -/
  orthogonal : ∀ m n : ℕ, m ≠ n →
    MeasureTheory.integral μ (fun x => Polynomial.eval x (P m) * Polynomial.eval x (P n)) = 0
  /-- Each squared norm is nonzero, excluding the zero family
      (concept `jis_sem_6573fe45e3bbd4f163aed756`). -/
  norm_ne_zero : ∀ n : ℕ,
    MeasureTheory.integral μ (fun x => (Polynomial.eval x (P n)) ^ 2) ≠ 0
  /-- Nonnegative weight function (source block `jis_srcblock_e90c95146a5fe658`). -/
  weight : ℝ → ℝ
  /-- The weight is nonnegative (source block `jis_srcblock_e90c95146a5fe658`). -/
  weight_nonneg : ∀ x ∈ domain, 0 ≤ weight x
  /-- The measure is the weight density against restricted Lebesgue volume
      (source block `jis_srcblock_e90c95146a5fe658`). -/
  measure_eq : μ = (MeasureTheory.volume.restrict domain).withDensity
    (fun x => ENNReal.ofReal (weight x))
  /-- Classical Pearson equation `V w' = U w`, where `U` is linear and `V` is a genuinely
      nonzero quadratic polynomial. This cross-multiplied form remains meaningful at zeros of
      `V` or `w` (source block `jis_srcblock_e90c95146a5fe658`). -/
  classical : ∃ u0 u1 v0 v1 v2 : ℝ,
    (v0 ≠ 0 ∨ v1 ≠ 0 ∨ v2 ≠ 0) ∧
      ∀ x : ℝ, x ∈ interior domain →
        DifferentiableAt ℝ weight x ∧
          (v0 + v1 * x + v2 * x ^ 2) * deriv weight x =
            (u0 + u1 * x) * weight x

end

end MetaMathlibExt
