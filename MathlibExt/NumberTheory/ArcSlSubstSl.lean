/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Power series inverse of Sl

The main result is `arcSl_subst_sl`: substituting the Eisenstein power series
`Sl` into the formal power series `ArcSl` gives the variable `X`. The proof
uses the binomial series for `(1 + X) ^ (-2/3)` and the identity
`Cl ^ 3 + Sl ^ 3 = 1` for the companion series.
-/

namespace MetaMathlibExt

open PowerSeries

namespace arcSl_subst_sl

/-- The binomial series for `(1 + X) ^ (-2/3)`. -/
private noncomputable def binomial : PowerSeries ℚ :=
  binomialSeries ℚ (-2 / 3 : ℚ)

/-- The binomial series for `(1 - X) ^ (-2/3)`, obtained by rescaling. -/
private noncomputable def rescaledBinomial : PowerSeries ℚ :=
  rescale (-1 : ℚ) binomial

/-- The series `(1 - X ^ 3) ^ (-2/3)`, obtained by expanding by a factor of three. -/
private noncomputable def expandedBinomial : PowerSeries ℚ :=
  expand 3 (by norm_num) rescaledBinomial

private lemma coeff_rescaledBinomial (m : ℕ) :
    coeff m rescaledBinomial = (-1 : ℚ) ^ m * Ring.choose (-2 / 3 : ℚ) m := by
  simp [rescaledBinomial, binomial, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]

private lemma rescale_one_add_X : rescale (-1 : ℚ) (1 + X) = 1 - X := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n => simp

private lemma cube_binomial : binomial ^ 3 * (1 + X) ^ 2 = 1 := by
  have h1 : binomial * binomial = binomialSeries ℚ (-4 / 3 : ℚ) := by
    rw [binomial, ← binomialSeries_add]
    congr 1
    norm_num
  have h2 : binomialSeries ℚ (-4 / 3 : ℚ) * binomial = binomialSeries ℚ (-2 : ℚ) := by
    rw [binomial, ← binomialSeries_add]
    congr 1
    norm_num
  have h3 : binomialSeries ℚ (-2 : ℚ) * binomialSeries ℚ (2 : ℚ) = 1 := by
    rw [← binomialSeries_add]
    norm_num
  have h4 : binomialSeries ℚ (2 : ℚ) = (1 + X) ^ 2 := by
    have h := binomialSeries_nat (R := ℚ) (A := ℚ) 2
    norm_num at h
    exact h
  calc binomial ^ 3 * (1 + X) ^ 2
      = (binomial * binomial * binomial) * binomialSeries ℚ (2 : ℚ) := by
        rw [pow_succ, pow_succ, pow_one, h4]
    _ = binomialSeries ℚ (-2 : ℚ) * binomialSeries ℚ (2 : ℚ) := by rw [h1, h2]
    _ = 1 := h3

private lemma cube_rescaledBinomial : rescaledBinomial ^ 3 * (1 - X) ^ 2 = 1 := by
  have h := congrArg (rescale (-1 : ℚ)) cube_binomial
  simpa [rescaledBinomial, rescale_one_add_X, map_pow, map_mul, map_one] using h

private lemma cube_expandedBinomial :
    expandedBinomial ^ 3 * (1 - X ^ 3) ^ 2 = 1 := by
  have h := congrArg (expand 3 (by norm_num : (3 : ℕ) ≠ 0)) cube_rescaledBinomial
  simpa [expandedBinomial, map_pow, map_mul, map_one, map_sub, expand_X] using h

private lemma constantCoeff_expandedBinomial : constantCoeff expandedBinomial = 1 := by
  rw [expandedBinomial, constantCoeff_expand, ← coeff_zero_eq_constantCoeff_apply,
    coeff_rescaledBinomial]
  simp

private lemma derivative_arcSl_eq_expandedBinomial :
    derivative (R := ℚ) (PowerSeries.mk fun k => if k % 3 = 1 then
        (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0) =
      expandedBinomial := by
  ext n
  rw [coeff_derivative, coeff_mk]
  by_cases h3 : 3 ∣ n
  · obtain ⟨m, rfl⟩ := h3
    have hmod : (3 * m + 1) % 3 = 1 := by omega
    have hdiv : (3 * m + 1) / 3 = m := by omega
    simp only [hmod, hdiv, ↓reduceIte]
    rw [expandedBinomial, coeff_expand]
    simp only [show 3 ∣ 3 * m from ⟨m, rfl⟩, ↓reduceIte]
    have hdiv2 : 3 * m / 3 = m := by omega
    rw [hdiv2, coeff_rescaledBinomial]
    field_simp
    push_cast
    ring
  · simp only [show ¬ (n + 1) % 3 = 1 by omega, ↓reduceIte]
    rw [expandedBinomial, coeff_expand]
    simp only [h3, ↓reduceIte]
    simp

private lemma cube_add (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : constantCoeff S = 0) (hC0 : constantCoeff C = 1) :
    C ^ 3 + S ^ 3 = 1 := by
  apply PowerSeries.derivative.ext
  · have hD : PowerSeries.derivative (R := ℚ) (C ^ 3 + S ^ 3) = 0 := by
      simp only [map_add, derivative_pow, hS, hC]
      ring
    rw [hD]
    simp
  · simp [map_add, map_pow, hS0, hC0]

private lemma subst_expandedBinomial_mul_sq (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : constantCoeff S = 0) (hC0 : constantCoeff C = 1) :
    (expandedBinomial.subst S) * C ^ 2 = 1 := by
  have ha : HasSubst S := HasSubst.of_constantCoeff_zero' hS0
  have hCS := cube_add S C hS hC hS0 hC0
  have h1 : (1 : PowerSeries ℚ).subst S = 1 := by
    rw [← coe_substAlgHom ha, map_one]
  have hE : (expandedBinomial.subst S) ^ 3 * (1 - S ^ 3) ^ 2 = 1 := by
    have h0 : (expandedBinomial ^ 3 * (1 - X ^ 3) ^ 2).subst S = 1 := by
      rw [cube_expandedBinomial, h1]
    rw [subst_mul ha, subst_pow ha, subst_pow ha, subst_sub ha, subst_pow ha, subst_X ha,
      h1] at h0
    exact h0
  have h1sub : (1 : PowerSeries ℚ) - S ^ 3 = C ^ 3 := by
    rw [sub_eq_iff_eq_add]
    exact hCS.symm
  rw [h1sub] at hE
  have hZ3 : ((expandedBinomial.subst S) * C ^ 2) ^ 3 = 1 := by
    rw [mul_pow, show (C ^ 2 : PowerSeries ℚ) ^ 3 = (C ^ 3) ^ 2 by ring]
    exact hE
  have hconstZ : constantCoeff ((expandedBinomial.subst S) * C ^ 2) = 1 := by
    have hEconst : constantCoeff (expandedBinomial.subst S) = 1 := by
      rw [PowerSeries.constantCoeff_eq,
        constantCoeff_subst_of_constantCoeff_zero hS0]
      simp [constantCoeff_expandedBinomial]
    simp [map_mul, map_pow, hEconst, hC0]
  have hZne : (expandedBinomial.subst S) * C ^ 2 ≠ 0 := by
    intro h
    rw [h] at hconstZ
    simp at hconstZ
  have hD : PowerSeries.derivative (R := ℚ) ((expandedBinomial.subst S) * C ^ 2) = 0 := by
    have h1 : PowerSeries.derivative (R := ℚ) (((expandedBinomial.subst S) * C ^ 2) ^ 3) = 0 := by
      rw [hZ3]
      simp
    rw [derivative_pow] at h1
    have hcast : ((3 : ℕ) : MvPowerSeries Unit ℚ) ≠ 0 := by
      intro h
      have h2 := congrArg (MvPowerSeries.constantCoeff (σ := Unit) (R := ℚ)) h
      simp only [map_natCast, map_zero] at h2
      norm_num at h2
    have hne : ((3 : ℕ) : MvPowerSeries Unit ℚ) * ((expandedBinomial.subst S) * C ^ 2) ^ (3 - 1)
        ≠ 0 :=
      mul_ne_zero hcast (pow_ne_zero _ hZne)
    have hderiv := (mul_eq_zero.mp h1).resolve_left hne
    exact hderiv
  apply PowerSeries.derivative.ext
  · rw [hD]
    simp
  · rw [hconstZ]
    simp

end arcSl_subst_sl

/-- **Power series inverse of $\mathrm{Sl}$.** Let $S, C \in \mathbb{Q}[[u]]$ be formal power
series with $S' = C^2$, $C' = -S^2$, $S(0) = 0$ and $C(0) = 1$. Then
$$\sum_{n \ge 0} (-1)^n \binom{-2/3}{n} \frac{S^{3n+1}}{3n+1} = u$$
in $\mathbb{Q}[[u]]$, where $\binom{-2/3}{n} = \frac{1}{n!} \prod_{j=0}^{n-1} (-2/3 - j)$ is the
generalized binomial coefficient.

These conditions determine $S$ and $C$ uniquely: they are the Taylor series at $0$ of the
Eisenstein elliptic functions $\mathrm{Sl}$ and $\mathrm{Cl}$. The statement says that
$\mathrm{ArcSl}(t) = \sum_{n \ge 0} (-1)^n \binom{-2/3}{n} t^{3n+1}/(3n+1)$ is the inverse of
$\mathrm{Sl}$ near $0$.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Corollary 1
(`integers-2026-A112-cor-1`). -/
public theorem arcSl_subst_sl (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1) :
    (PowerSeries.mk fun k => if k % 3 = 1 then
        (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S =
      PowerSeries.X := by
  have ha : HasSubst S := HasSubst.of_constantCoeff_zero' hS0
  have hD : PowerSeries.derivative (R := ℚ)
      ((PowerSeries.mk fun k => if k % 3 = 1 then
        (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S) = 1 := by
    rw [derivative_subst ha, arcSl_subst_sl.derivative_arcSl_eq_expandedBinomial, hS]
    exact arcSl_subst_sl.subst_expandedBinomial_mul_sq S C hS hC hS0 hC0
  have hconst : constantCoeff
      ((PowerSeries.mk fun k => if k % 3 = 1 then
        (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S) = 0 := by
    apply constantCoeff_subst_eq_zero hS0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mk]
    norm_num
  apply PowerSeries.derivative.ext
  · rw [hD]
    simp
  · rw [hconst]
    simp

end MetaMathlibExt
