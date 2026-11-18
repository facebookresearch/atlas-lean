/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Spectral gap and log-Sobolev constant of a finite chain, in Dirichlet-form terms

For a Markov kernel `P` on a finite set with weights `π`, write `E(f, f) = E_{P - 1}(f, f)
= ½ ∑ π(x) P(x, y) (f x - f y)²` for its Dirichlet form (`DirichletForm.form_sub_one`). Following
P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*,
Ann. Appl. Probab. 6 (1996), equations (1.4), (1.6) and (3.1):

* the variance is `Var(f) = ½ ∑_{x,y} (f x - f y)² π(x) π(y)`;
* the spectral gap is `λ = inf {E(f, f) / Var(f) : Var(f) ≠ 0}`;
* the entropy-like functional is `L(f) = ∑_x f(x)² log(f(x)² / ‖f‖₂²) π(x)`;
* the log-Sobolev constant is `α = inf {E(f, f) / L(f) : L(f) ≠ 0}`.

So `λ` is the best constant in the Poincaré inequality `λ Var(f) ≤ E(f, f)` and `1/α` the best
constant in the log-Sobolev inequality `L(f) ≤ C E(f, f)`. Both infima are taken in `ℝ`; when
the set is empty (for instance on a one-point space, or when `π` charges a single point) the
value is `sInf ∅ = 0`.

The Poincaré inequality is the hypothesis of Sinclair's mixing bounds
(`MathlibExt.Probability.CanonicalPaths`, `MathlibExt.Probability.PoincareMixing`), written there
as `∑ (ψ x - ψ y)² π(x) π(y) ≤ B ∑ (ψ x - ψ y)² π(x) P(x, y)`, i.e. `Var ≤ B E`. We prove that this
is the same as `1/B ≤ λ`, and so restate Sinclair's mixing bound for a lazy chain in terms of its
spectral gap.

## Main definitions

* `weightedVariance π f`, `spectralGap π P`, `entropyFunctional π f`, `logSobolevConstant π P`.

## Main results

* `spectralGap_mul_weightedVariance_le`: the Poincaré inequality `λ Var(f) ≤ E(f, f)`.
* `le_spectralGap`: any constant in a Poincaré inequality is at most `λ`.
* `inv_le_spectralGap_iff_poincare`: Sinclair's Poincaré hypothesis with constant `B` is
  `1/B ≤ λ`.
* `isMixedAt_of_le_spectralGap`: Sinclair's mixing bound for a lazy reversible chain from a lower
  bound on its spectral gap.
* `entropyFunctional_nonneg`, `logSobolevConstant_mul_entropyFunctional_le`: the log-Sobolev
  inequality `α L(f) ≤ E(f, f)`.

The comparison `2α ≤ λ` (Diaconis and Saloff-Coste 1996, Lemma 3.1) is proved in
`MathlibExt.Probability.DirichletForm.LogSobolevGap`.

## References

* P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*,
  Ann. Appl. Probab. 6 (1996), 695–750: equations (1.4), (1.6), (1.7), (3.1) and Lemma 3.1.
* A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combin. Probab. Comput. 1 (1992), 351–370.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory
open MathlibExt.Probability.MarkovMixing

namespace MathlibExt.Probability.DirichletForm

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Variance of a function under a weight vector.**
`Var_π(f) = ½ ∑_{x,y} (f x - f y)² π(x) π(y)` (P. Diaconis and L. Saloff-Coste,
*Ann. Appl. Probab.* 6 (1996), equation (1.4)); for a probability vector `π` this is
`∑ π (f - E_π f)²`. -/
noncomputable def weightedVariance (π : S → ℝ) (f : S → ℝ) : ℝ :=
  1 / 2 * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * π y)

/-- **Spectral gap of a finite Markov kernel, in Dirichlet-form terms.**
`λ(P, π) = inf {E(f, f) / Var_π(f) : Var_π(f) ≠ 0}`, where `E(f, f) = ½ ∑ π(x) P(x, y)
(f x - f y)²` is the Dirichlet form of `P - 1` (P. Diaconis and L. Saloff-Coste, *Ann. Appl.
Probab.* 6 (1996), equation (1.4)). The infimum of the empty set is `0` (one-point spaces). -/
noncomputable def spectralGap (π : S → ℝ) (P : Matrix S S ℝ) : ℝ :=
  sInf ((fun f => form π (P - 1) f f / weightedVariance π f) '' {f | weightedVariance π f ≠ 0})

/-- **Entropy-like functional of the log-Sobolev inequality.**
`L_π(f) = ∑_x f(x)² log(f(x)² / ‖f‖₂²) π(x)` with `‖f‖₂² = ∑ π f²` (P. Diaconis and
L. Saloff-Coste, *Ann. Appl. Probab.* 6 (1996), equation (1.6); `Real.log 0 = 0`, so points
where `f` vanishes contribute `0`). -/
noncomputable def entropyFunctional (π : S → ℝ) (f : S → ℝ) : ℝ :=
  ∑ x, f x ^ 2 * Real.log (f x ^ 2 / ∑ y, π y * f y ^ 2) * π x

/-- **Log-Sobolev constant of a finite Markov kernel.**
`α(P, π) = inf {E(f, f) / L_π(f) : L_π(f) ≠ 0}`, with `E` the Dirichlet form of `P - 1`
(P. Diaconis and L. Saloff-Coste, *Ann. Appl. Probab.* 6 (1996), equations (1.7) and (3.1));
`1/α` is the best constant `C` in `L_π(f) ≤ C E(f, f)`. The infimum of the empty set is `0`. -/
noncomputable def logSobolevConstant (π : S → ℝ) (P : Matrix S S ℝ) : ℝ :=
  sInf ((fun f => form π (P - 1) f f / entropyFunctional π f) '' {f | entropyFunctional π f ≠ 0})

omit [DecidableEq S] in
/-- **The variance is nonnegative** when `π ≥ 0`. -/
theorem weightedVariance_nonneg {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : S → ℝ) :
    0 ≤ weightedVariance π f :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hπ x) (hπ y)))

/-- **The Dirichlet form of a Markov kernel is nonnegative.** If `π ≥ 0`, `P ≥ 0` entrywise and
the rows of `P` sum to `1`, then `0 ≤ E_{P - 1}(f, f)`. -/
theorem form_sub_one_self_nonneg {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) {P : Matrix S S ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (f : S → ℝ) :
    0 ≤ form π (P - 1) f f := by
  rw [form_sub_one π hrow]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
  have := mul_nonneg (mul_nonneg (hπ x) (hP x y)) (mul_self_nonneg (f x - f y))
  linarith [show π x * P x y * (f x - f y) * (f x - f y) =
    π x * P x y * ((f x - f y) * (f x - f y)) by ring]

/-- **The spectral gap is nonnegative** for `π ≥ 0` and a stochastic `P`. -/
theorem spectralGap_nonneg {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) {P : Matrix S S ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) : 0 ≤ spectralGap π P := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨f, -, rfl⟩
  exact div_nonneg (form_sub_one_self_nonneg hπ hP hrow f) (weightedVariance_nonneg hπ f)

/-- **Poincaré inequality with the spectral gap.** If `π ≥ 0`, `P ≥ 0` and the rows of `P` sum
to `1`, then `λ(P, π) Var_π(f) ≤ E(f, f)` for every `f` (P. Diaconis and L. Saloff-Coste,
*Ann. Appl. Probab.* 6 (1996), equation (1.4): `λ` is the best such constant). -/
theorem spectralGap_mul_weightedVariance_le {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) {P : Matrix S S ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (f : S → ℝ) :
    spectralGap π P * weightedVariance π f ≤ form π (P - 1) f f := by
  by_cases hv : weightedVariance π f = 0
  · rw [hv, mul_zero]; exact form_sub_one_self_nonneg hπ hP hrow f
  · have hvpos : 0 < weightedVariance π f :=
      lt_of_le_of_ne (weightedVariance_nonneg hπ f) (Ne.symm hv)
    have hle : spectralGap π P ≤ form π (P - 1) f f / weightedVariance π f := by
      refine csInf_le ⟨0, ?_⟩ ⟨f, hv, rfl⟩
      rintro _ ⟨g, -, rfl⟩
      exact div_nonneg (form_sub_one_self_nonneg hπ hP hrow g) (weightedVariance_nonneg hπ g)
    rwa [le_div_iff₀ hvpos] at hle

/-- **Poincaré constants bound the spectral gap from below.** If some function has nonzero
variance and `c Var_π(f) ≤ E(f, f)` for every `f`, then `c ≤ λ(P, π)` (P. Diaconis and
L. Saloff-Coste, *Ann. Appl. Probab.* 6 (1996), equation (1.4)). -/
theorem le_spectralGap {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) {P : Matrix S S ℝ}
    (hne : ∃ f, weightedVariance π f ≠ 0) {c : ℝ}
    (h : ∀ f, c * weightedVariance π f ≤ form π (P - 1) f f) : c ≤ spectralGap π P := by
  obtain ⟨f₀, hf₀⟩ := hne
  refine le_csInf ⟨_, f₀, hf₀, rfl⟩ ?_
  rintro _ ⟨f, hf, rfl⟩
  have hvpos : 0 < weightedVariance π f :=
    lt_of_le_of_ne (weightedVariance_nonneg hπ f) (Ne.symm hf)
  rw [le_div_iff₀ hvpos]
  exact h f

omit [DecidableEq S] in
private theorem sum_sq_mul_eq_two_mul_weightedVariance (π f : S → ℝ) :
    ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * π y) = 2 * weightedVariance π f := by
  unfold weightedVariance; ring

private theorem sum_sq_mul_eq_two_mul_form {π : S → ℝ} {P : Matrix S S ℝ}
    (hrow : ∀ x, ∑ y, P x y = 1) (f : S → ℝ) :
    ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y) = 2 * form π (P - 1) f f := by
  rw [form_sub_one π hrow]
  have : ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y) =
      ∑ x, ∑ y, π x * P x y * (f x - f y) * (f x - f y) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [this]; ring

/-- **Sinclair's Poincaré hypothesis is a lower bound on the spectral gap.** Let `π ≥ 0`, `P ≥ 0`
with unit row sums, `B > 0`, and suppose some function has nonzero variance. Then the Poincaré
inequality `∑ (ψ x - ψ y)² π(x) π(y) ≤ B ∑ (ψ x - ψ y)² π(x) P(x, y)` for every `ψ` (the
hypothesis of `MathlibExt.Probability.CanonicalPaths.one_le_mul_one_sub_of_poincare` and of
`MathlibExt.Probability.PoincareMixing.isMixedAt_of_poincare`, after A. Sinclair, *Combin.
Probab. Comput.* 1 (1992)) holds if and only if `1/B ≤ λ(P, π)` (P. Diaconis and
L. Saloff-Coste, *Ann. Appl. Probab.* 6 (1996), equation (1.4)). -/
theorem inv_le_spectralGap_iff_poincare {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) {P : Matrix S S ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hne : ∃ f, weightedVariance π f ≠ 0)
    {B : ℝ} (hB : 0 < B) :
    B⁻¹ ≤ spectralGap π P ↔ ∀ ψ : S → ℝ, ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * π y) ≤
      B * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * P x y) := by
  simp only [sum_sq_mul_eq_two_mul_weightedVariance, sum_sq_mul_eq_two_mul_form hrow]
  constructor
  · intro h ψ
    have h1 := spectralGap_mul_weightedVariance_le hπ hP hrow ψ
    have h2 : B⁻¹ * weightedVariance π ψ ≤ spectralGap π P * weightedVariance π ψ :=
      mul_le_mul_of_nonneg_right h (weightedVariance_nonneg hπ ψ)
    have h3 : weightedVariance π ψ = B * (B⁻¹ * weightedVariance π ψ) := by field_simp
    nlinarith
  · intro h
    refine le_spectralGap hπ hne fun f => ?_
    have := h f
    have h3 : B⁻¹ * weightedVariance π f = B⁻¹ * (2 * weightedVariance π f) / 2 := by ring
    rw [h3, div_le_iff₀ (by norm_num : (0 : ℝ) < 2), inv_mul_le_iff₀ hB]
    linarith

/-- **Mixing of a lazy reversible chain from its spectral gap.** Let `K` be stochastic and
reversible with respect to a positive probability vector `π`, and let `P = (I + K)/2`. If
`0 < γ ≤ 1` and `γ ≤ λ(P, π)`, then `P` is `1/4`-mixed at every time `t` with
`(1 - γ)ᵗ (1/π(x) - 1) ≤ 1/4` for all `x`. This is
`MathlibExt.Probability.PoincareMixing.isMixedAt_of_poincare` (after A. Sinclair, *Combin.
Probab. Comput.* 1 (1992), Proposition 1(i)) with its Poincaré hypothesis read off the spectral
gap through `inv_le_spectralGap_iff_poincare`, for `B = 1/γ`. -/
theorem isMixedAt_of_le_spectralGap {π : S → ℝ} (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    {K : Matrix S S ℝ} (hK : K ∈ rowStochastic ℝ S) (hrev : IsDetailedBalance π K)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγ : γ ≤ spectralGap π ((1 / 2 : ℝ) • (1 + K))) {t : ℕ}
    (ht : ∀ x, (1 - γ) ^ t * (1 / π x - 1) ≤ 1 / 4) :
    IsMixedAt ((1 / 2 : ℝ) • (1 + K)) π t := by
  obtain ⟨hPs, -⟩ := PoincareMixing.lazy_mem_rowStochastic_and_detailedBalance hK hrev
  have hP : ∀ x y, 0 ≤ ((1 / 2 : ℝ) • (1 + K)) x y := fun x y =>
    nonneg_of_mem_rowStochastic hPs
  have hrow : ∀ x, ∑ y, ((1 / 2 : ℝ) • (1 + K)) x y = 1 := sum_row_of_mem_rowStochastic hPs
  by_cases hne : ∃ f, weightedVariance π f ≠ 0
  · have hB : 1 ≤ γ⁻¹ := one_le_inv₀ hγ0 |>.mpr hγ1
    have hpoin := (inv_le_spectralGap_iff_poincare (fun x => (hπ x).le) hP hrow hne
      (inv_pos.mpr hγ0)).mp (by rwa [inv_inv])
    refine PoincareMixing.isMixedAt_of_poincare hπ hπ1 hK hrev hB hpoin fun x => ?_
    simpa [one_div, inv_inv] using ht x
  · -- Every function is `π`-constant: the Poincaré inequality holds trivially with `B = 1/γ`.
    push Not at hne
    have hB : 1 ≤ γ⁻¹ := one_le_inv₀ hγ0 |>.mpr hγ1
    refine PoincareMixing.isMixedAt_of_poincare hπ hπ1 hK hrev hB (fun ψ => ?_) fun x => ?_
    · rw [sum_sq_mul_eq_two_mul_weightedVariance, hne ψ, sum_sq_mul_eq_two_mul_form hrow]
      have := form_sub_one_self_nonneg (fun x => (hπ x).le) hP hrow ψ
      rw [mul_zero]
      exact mul_nonneg (inv_pos.mpr hγ0).le (by linarith)
    · simpa [one_div, inv_inv] using ht x

omit [DecidableEq S] in
/-- **The entropy-like functional is nonnegative.** If `π` is a probability vector, then
`0 ≤ L_π(f)` for every `f` (P. Diaconis and L. Saloff-Coste, *Ann. Appl. Probab.* 6 (1996),
Section 3.1; from `t log(t/N) ≥ t - N` for `t ≥ 0`, `N > 0`). -/
theorem entropyFunctional_nonneg {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1) (f : S → ℝ) :
    0 ≤ entropyFunctional π f := by
  set N := ∑ y, π y * f y ^ 2 with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun y _ => mul_nonneg (hπ y) (sq_nonneg _)
  rcases hN0.lt_or_eq with hNpos | hNz
  · -- `f² log(f²/N) ≥ f² - N` pointwise.
    have hpt : ∀ x, (f x ^ 2 - N) * π x ≤ f x ^ 2 * Real.log (f x ^ 2 / N) * π x := by
      intro x
      refine mul_le_mul_of_nonneg_right ?_ (hπ x)
      rcases (sq_nonneg (f x)).lt_or_eq with hpos | hz
      · have hl := Real.one_sub_inv_le_log_of_pos (div_pos hpos hNpos)
        rw [inv_div] at hl
        have : f x ^ 2 * (1 - N / f x ^ 2) = f x ^ 2 - N := by
          rw [mul_sub, mul_one, mul_div_cancel₀ _ hpos.ne']
        nlinarith [mul_le_mul_of_nonneg_left hl hpos.le]
      · rw [← hz]; simp; linarith
    have hsum : ∑ x, (f x ^ 2 - N) * π x = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ1, mul_one]
      rw [hN]; simp only [mul_comm]; ring
    unfold entropyFunctional
    rw [← hN]
    linarith [Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset S)) => hpt x]
  · unfold entropyFunctional
    rw [← hN, ← hNz]
    simp

/-- **Log-Sobolev inequality with the log-Sobolev constant.** If `π` is a probability vector,
`P ≥ 0` and the rows of `P` sum to `1`, then `α(P, π) L_π(f) ≤ E(f, f)` for every `f`
(P. Diaconis and L. Saloff-Coste, *Ann. Appl. Probab.* 6 (1996), equations (1.6), (1.7)). -/
theorem logSobolevConstant_mul_entropyFunctional_le {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hπ1 : ∑ x, π x = 1)
    {P : Matrix S S ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (f : S → ℝ) :
    logSobolevConstant π P * entropyFunctional π f ≤ form π (P - 1) f f := by
  by_cases hv : entropyFunctional π f = 0
  · rw [hv, mul_zero]; exact form_sub_one_self_nonneg hπ hP hrow f
  · have hpos : 0 < entropyFunctional π f :=
      lt_of_le_of_ne (entropyFunctional_nonneg hπ hπ1 f) (Ne.symm hv)
    have hle : logSobolevConstant π P ≤ form π (P - 1) f f / entropyFunctional π f := by
      refine csInf_le ⟨0, ?_⟩ ⟨f, hv, rfl⟩
      rintro _ ⟨g, -, rfl⟩
      exact div_nonneg (form_sub_one_self_nonneg hπ hP hrow g) (entropyFunctional_nonneg hπ hπ1 g)
    rwa [le_div_iff₀ hpos] at hle

/-- **The log-Sobolev constant is nonnegative** for a probability vector `π` and a stochastic
`P`. -/
theorem logSobolevConstant_nonneg {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    {P : Matrix S S ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) :
    0 ≤ logSobolevConstant π P := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨f, -, rfl⟩
  exact div_nonneg (form_sub_one_self_nonneg hπ hP hrow f) (entropyFunctional_nonneg hπ hπ1 f)

end MathlibExt.Probability.DirichletForm
