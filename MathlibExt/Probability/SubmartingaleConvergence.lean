/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Almost-sure convergence of submartingales with bounded positive parts

If `X` is a submartingale on a probability space and the integrals of the
positive parts `∫ (X n)⁺ dμ` are uniformly bounded, then `X n` converges
almost surely to an integrable limit `X_∞`.

## Source

This formalizes the target "Theorem (Martingale convergence)"
(Lecture 27) of `v1/Atlas/TheoryOfProbability/targets.yaml`:

> If `X_n` is a submartingale with `sup E X_n⁺ < ∞` then as `n → ∞`,
> `X_n` converges a.s. to a limit `X` with `E|X| < ∞`.

The v1 formalization is `v1/Atlas/TheoryOfProbability/code/SubmartingaleConvergence.lean`
(`submartingale_ae_convergence`, fully proved there); the two helper lemmas
below are also ported from that file.

## Relation to Mathlib

Mathlib has the `L¹`-bounded form of this theorem
(`Submartingale.ae_tendsto_limitProcess`, which assumes
`eLpNorm (X n) 1 μ ≤ R` for all `n`). This API obtains that bound from the
textbook positive-part hypothesis. The bridge is the pointwise identity
`‖x‖ = 2 x⁺ - x` together with monotonicity of `∫ X n dμ`, which turns a
uniform bound on `∫ (X n)⁺ dμ` into a uniform `L¹` bound
`∫ ‖X n‖ dμ ≤ 2C - ∫ X 0 dμ`.

## Main results

* `MeasureTheory.Submartingale.integral_mono`: expectations are monotone
  along a submartingale.
* `MeasureTheory.Submartingale.integral_norm_le`: the `L¹` bound above.
* `MeasureTheory.Submartingale.exists_ae_tendsto_of_posPart_bdd`: the
  textbook convergence theorem.
* `MeasureTheory.Supermartingale.exists_ae_tendsto_of_negPart_bdd`: the
  dual statement for supermartingales, via negation.
* `MeasureTheory.Martingale.exists_ae_tendsto_of_posPart_bdd`: the
  martingale case, since every martingale is a submartingale.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MeasureTheory

/-- **Expectations increase along a submartingale.** Let $(X_n)_{n \ge 0}$ be a real-valued
submartingale with respect to a filtration $(\mathcal F_n)_{n \ge 0}$ on a probability space
$(\Omega, \mu)$. Then $\int X_i \, d\mu \le \int X_j \, d\mu$ for all natural numbers $i \le j$. -/
theorem Submartingale.integral_mono
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hsub : Submartingale X ℱ μ) {i j : ℕ} (hij : i ≤ j) :
    ∫ ω, X i ω ∂μ ≤ ∫ ω, X j ω ∂μ := by
  have h_ae := hsub.2.1 i j hij
  calc ∫ ω, X i ω ∂μ
      ≤ ∫ ω, μ[X j | ↑(ℱ i)] ω ∂μ :=
        integral_mono_ae (hsub.2.2 i) integrable_condExp h_ae
    _ = ∫ ω, X j ω ∂μ := integral_condExp (ℱ.le i) (μ := μ)

/-- **L¹ bound for a submartingale with bounded positive parts.** Let $(X_n)_{n \ge 0}$ be a
real-valued submartingale with respect to a filtration $(\mathcal F_n)_{n \ge 0}$ on a probability
space $(\Omega, \mu)$, and let $C$ be a real number with $\int X_n^+ \, d\mu \le C$ for every $n$,
where $X_n^+$ is the positive part of $X_n$. Then for every $n$,
$\int |X_n| \, d\mu \le 2C - \int X_0 \, d\mu$.

The proof uses the identity $|x| = 2x^+ - x$ together with the monotonicity of
$n \mapsto \int X_n \, d\mu$. -/
theorem Submartingale.integral_norm_le
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} {C : ℝ}
    (hsub : Submartingale X ℱ μ)
    (hbdd : ∀ n, ∫ ω, (X n ω)⁺ ∂μ ≤ C) (n : ℕ) :
    ∫ ω, ‖X n ω‖ ∂μ ≤ 2 * C - ∫ ω, X 0 ω ∂μ := by
  have hint := hsub.2.2
  have hmax : Integrable (fun ω => (X n ω)⁺) μ := (hint n).sup (integrable_zero _ _ μ)
  have key : ∫ ω, ‖X n ω‖ ∂μ = 2 * ∫ ω, (X n ω)⁺ ∂μ - ∫ ω, X n ω ∂μ := by
    have kk : ∀ ω, ‖X n ω‖ = 2 * (X n ω)⁺ - X n ω := by
      intro ω
      simp only [Real.norm_eq_abs, posPart]
      rcases le_or_gt (X n ω) 0 with h | h
      · simp [abs_of_nonpos h, max_eq_right h]
      · simp [abs_of_pos h, max_eq_left h.le]; ring
    simp_rw [kk]
    rw [integral_sub (hmax.const_mul 2) (hint n)]
    congr 1; exact integral_const_mul 2 _
  have hmono : ∫ ω, X 0 ω ∂μ ≤ ∫ ω, X n ω ∂μ :=
    hsub.integral_mono (Nat.zero_le n)
  linarith [hbdd n]

/-- **Submartingale almost-sure convergence theorem.** Let $(X_n)_{n \ge 0}$ be a real-valued
submartingale with respect to a filtration $(\mathcal F_n)_{n \ge 0}$ on a probability space
$(\Omega, \mu)$, and let $C$ be a real number with $\int X_n^+ \, d\mu \le C$ for every $n$, where
$X_n^+$ is the positive part of $X_n$. Then there is an integrable function
$X_\infty : \Omega \to \mathbb R$ such that $X_n(\omega) \to X_\infty(\omega)$ as $n \to \infty$
for $\mu$-almost every $\omega$. -/
theorem Submartingale.exists_ae_tendsto_of_posPart_bdd
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} {C : ℝ}
    (hsub : Submartingale X ℱ μ)
    (hbdd : ∀ n, ∫ ω, (X n ω)⁺ ∂μ ≤ C) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (X_inf ω)) := by
  have hint : ∀ n, Integrable (X n) μ := hsub.2.2
  have h_norm_bdd := hsub.integral_norm_le hbdd
  set B := (2 * C - ∫ ω, X 0 ω ∂μ).toNNReal
  have h_eLpNorm : ∀ n, eLpNorm (X n) 1 μ ≤ ↑B := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm (hint n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    rw [ENNReal.ofReal_le_coe]
    exact le_trans (h_norm_bdd n) (Real.le_coe_toNNReal _)
  have hconv := hsub.ae_tendsto_limitProcess h_eLpNorm
  have hasm : ∀ n, AEStronglyMeasurable (X n) μ :=
    fun n => ((hsub.1 n).mono (ℱ.le n)).aestronglyMeasurable
  have hint_lim : Integrable (ℱ.limitProcess X μ) μ :=
    memLp_one_iff_integrable.mp (Filtration.memLp_limitProcess_of_eLpNorm_bdd hasm h_eLpNorm)
  exact ⟨ℱ.limitProcess X μ, hint_lim, hconv⟩

/-- **Supermartingale almost-sure convergence theorem.** Let $(X_n)_{n \ge 0}$ be a real-valued
supermartingale with respect to a filtration $(\mathcal F_n)_{n \ge 0}$ on a probability space
$(\Omega, \mu)$, and let $C$ be a real number with $\int X_n^- \, d\mu \le C$ for every $n$, where
$X_n^-$ is the negative part of $X_n$. Then there is an integrable function
$X_\infty : \Omega \to \mathbb R$ such that $X_n(\omega) \to X_\infty(\omega)$ as $n \to \infty$
for $\mu$-almost every $\omega$.

This follows from the submartingale theorem applied to $-X$, since $(-X_n)^+ = X_n^-$. -/
theorem Supermartingale.exists_ae_tendsto_of_negPart_bdd
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} {C : ℝ}
    (hsuper : Supermartingale X ℱ μ)
    (hbdd : ∀ n, ∫ ω, (X n ω)⁻ ∂μ ≤ C) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (X_inf ω)) := by
  have hsub : Submartingale (-X) ℱ μ := hsuper.neg
  have hbdd' : ∀ n, ∫ ω, ((-X) n ω)⁺ ∂μ ≤ C := by
    intro n
    have h : (fun ω => ((-X) n ω)⁺) = fun ω => (X n ω)⁻ := by
      funext ω
      rfl
    rw [h]
    exact hbdd n
  obtain ⟨Y, hY, hconv⟩ := hsub.exists_ae_tendsto_of_posPart_bdd hbdd'
  refine ⟨-Y, hY.neg, ?_⟩
  filter_upwards [hconv] with ω hω
  simpa using hω.neg

/-- **Martingale almost-sure convergence theorem.** Let $(X_n)_{n \ge 0}$ be a real-valued
martingale with respect to a filtration $(\mathcal F_n)_{n \ge 0}$ on a probability space
$(\Omega, \mu)$, and let $C$ be a real number with $\int X_n^+ \, d\mu \le C$ for every $n$, where
$X_n^+$ is the positive part of $X_n$. Then there is an integrable function
$X_\infty : \Omega \to \mathbb R$ such that $X_n(\omega) \to X_\infty(\omega)$ as $n \to \infty$
for $\mu$-almost every $\omega$.

This is the submartingale theorem, since every martingale is a submartingale. -/
theorem Martingale.exists_ae_tendsto_of_posPart_bdd
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} {C : ℝ}
    (hmart : Martingale X ℱ μ)
    (hbdd : ∀ n, ∫ ω, (X n ω)⁺ ∂μ ≤ C) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (X_inf ω)) :=
  hmart.submartingale.exists_ae_tendsto_of_posPart_bdd hbdd

end MeasureTheory
