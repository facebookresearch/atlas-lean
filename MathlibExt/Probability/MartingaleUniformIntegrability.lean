/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.TFAE

/-!
# Uniform integrability and `L¹` convergence of (sub)martingales

For a submartingale, uniform integrability is equivalent to convergence
almost surely and in `L¹`, and to convergence in `L¹` alone. For a
martingale there is a fourth equivalent condition: the martingale is the
conditional-expectation martingale of some integrable random variable.

## Source

This formalizes the targets "Theorem (Submartingale convergence)"
(Lecture 28) and "Theorem (Martingale convergence)" (Lecture 29) of
`v1/Atlas/TheoryOfProbability/targets.yaml`:

* "The following are equivalent for a submartingale: (1) It's uniformly
  integrable. (2) It converges a.s. and in `L¹`. (3) It converges in `L¹`."
* "The following are equivalent for a martingale: (1) It's uniformly
  integrable. (2) It converges a.s. and in `L¹`. (3) It converges in `L¹`.
  (4) There is an integrable random variable `X` so that
  `X_n = E(X | ℱ_n)`."

The v1 formalizations are
`v1/Atlas/TheoryOfProbability/code/SubmartingaleUIConvergence.lean`
(`submartingale_ui_convergence_equiv`, fully proved there) for the
submartingale case; the martingale case has no v1 formalization (its v1
file `MartingaleConvergenceUI.lean` is an empty stub), so the fourth
equivalence is proved here from Mathlib's
`Martingale.eq_condExp_of_tendsto_eLpNorm` and
`Integrable.uniformIntegrable_condExp_filtration`.

The statements are new as packaged theorems: Mathlib has the ingredients
(`Submartingale.tendsto_eLpNorm_one_limitProcess`,
`Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable`,
`unifIntegrable_of_tendsto_Lp`, and the martingale conditional-expectation
lemmas above) but no single equivalence for submartingales or martingales.
`L¹` convergence is stated with the integral `∫ ‖X n - X_∞‖ dμ`, as in v1,
rather than with `eLpNorm`; the private lemmas below translate between the
two formulations.

## Main results

* `MeasureTheory.Submartingale.uniformIntegrable_tfae`: the three-way
  equivalence for submartingales.
* `MeasureTheory.Martingale.uniformIntegrable_tfae`: the four-way
  equivalence for martingales, including the conditional-expectation
  representation.
-/

@[expose] public section

open scoped MeasureTheory NNReal ENNReal Topology
open MeasureTheory Filter

namespace MeasureTheory

/-- Translates `L¹` convergence in the `eLpNorm` formulation to convergence of the real-valued
`L¹` integrals `∫ ‖f n - g‖ dμ → 0`. -/
private lemma tendsto_integral_norm_zero_of_tendsto_eLpNorm
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hint : ∀ n, Integrable (f n - g) μ)
    (h : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, ‖f n ω - g ω‖ ∂μ) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (h (ENNReal.ofReal (ε / 2)) (by positivity)).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  have hstep := hN n hn
  rw [eLpNorm_one_eq_lintegral_enorm (hint n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hint n)] at hstep
  have hle := (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hstep
  have : (fun ω : Ω => ‖f n ω - g ω‖) = fun x => ‖(f n - g) x‖ := by
    ext; simp [Pi.sub_apply]
  simp_rw [this]; linarith

/-- Converse of `tendsto_integral_norm_zero_of_tendsto_eLpNorm`: convergence of
`∫ ‖f n - g‖ dμ → 0` upgrades to `eLpNorm (f n - g) 1 μ → 0`. -/
private lemma tendsto_eLpNorm_of_tendsto_integral_norm_zero
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hint : ∀ n, Integrable (f n - g) μ)
    (h : Tendsto (fun n => ∫ ω, ‖f n ω - g ω‖ ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (nhds 0) := by
  have heq : (fun n => eLpNorm (f n - g) 1 μ) =
      (fun n => ENNReal.ofReal (∫ ω, ‖f n ω - g ω‖ ∂μ)) := by
    ext n
    rw [eLpNorm_one_eq_lintegral_enorm (hint n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    congr 1
  rw [heq, show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from by simp]
  exact ENNReal.tendsto_ofReal h

/-- If `f n → g` in `L¹` (in the `eLpNorm` formulation) and `g` is integrable, then the family
`f n` is uniformly `L¹`-bounded by some constant `C : ℝ≥0`. This supplies the boundedness
half of `UniformIntegrable` when assembling it from `unifIntegrable_of_tendsto_Lp`. -/
private lemma eLpNorm_bound_of_L1_tendsto
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : MemLp g 1 μ)
    (hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (nhds 0)) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm (f i) 1 μ ≤ C := by
  rw [ENNReal.tendsto_nhds_zero] at hL1
  obtain ⟨N, hN⟩ := (hL1 1 one_pos).exists_forall_of_atTop
  set Ctail : ℝ≥0 := 1 + (eLpNorm g 1 μ).toNNReal
  set Cinit : ℝ≥0 := (Finset.range N).sup fun n => (eLpNorm (f n) 1 μ).toNNReal
  refine ⟨Cinit ⊔ Ctail, fun i => ?_⟩
  by_cases hi : i < N
  · calc eLpNorm (f i) 1 μ
        = ↑((eLpNorm (f i) 1 μ).toNNReal) := (ENNReal.coe_toNNReal (hf i).ne).symm
      _ ≤ ↑Cinit := ENNReal.coe_le_coe.mpr
          (Finset.le_sup (f := fun n => (eLpNorm (f n) 1 μ).toNNReal)
            (Finset.mem_range.mpr hi))
      _ ≤ ↑(Cinit ⊔ Ctail) := ENNReal.coe_le_coe.mpr le_sup_left
  · simp only [not_lt] at hi
    calc eLpNorm (f i) 1 μ
        = eLpNorm ((f i - g) + g) 1 μ := by ring_nf
      _ ≤ eLpNorm (f i - g) 1 μ + eLpNorm g 1 μ := eLpNorm_add_le le_rfl
      _ ≤ 1 + eLpNorm g 1 μ := by gcongr; exact hN i hi
      _ = ↑(1 : ℝ≥0) + ↑((eLpNorm g 1 μ).toNNReal) := by
          rw [ENNReal.coe_toNNReal hg.ne, ENNReal.coe_one]
      _ = ↑Ctail := by push_cast; rfl
      _ ≤ ↑(Cinit ⊔ Ctail) := ENNReal.coe_le_coe.mpr le_sup_right

/-- **Equivalent conditions for uniform integrability of a submartingale.** Let $(\Omega, \mu)$ be
a probability space with a filtration $(\mathcal{F}_n)_{n \in \mathbb{N}}$, and let
$(X_n)_{n \in \mathbb{N}}$ be a real-valued submartingale with respect to $(\mathcal{F}_n)$ and
$\mu$. The following are equivalent:
1. $(X_n)$ is uniformly integrable.
2. There is an integrable $X_\infty$ such that $X_n \to X_\infty$ almost surely and
   $\int |X_n - X_\infty| \, d\mu \to 0$.
3. There is an integrable $X_\infty$ such that $\int |X_n - X_\infty| \, d\mu \to 0$. -/
theorem Submartingale.uniformIntegrable_tfae
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0}
    {X : ℕ → Ω → ℝ}
    (hsub : Submartingale X ℱ μ) :
    List.TFAE [
      UniformIntegrable X 1 μ,
      ∃ X_inf, Integrable X_inf μ ∧
        (∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop (nhds (X_inf ω))) ∧
        Filter.Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) Filter.atTop (nhds 0),
      ∃ X_inf, Integrable X_inf μ ∧
        Filter.Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) Filter.atTop (nhds 0)
    ] := by
  tfae_have 1 → 2 := by
    intro hUI
    obtain ⟨R, hR⟩ := hUI.2
    have hmeas : ∀ n, AEStronglyMeasurable (X n) μ := hUI.aestronglyMeasurable
    set X_inf := ℱ.limitProcess X μ
    have hint_lim : Integrable X_inf μ :=
      (Filtration.memLp_limitProcess_of_eLpNorm_bdd hmeas hR).integrable le_rfl
    have hae := hsub.ae_tendsto_limitProcess_of_uniformIntegrable hUI
    have hL1 := hsub.tendsto_eLpNorm_one_limitProcess hUI
    exact ⟨X_inf, hint_lim, hae,
      tendsto_integral_norm_zero_of_tendsto_eLpNorm
        (fun n => (hsub.integrable n).sub hint_lim) hL1⟩
  tfae_have 2 → 3 := by
    rintro ⟨X_inf, hint, _, hL1⟩
    exact ⟨X_inf, hint, hL1⟩
  tfae_have 3 → 1 := by
    rintro ⟨X_inf, hint, hL1⟩
    have hMemLp_n : ∀ n, MemLp (X n) 1 μ := fun n =>
      memLp_one_iff_integrable.mpr (hsub.integrable n)
    have hMemLp_inf : MemLp X_inf 1 μ := memLp_one_iff_integrable.mpr hint
    have hint_sub : ∀ n, Integrable (X n - X_inf) μ := fun n =>
      (hsub.integrable n).sub hint
    have heLpNorm := tendsto_eLpNorm_of_tendsto_integral_norm_zero hint_sub hL1
    exact ⟨unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top hMemLp_n hMemLp_inf heLpNorm,
      eLpNorm_bound_of_L1_tendsto hMemLp_n hMemLp_inf heLpNorm⟩
  tfae_finish

/-- **Equivalent conditions for uniform integrability of a martingale.** Let $(\Omega, \mu)$ be a
probability space with a filtration $(\mathcal{F}_n)_{n \in \mathbb{N}}$, and let
$(X_n)_{n \in \mathbb{N}}$ be a real-valued martingale with respect to $(\mathcal{F}_n)$ and $\mu$.
The following are equivalent:
1. $(X_n)$ is uniformly integrable.
2. There is an integrable $X_\infty$ such that $X_n \to X_\infty$ almost surely and
   $\int |X_n - X_\infty| \, d\mu \to 0$.
3. There is an integrable $X_\infty$ such that $\int |X_n - X_\infty| \, d\mu \to 0$.
4. There is an integrable $X_\infty$ such that $X_n = \mathbb{E}[X_\infty \mid \mathcal{F}_n]$
   almost surely for every $n$. -/
theorem Martingale.uniformIntegrable_tfae
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0}
    {X : ℕ → Ω → ℝ}
    (hmart : Martingale X ℱ μ) :
    List.TFAE [
      UniformIntegrable X 1 μ,
      ∃ X_inf, Integrable X_inf μ ∧
        (∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop (nhds (X_inf ω))) ∧
        Filter.Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) Filter.atTop (nhds 0),
      ∃ X_inf, Integrable X_inf μ ∧
        Filter.Tendsto (fun n => ∫ ω, ‖X n ω - X_inf ω‖ ∂μ) Filter.atTop (nhds 0),
      ∃ X_inf, Integrable X_inf μ ∧ ∀ n, X n =ᵐ[μ] μ[X_inf | ℱ n]
    ] := by
  have hsub := hmart.submartingale
  tfae_have 1 → 2 := by
    intro hUI
    obtain ⟨R, hR⟩ := hUI.2
    have hmeas : ∀ n, AEStronglyMeasurable (X n) μ := hUI.aestronglyMeasurable
    set X_inf := ℱ.limitProcess X μ
    have hint_lim : Integrable X_inf μ :=
      (Filtration.memLp_limitProcess_of_eLpNorm_bdd hmeas hR).integrable le_rfl
    have hae := hsub.ae_tendsto_limitProcess_of_uniformIntegrable hUI
    have hL1 := hsub.tendsto_eLpNorm_one_limitProcess hUI
    exact ⟨X_inf, hint_lim, hae,
      tendsto_integral_norm_zero_of_tendsto_eLpNorm
        (fun n => (hsub.integrable n).sub hint_lim) hL1⟩
  tfae_have 2 → 3 := by
    rintro ⟨X_inf, hint, _, hL1⟩
    exact ⟨X_inf, hint, hL1⟩
  tfae_have 3 → 4 := by
    rintro ⟨X_inf, hint, hL1⟩
    have hint_sub : ∀ n, Integrable (X n - X_inf) μ := fun n =>
      (hsub.integrable n).sub hint
    have heLpNorm := tendsto_eLpNorm_of_tendsto_integral_norm_zero hint_sub hL1
    exact ⟨X_inf, hint, fun n => hmart.eq_condExp_of_tendsto_eLpNorm hint heLpNorm n⟩
  tfae_have 4 → 1 := by
    rintro ⟨X_inf, hint, hce⟩
    exact (hint.uniformIntegrable_condExp_filtration).ae_eq (fun n => (hce n).symm)
  tfae_finish

end MeasureTheory
