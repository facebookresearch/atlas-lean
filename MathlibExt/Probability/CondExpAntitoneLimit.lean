/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!

# Identifying an a.e. limit of conditional expectations

If the conditional expectations of an integrable function `g` with respect to
a sequence of sub-σ-algebras `m n` converge almost everywhere to an
integrable function `h` that is measurable with respect to the intersection
`⨅ n, m n`, then `h` is the conditional expectation of `g` given that
intersection. The proof goes through `L¹` convergence (Vitali's theorem:
uniform integrability of the conditional expectations plus convergence in
measure) and the characterization of conditional expectation by set integrals.

Source: `v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean`
(`condExp_antitone_limit_eq`, fully proved there), supporting Durrett's
Lecture 29 backwards-martingale material. That v1 lemma was the key step
for identifying the limit in Lévy's downward theorem; the convergence
itself (Lévy's downward theorem and backwards-martingale convergence) was
ported in batch 35 (#442) via a different route and is *not* restated here.

## Main results

- `MathlibExt.Probability.CondExpAntitoneLimit.tendsto_eLpNorm_condExp_sub_of_ae_tendsto`:
  `L¹` convergence of `μ[g | m n]` to an identified a.e. limit `h`.
- `MathlibExt.Probability.CondExpAntitoneLimit.condExp_antitone_limit_eq`:
  identification `h =ᵐ[μ] μ[g | ⨅ n, m n]`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology MeasureTheory

namespace MathlibExt.Probability.CondExpAntitoneLimit

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Almost-everywhere convergent conditional expectations converge in L¹.** Let $\mu$ be a finite
measure on a measurable space $(\Omega, \mathcal{F})$, let $(\mathcal{G}_n)_{n \in \mathbb{N}}$ be
a sequence of sub-σ-algebras of $\mathcal{F}$, let $g : \Omega \to \mathbb{R}$ be integrable,
and write $\mu[g \mid \mathcal{G}_n]$ for the conditional expectation of $g$ given
$\mathcal{G}_n$ with respect to $\mu$. If $h : \Omega \to \mathbb{R}$ is integrable and
$\mu[g \mid \mathcal{G}_n] \to h$ $\mu$-almost everywhere as $n \to \infty$, then
$\int_\Omega |\mu[g \mid \mathcal{G}_n] - h| \, d\mu \to 0$ as $n \to \infty$.

This is Vitali's theorem applied to the uniformly integrable family of conditional expectations of
a single integrable function. -/
theorem tendsto_eLpNorm_condExp_sub_of_ae_tendsto [IsFiniteMeasure μ]
    (g : Ω → ℝ) (m : ℕ → MeasurableSpace Ω)
    (hm_le : ∀ n, m n ≤ m0)
    (hg : Integrable g μ)
    (h : Ω → ℝ)
    (hh_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | m n]) ω) atTop (𝓝 (h ω)))
    (hh_int : Integrable h μ) :
    Tendsto (fun n => eLpNorm ((μ[g | m n]) - h) 1 μ) atTop (𝓝 0) := by
  have hui : UniformIntegrable (fun n => (μ[g | m n] : Ω → ℝ)) 1 μ :=
    hg.uniformIntegrable_condExp hm_le
  have haem : ∀ n, AEStronglyMeasurable (fun ω => (μ[g | m n]) ω) μ :=
    fun n => (stronglyMeasurable_condExp (m := m n)).aestronglyMeasurable.mono (hm_le n)
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top haem
    (memLp_one_iff_integrable.mpr hh_int) hui.1
    (tendstoInMeasure_of_tendsto_ae haem hh_ae)

/-- **Identifying the a.e. limit of conditional expectations.** Let $\mu$ be a finite measure on a
measurable space $(\Omega, \mathcal{F})$, let $(\mathcal{G}_n)_{n \in \mathbb{N}}$ be any
sequence of sub-σ-algebras of $\mathcal{F}$ (not assumed monotone), and let
$g : \Omega \to \mathbb{R}$ be integrable. Write $\mu[g \mid \mathcal{G}]$ for the conditional
expectation of $g$ given a sub-σ-algebra $\mathcal{G}$ with respect to $\mu$, and
$\mathcal{G}_\infty = \bigcap_n \mathcal{G}_n$. Suppose $h : \Omega \to \mathbb{R}$ is
integrable, strongly measurable with respect to $\mathcal{G}_\infty$, and
$\mu[g \mid \mathcal{G}_n](\omega) \to h(\omega)$ as $n \to \infty$ for $\mu$-almost every
$\omega$. Then $h = \mu[g \mid \mathcal{G}_\infty]$ $\mu$-almost everywhere. -/
theorem condExp_antitone_limit_eq [IsFiniteMeasure μ]
    (g : Ω → ℝ) (m : ℕ → MeasurableSpace Ω)
    (hm_le : ∀ n, m n ≤ m0)
    (hg : Integrable g μ)
    (h : Ω → ℝ)
    (hh_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | m n]) ω) atTop (𝓝 (h ω)))
    (hh_int : Integrable h μ)
    (hh_meas : StronglyMeasurable[⨅ n, m n] h) :
    h =ᵐ[μ] μ[g | ⨅ n, m n] := by
  have hm_inf_le : ⨅ n, m n ≤ m0 := le_trans (iInf_le _ 0) (hm_le 0)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm_inf_le hg
    (fun s _ _ => hh_int.integrableOn) ?_ hh_meas.aestronglyMeasurable
  intro s hs hμs
  have hs_n : ∀ n, MeasurableSet[m n] s := fun n => (iInf_le m n) s hs
  have hint_eq : ∀ n, ∫ x in s, (μ[g | m n]) x ∂μ = ∫ x in s, g x ∂μ :=
    fun n => setIntegral_condExp (hm_le n) hg (hs_n n)
  have hL1 : Tendsto (fun n => eLpNorm ((μ[g | m n]) - h) 1 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_condExp_sub_of_ae_tendsto g m hm_le hg h hh_ae hh_int
  have hsetint := tendsto_setIntegral_of_L1' h
    (Filter.Eventually.of_forall fun n => integrable_condExp) hL1 s
  exact tendsto_nhds_unique (hsetint.congr hint_eq) tendsto_const_nhds

end MathlibExt.Probability.CondExpAntitoneLimit
