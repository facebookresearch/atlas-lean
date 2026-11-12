/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Identification in the sharp regression-discontinuity design

A forcing variable `X` assigns treatment deterministically at a cutoff `c`: units with `X ≥ c`
are treated. With potential outcomes `Y₀, Y₁` and observed outcome
`observed (X ⁻¹' Ici c) Y₀ Y₁`, the jump of the observed regression function `x ↦ E[Y | X = x]`
at `c` identifies the effect at the cutoff, `E[Y(1) - Y(0) | X = c]`, provided the potential-outcome
regression functions are continuous at `c` and units are observed arbitrarily close to `c` on
both sides.

`E[· | X = x]` is defined only for almost every `x` (under the law of `X`), so a pointwise limit
needs a model. Here `m₀, m₁ : ℝ → ℝ` are versions of `x ↦ E[Y(d) | X = x]`
(`μ[Y_d | σ(X)] =ᵐ m_d ∘ X`), and continuity at `c` fixes the cutoff effect as `m₁ c - m₀ c`.
The support condition says units are observed arbitrarily close to `c` on both sides: every
interval `(c, c + ε)` and `(c - ε, c)` has positive probability under the law of `X`. The main
theorem then holds for *every* version `r` of the observed regression function that has
one-sided limits at `c` (no measurability of `r` is needed), so the conclusion does not depend on
which version is chosen; `sharpRDMean c m₀ m₁` is one such version.

This is the population identification step only; local-polynomial estimation, bandwidth choice,
inference and the fuzzy design are not covered.

## Main definitions

* `sharpRDMean c m₀ m₁`: the observed regression function, `m₁` on `[c, ∞)` and `m₀` below `c`.

## Main results

* `condExp_observed_ae_eq_sharpRDMean`: `sharpRDMean c m₀ m₁ ∘ X` is a version of
  `μ[observed (X ⁻¹' Ici c) Y₀ Y₁ | σ(X)]`.
* `tendsto_sharpRDMean`: under continuity at `c`, its right and left limits are `m₁ c` and `m₀ c`.
* `sharpRD_identification`: for any version `r` with one-sided limits `Lr`, `Ll` at
  `c`, `Lr - Ll = m₁ c - m₀ c`.

## References

* J. Hahn, P. Todd, W. van der Klaauw, *Identification and estimation of treatment effects with a
  regression-discontinuity design*, Econometrica 69 (2001), 201–209, Theorem 1.
* G. W. Imbens, T. Lemieux, *Regression discontinuity designs: A guide to practice*,
  J. Econometrics 142 (2008), 615–635, §2.2 (eqs. (2.1)–(2.2), Assumption 2.1).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace MathlibExt.Probability.Statistics.RegressionDiscontinuity

open MathlibExt.Probability.Causality

/-- The conditional mean of the observed outcome in a sharp regression-discontinuity design with
cutoff `c`: treatment is `1{X ≥ c}`, so the observed regression function is `m₁ x` for `x ≥ c`
and `m₀ x` for `x < c`, where `m_d` is a version of `x ↦ E[Y(d) | X = x]`. -/
noncomputable def sharpRDMean (c : ℝ) (m₀ m₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if c ≤ x then m₁ x else m₀ x

/-- In a sharp RD design (treated event `{X ≥ c}`), `sharpRDMean c m₀ m₁ ∘ X` is a version of the
conditional expectation of the observed outcome given `X`. -/
theorem condExp_observed_ae_eq_sharpRDMean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (c : ℝ)
    {Y₀ Y₁ : Ω → ℝ} (hY₀ : Integrable Y₀ μ) (hY₁ : Integrable Y₁ μ) {m₀ m₁ : ℝ → ℝ}
    (h₀ : μ[Y₀ | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m₀ ∘ X)
    (h₁ : μ[Y₁ | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m₁ ∘ X) :
    μ[observed (X ⁻¹' Ici c) Y₀ Y₁ | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      sharpRDMean c m₀ m₁ ∘ X := by
  classical
  have hT : MeasurableSet (X ⁻¹' Ici c) := hX measurableSet_Ici
  have hT_comap : MeasurableSet[MeasurableSpace.comap X inferInstance] (X ⁻¹' Ici c) :=
    ⟨Ici c, measurableSet_Ici, rfl⟩
  have hY₁_int : Integrable ((X ⁻¹' Ici c).indicator Y₁) μ := hY₁.indicator hT
  have hY₀_int : Integrable ((X ⁻¹' Ici c)ᶜ.indicator Y₀) μ := hY₀.indicator hT.compl
  have h_add := MeasureTheory.condExp_add hY₁_int hY₀_int
    (MeasurableSpace.comap X inferInstance)
  have h_ind1 := MeasureTheory.condExp_indicator hY₁ hT_comap
  have h_ind0 := MeasureTheory.condExp_indicator hY₀ hT_comap.compl
  have h1' : (X ⁻¹' Ici c).indicator μ[Y₁ | MeasurableSpace.comap X inferInstance]
      =ᵐ[μ] (X ⁻¹' Ici c).indicator (m₁ ∘ X) := by
    filter_upwards [h₁] with ω hω
    by_cases hmem : ω ∈ X ⁻¹' Ici c
    · simp [hmem, hω]
    · simp [hmem]
  have h0' : (X ⁻¹' Ici c)ᶜ.indicator μ[Y₀ | MeasurableSpace.comap X inferInstance]
      =ᵐ[μ] (X ⁻¹' Ici c)ᶜ.indicator (m₀ ∘ X) := by
    filter_upwards [h₀] with ω hω
    by_cases hmem : ω ∈ (X ⁻¹' Ici c)ᶜ
    · simp [hmem, hω]
    · simp [hmem]
  have h_mid : μ[observed (X ⁻¹' Ici c) Y₀ Y₁ | MeasurableSpace.comap X inferInstance]
      =ᵐ[μ] (X ⁻¹' Ici c).indicator (m₁ ∘ X) + (X ⁻¹' Ici c)ᶜ.indicator (m₀ ∘ X) := by
    have := h_add.trans (h_ind1.add h_ind0)
    simpa [observed] using this.trans (h1'.add h0')
  refine h_mid.trans ?_
  filter_upwards with ω
  by_cases hc : c ≤ X ω
  · have hmem : ω ∈ X ⁻¹' Ici c := hc
    have hmemc : ω ∉ (X ⁻¹' Ici c)ᶜ := by simp [hmem]
    simp [sharpRDMean, hmem, hmemc, hc]
  · have hmem : ω ∉ X ⁻¹' Ici c := hc
    have hmemc : ω ∈ (X ⁻¹' Ici c)ᶜ := hmem
    simp [sharpRDMean, hmem, hmemc, hc]

/-- If `m₀` and `m₁` are continuous at the cutoff, the observed regression function
`sharpRDMean c m₀ m₁` has right limit `m₁ c` and left limit `m₀ c` at `c`. -/
theorem tendsto_sharpRDMean {c : ℝ} {m₀ m₁ : ℝ → ℝ} (hc₀ : ContinuousAt m₀ c)
    (hc₁ : ContinuousAt m₁ c) :
    Tendsto (sharpRDMean c m₀ m₁) (𝓝[>] c) (𝓝 (m₁ c)) ∧
      Tendsto (sharpRDMean c m₀ m₁) (𝓝[<] c) (𝓝 (m₀ c)) := by
  constructor
  · have hR : m₁ =ᶠ[𝓝[>] c] sharpRDMean c m₀ m₁ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [sharpRDMean]
      have : c ≤ x := le_of_lt hx
      simp [this]
    exact Filter.Tendsto.congr' hR (hc₁.tendsto.mono_left nhdsWithin_le_nhds)
  · have hL : m₀ =ᶠ[𝓝[<] c] sharpRDMean c m₀ m₁ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [sharpRDMean]
      have : ¬ c ≤ x := not_le_of_gt hx
      simp [this]
    exact Filter.Tendsto.congr' hL (hc₀.tendsto.mono_left nhdsWithin_le_nhds)

/-- **Identification in the sharp regression-discontinuity design** (Hahn, Todd and van der
Klaauw 2001; Imbens and Lemieux 2008, §2.2): treatment is `1{X ≥ c}`; `m_d` is a version of
`x ↦ E[Y(d) | X = x]`, continuous at `c`; units are observed arbitrarily close to `c` on both
sides (every one-sided neighborhood `(c, c + ε)`, `(c - ε, c)` has positive probability under
the law of `X`). Then for *any* version `r` of `x ↦ E[Y | X = x]` (`Y` the observed outcome)
that has one-sided limits at `c`, the jump `lim_{x↓c} r x - lim_{x↑c} r x` equals the cutoff
effect `m₁ c - m₀ c = E[Y(1) - Y(0) | X = c]`. -/
theorem sharpRD_identification {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) {c : ℝ} {Y₀ Y₁ : Ω → ℝ}
    (hY₀ : Integrable Y₀ μ) (hY₁ : Integrable Y₁ μ) {m₀ m₁ : ℝ → ℝ}
    (h₀ : μ[Y₀ | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m₀ ∘ X)
    (h₁ : μ[Y₁ | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m₁ ∘ X)
    (hc₀ : ContinuousAt m₀ c) (hc₁ : ContinuousAt m₁ c)
    (hsuppR : ∀ ε > 0, μ (X ⁻¹' Ioo c (c + ε)) ≠ 0)
    (hsuppL : ∀ ε > 0, μ (X ⁻¹' Ioo (c - ε) c) ≠ 0)
    {r : ℝ → ℝ}
    (hver : μ[observed (X ⁻¹' Ici c) Y₀ Y₁ | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      r ∘ X)
    {Lr Ll : ℝ} (hLr : Tendsto r (𝓝[>] c) (𝓝 Lr)) (hLl : Tendsto r (𝓝[<] c) (𝓝 Ll)) :
    Lr - Ll = m₁ c - m₀ c := by
  classical
  have h_obs := condExp_observed_ae_eq_sharpRDMean hX c hY₀ hY₁ h₀ h₁
  have hr_eq : r ∘ X =ᵐ[μ] sharpRDMean c m₀ m₁ ∘ X := hver.symm.trans h_obs
  have hfreqR : ∃ᶠ x in 𝓝[>] c, r x = m₁ x := by
    rw [(nhdsGT_basis c).frequently_iff]
    intro u hu
    have hε : 0 < u - c := sub_pos.mpr hu
    have hne := hsuppR (u - c) hε
    have hcu : c + (u - c) = u := by ring
    rw [hcu] at hne
    have hae : ∀ᵐ ω ∂μ.restrict (X ⁻¹' Ioo c u),
        (r ∘ X) ω = (sharpRDMean c m₀ m₁ ∘ X) ω :=
      MeasureTheory.ae_restrict_of_ae hr_eq
    obtain ⟨ω, hmem, heq⟩ :=
      MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hne hae
    have hxmem : X ω ∈ Ioo c u := hmem
    refine ⟨X ω, hxmem, ?_⟩
    simp only [Function.comp_apply] at heq
    have hle : c ≤ X ω := le_of_lt hxmem.1
    simp only [sharpRDMean, hle, ↓reduceIte] at heq
    exact heq
  have hfreqL : ∃ᶠ x in 𝓝[<] c, r x = m₀ x := by
    rw [(nhdsLT_basis c).frequently_iff]
    intro l hl
    have hε : 0 < c - l := sub_pos.mpr hl
    have hne := hsuppL (c - l) hε
    have hcl : c - (c - l) = l := by ring
    rw [hcl] at hne
    have hae : ∀ᵐ ω ∂μ.restrict (X ⁻¹' Ioo l c),
        (r ∘ X) ω = (sharpRDMean c m₀ m₁ ∘ X) ω :=
      MeasureTheory.ae_restrict_of_ae hr_eq
    obtain ⟨ω, hmem, heq⟩ :=
      MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hne hae
    have hxmem : X ω ∈ Ioo l c := hmem
    refine ⟨X ω, hxmem, ?_⟩
    simp only [Function.comp_apply] at heq
    have hnle : ¬ c ≤ X ω := not_le_of_gt hxmem.2
    simp only [sharpRDMean, hnle, ↓reduceIte] at heq
    exact heq
  have hR : Lr = m₁ c :=
    tendsto_nhds_unique_of_frequently_eq hLr (hc₁.tendsto.mono_left nhdsWithin_le_nhds) hfreqR
  have hL : Ll = m₀ c :=
    tendsto_nhds_unique_of_frequently_eq hLl (hc₀.tendsto.mono_left nhdsWithin_le_nhds) hfreqL
  rw [hR, hL]

end MathlibExt.Probability.Statistics.RegressionDiscontinuity
