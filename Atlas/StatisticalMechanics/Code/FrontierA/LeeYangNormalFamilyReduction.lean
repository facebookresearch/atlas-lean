/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Code.FrontierA.LeeYangThermodynamicPrereq

open Filter Set Topology

namespace StatMech.FrontierA




def IsLocallyUniformlySequentiallyPrecompact
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) g atTop U




theorem tendstoLocallyUniformlyOn_of_subsequential_limits_unique
    (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U)
    (hcompact : IsLocallyUniformlySequentiallyPrecompact F U)
    (hunique : ∀ (φ ψ : ℕ → ℕ) (f : ℂ → ℂ),
      StrictMono φ → StrictMono ψ →
      TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop U →
      Set.EqOn f g U) :
    TendstoLocallyUniformlyOn F g atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  by_contra hnot
  have hfrequent : ∃ᶠ n in atTop,
      ¬ ∀ x ∈ K, dist (g x) (F n x) < epsilon := not_eventually.mp hnot
  obtain ⟨φ, hφmono, hφbad⟩ := extraction_of_frequently_atTop hfrequent
  obtain ⟨ψ, hψmono, f, hf⟩ := hcompact φ hφmono
  have hfg : Set.EqOn f g U := hunique φ ψ f hφmono hψmono hf
  have hfunif : TendstoUniformlyOn (fun n => F (φ (ψ n))) f atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hfunif
  obtain ⟨n, hn⟩ := (hfunif epsilon hepsilon).exists
  have hbad := hφbad (ψ n)
  push Not at hbad
  obtain ⟨x, hxK, hxbd⟩ := hbad
  have hxU : x ∈ U := hKU hxK
  have hclose := hn x hxK
  rw [hfg hxU] at hclose
  exact (not_lt_of_ge hxbd) hclose




theorem holomorphic_subsequentialLimits_unique_of_anchor
    (F : ℕ → ℂ → ℂ) (U anchor : Set ℂ) (z₀ : ℂ)
    (anchorLimit : ℂ → ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hanchorU : anchor ⊆ U)
    (hanchorAccum : ∃ᶠ z in nhdsWithin z₀ ({z₀}ᶜ), z ∈ anchor)
    (hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U)
    (hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)))
    (φ₁ ψ₁ φ₂ ψ₂ : ℕ → ℕ) (f g : ℂ → ℂ)
    (hφ₁ : StrictMono φ₁) (hψ₁ : StrictMono ψ₁)
    (hφ₂ : StrictMono φ₂) (hψ₂ : StrictMono ψ₂)
    (hf : TendstoLocallyUniformlyOn (fun n => F (φ₁ (ψ₁ n))) f atTop U)
    (hg : TendstoLocallyUniformlyOn (fun n => F (φ₂ (ψ₂ n))) g atTop U) :
    Set.EqOn f g U := by
  have hfDiff : DifferentiableOn ℂ f U :=
    hf.differentiableOn
      (Eventually.of_forall (fun n => hholomorphic (φ₁ (ψ₁ n)))) hUopen
  have hgDiff : DifferentiableOn ℂ g U :=
    hg.differentiableOn
      (Eventually.of_forall (fun n => hholomorphic (φ₂ (ψ₂ n)))) hUopen
  have hfAnalytic : AnalyticOnNhd ℂ f U := hfDiff.analyticOnNhd hUopen
  have hgAnalytic : AnalyticOnNhd ℂ g U := hgDiff.analyticOnNhd hUopen
  apply hfAnalytic.eqOn_of_preconnected_of_frequently_eq hgAnalytic
    hUconnected hz₀
  apply hanchorAccum.mono
  intro z hzanchor
  have hzU : z ∈ U := hanchorU hzanchor
  have hfAt := hf.tendsto_at hzU
  have hgAt := hg.tendsto_at hzU
  have hφψ₁ : Tendsto (φ₁ ∘ ψ₁) atTop atTop :=
    (hφ₁.comp hψ₁).tendsto_atTop
  have hφψ₂ : Tendsto (φ₂ ∘ ψ₂) atTop atTop :=
    (hφ₂.comp hψ₂).tendsto_atTop
  have hfAnchor : f z = anchorLimit z :=
    tendsto_nhds_unique hfAt ((hanchorLimit z hzanchor).comp hφψ₁)
  have hgAnchor : g z = anchorLimit z :=
    tendsto_nhds_unique hgAt ((hanchorLimit z hzanchor).comp hφψ₂)
  exact hfAnchor.trans hgAnchor.symm





theorem montelVitali_of_locallyUniform_precompact
    (F : ℕ → ℂ → ℂ) (U anchor : Set ℂ) (z₀ : ℂ)
    (anchorLimit : ℂ → ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hanchorU : anchor ⊆ U)
    (hanchorAccum : ∃ᶠ z in nhdsWithin z₀ ({z₀}ᶜ), z ∈ anchor)
    (hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U)
    (hcompact : IsLocallyUniformlySequentiallyPrecompact F U)
    (hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z))) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn F g atTop U ∧
      DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (deriv ∘ F) (deriv g) atTop U := by
  obtain ⟨ψ, hψmono, g, hg⟩ := hcompact id strictMono_id
  have hfull : TendstoLocallyUniformlyOn F g atTop U :=
    tendstoLocallyUniformlyOn_of_subsequential_limits_unique F g U hUopen hcompact
      (fun φ₂ ψ₂ f hφ₂ hψ₂ hf =>
        holomorphic_subsequentialLimits_unique_of_anchor F U anchor z₀
          anchorLimit hUopen hUconnected hz₀ hanchorU hanchorAccum
          hholomorphic hanchorLimit φ₂ ψ₂ id ψ f g hφ₂ hψ₂
          strictMono_id hψmono hf hg)
  have hgDiff : DifferentiableOn ℂ g U :=
    hfull.differentiableOn (Eventually.of_forall hholomorphic) hUopen
  refine ⟨g, hfull, hgDiff, ?_⟩
  exact hfull.deriv (Eventually.of_forall hholomorphic) hUopen

end StatMech.FrontierA
