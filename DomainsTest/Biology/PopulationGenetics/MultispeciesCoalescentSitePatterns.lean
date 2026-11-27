/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.MultispeciesCoalescentSitePatterns

/-!
# Tests for the site patterns of three species under the multispecies coalescent

The classification of sites into patterns, the pattern probabilities on a gene tree at zero
ages and their normalization, the gene-tree probabilities and total mass of the density at Zhu
and Yang's parameter values, Theorem 3 in the page's notation for `S₁ = ((A, B), C)`, and isml
on two count vectors, one of them Zhu and Yang's example `(4, 13, 12, 11, 50)`.
-/

@[expose] public section

open Real MeasureTheory

namespace MathlibExtTest.Biology.PopulationGenetics.MultispeciesCoalescent.SitePatterns

open MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent
open MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent.SitePatterns

/-! ### Site patterns -/

/-- The five patterns, read in the order `A`, `B`, `C`. -/
example : sitePattern 2 2 2 = .xxx ∧ sitePattern 0 0 1 = .xxy ∧ sitePattern 1 0 0 = .yxx ∧
    sitePattern 0 1 0 = .xyx ∧ sitePattern 0 1 2 = .xyz := by
  decide

/-- The cherry patterns of `S₁`, `S₂`, `S₃` are `xxy`, `yxx`, `xyx`. -/
example : RootedTriple.ab.cherryPattern = .xxy ∧ RootedTriple.bc.cherryPattern = .yxx ∧
    RootedTriple.ca.cherryPattern = .xyx :=
  ⟨rfl, rfl, rfl⟩

/-! ### Pattern probabilities on a gene tree -/

/-- At zero node ages the three sequences are identical. -/
example (G : RootedTriple) : patternProb G 0 0 .xxx = 1 ∧ patternProb G 0 0 .xyz = 0 := by
  rw [patternProb_eq, patternProb_eq]
  norm_num

/-- On `((A, B), C)` the patterns `yxx` and `xyx` are equally probable, for all ages. -/
example (t₀ t₁ : ℝ) : patternProb .ab t₀ t₁ .yxx = patternProb .ab t₀ t₁ .xyx := by
  rw [patternProb_eq, patternProb_eq]
  rfl

/-- The pattern probabilities on a gene tree sum to one. -/
example (t₀ t₁ : ℝ) : ∑ j, patternProb .bc t₀ t₁ j = 1 := sum_patternProb_eq_one _ _ _

/-! ### Zhu and Yang's parameter values -/

/-- The parameters `(τ₀, τ₁, θ₀, θ₁) = (0.02, 0.019, 0.01, 0.05)` of Zhu and Yang's tables. -/
def zyParams : Params where
  τ₀ := 0.02
  τ₁ := 0.019
  θ₀ := 0.01
  θ₁ := 0.05
  τ₁_pos := by norm_num
  τ₁_lt_τ₀ := by norm_num
  θ₀_pos := by norm_num
  θ₁_pos := by norm_num

/-- The internal branch of `zyParams` is `2 (τ₀ - τ₁) / θ₁ = 0.04` coalescent units, so the
gene tree `((A, B), C)` has probability `1 - (2/3) e^{-0.04}`. -/
example : ∫ t, mscDensity .ab zyParams .ab t = 1 - 2 / 3 * exp (-(1 / 25)) := by
  rw [integral_mscDensity]
  norm_num [zyParams]

/-- The density has total mass one. -/
example (S : RootedTriple) : ∑ G, ∫ t, mscDensity S zyParams G t = 1 := by
  simp only [integral_mscDensity, RootedTriple.univ_eq]
  cases S <;> simp <;> ring

/-- The marginal site-pattern probabilities are a probability distribution. -/
example (S : RootedTriple) (j : SitePattern) :
    0 < marginalPatternProb S zyParams j ∧ ∑ j, marginalPatternProb S zyParams j = 1 :=
  ⟨marginalPatternProb_pos S zyParams j, sum_marginalPatternProb S zyParams⟩

/-! ### Theorem 3 for `S₁ = ((A, B), C)` -/

/-- Part 1 in the page's notation: under `S₁`, `p̄₁ > p̄₂ = p̄₃`. -/
example (p : Params) :
    marginalPatternProb .ab p .yxx < marginalPatternProb .ab p .xxy ∧
      marginalPatternProb .ab p .yxx = marginalPatternProb .ab p .xyx :=
  ⟨(isml_selects_majority_site_pattern .ab).1 p .bc (by decide),
    (isml_selects_majority_site_pattern .ab).2.1 p .bc .ca (by decide) (by decide)⟩

/-- Zhu and Yang's counts `(x₀, …, x₄) = (4, 13, 12, 11, 50)`. -/
def zyCounts : SitePattern → ℕ
  | .xxx => 4
  | .xxy => 13
  | .yxx => 12
  | .xyx => 11
  | .xyz => 50

/-- Part 2: with `x₁ = 13 > max (12, 11)`, `S₁` beats `S₂` at every parameter value and every
isml estimate is `S₁`. -/
example : (∀ p, ismlLikelihood zyCounts .bc p < ismlLikelihood zyCounts .ab p) ∧
    ∀ S p, IsIsmlEstimate zyCounts S p → S = .ab := by
  obtain ⟨h, h'⟩ := (isml_selects_majority_site_pattern .ab).2.2 zyCounts (by decide)
  exact ⟨fun p => h p .bc (by decide), h'⟩

/-- The symmetric case: when `xyx` is the most frequent of the three patterns in which two
sequences agree, every isml estimate is `S₃ = ((C, A), B)`. -/
example (S : RootedTriple) (p : Params) (h : IsIsmlEstimate
    (fun | .xxx => 40 | .xxy => 3 | .yxx => 5 | .xyx => 7 | .xyz => 1) S p) : S = .ca :=
  h.eq (by decide)

end MathlibExtTest.Biology.PopulationGenetics.MultispeciesCoalescent.SitePatterns
