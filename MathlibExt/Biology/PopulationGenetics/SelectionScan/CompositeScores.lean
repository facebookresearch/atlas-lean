/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FieldSimp

/-!
# Composite selection scores and the identifiability of a sweep location

Two results about statistics that combine many sites or many tests into one score.

**The composite of multiple signals (CMS, Grossman et al. 2010).** Several selection-scan
statistics are observed at a site. Conditionally on the hypothesis — the site is under
selection, or it is neutral — they are modelled as independent, each with its own positive
score function under each hypothesis. `CompositeModel` holds this data: a prior probability
of selection and the two families of positive score functions. The `posterior` below is the
normalized ratio of the products of these scores; it is a genuine Bayes posterior only
when each score function is a normalized density with respect to a common base measure
(the normalization hypothesis carried by `sum_joint_eq_one`). Bayes' rule then turns the
posterior odds into the prior odds times the product of the per-statistic Bayes factors,
which is exactly the CMS score; on the log scale the evidence is additive. The posterior is
a strictly increasing function of the score, so ranking sites by CMS and by posterior
probability agree.

**SweepFinder (Kim and Stephan 2002; Nielsen et al. 2005).** A sweep at position `x` of
strength `α > 0` leaves a lineage at position `y` unaffected with probability
`exp (-α |y - x|)`, so the frequency spectrum at `y` is the mixture of the neutral spectrum
with weight `escapeProb α x y` and the swept spectrum with the complementary weight. We prove
that the sweep parameters are identified by these per-site laws: distinct pairs `(x, α)` give
distinct escape functions, a mixture of two distinct laws determines its weight, and
consequently two parameter pairs producing the same per-site law at every position coincide.
This is the identifiability that the composite-likelihood surface of SweepFinder rests on.

## Main results

* `CompositeModel.posterior_mem_Ioo`, `CompositeModel.posterior_odds`,
  `CompositeModel.log_posterior_odds`: posterior odds are prior odds times the CMS score, and
  log posterior odds are log prior odds plus the sum of log Bayes factors.
* `CompositeModel.posterior_lt_posterior_of_cms_lt`: the posterior is strictly increasing in
  the score.
* `CompositeModel.sum_joint_eq_one`: with normalised component densities the joint model is a
  probability distribution on the observations.
* `escapeProb_eq_zero_iff`, `escapeProb_inj`: the sweep location and strength are determined
  by the escape probabilities (positivity of one strength parameter suffices).
* `mixture_weight_unique`: a mixture of two distinct laws determines its weight.
* `sweep_param_unique`: two sweep parameter pairs giving the same per-site law everywhere are
  equal.

## References

* S. R. Grossman, I. Shlyakhter, E. K. Karlsson, E. H. Byrne, S. Morales, G. Frieden,
  E. Hostetter, E. Angelino, M. Garber, O. Zuk, E. S. Lander, S. F. Schaffner and
  P. C. Sabeti, *A composite of multiple signals distinguishes causal variants in regions of
  positive selection*, Science 327 (2010), 883–886.
* Y. Kim and W. Stephan, *Detecting a local signature of genetic hitchhiking along a
  recombining chromosome*, Genetics 160 (2002), 765–777.
* R. Nielsen, S. Williamson, Y. Kim, M. J. Hubisz, A. G. Clark and C. Bustamante, *Genomic
  scans for selective sweeps using SNP data*, Genome Research 15 (2005), 1566–1575.
-/

open Real Finset

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.SelectionScan

/-! ### The composite of multiple signals -/

/-- A composite-score model (Grossman et al. 2010): a prior probability `prior` that the site
is under selection, and for each of the `k` component statistics a positive score function
`sel` under selection and `neut` under neutrality (unnormalized densities: only positivity is
assumed). Conditionally on the hypothesis the components are independent, which is what
makes the joint scores the products below. The Bayes/posterior reading of `posterior`
requires the additional normalization hypothesis of `sum_joint_eq_one`. -/
structure CompositeModel (k : ℕ) (σ : Fin k → Type*) where
  /-- The prior probability that the site is under selection. -/
  prior : ℝ
  /-- The prior is a probability strictly between `0` and `1`. -/
  prior_pos : 0 < prior
  /-- The prior is a probability strictly between `0` and `1`. -/
  prior_lt_one : prior < 1
  /-- The unnormalized score function of component `i` under selection. -/
  sel : ∀ i, σ i → ℝ
  /-- The unnormalized score function of component `i` under neutrality. -/
  neut : ∀ i, σ i → ℝ
  /-- Component score functions under selection are positive. -/
  sel_pos : ∀ i x, 0 < sel i x
  /-- Component score functions under neutrality are positive. -/
  neut_pos : ∀ i x, 0 < neut i x

namespace CompositeModel

variable {k : ℕ} {σ : Fin k → Type*} (M : CompositeModel k σ) (x : ∀ i, σ i)

/-- The Bayes factor of component `i` at the observed value: the ratio of its score
function under selection to its score function under neutrality. -/
noncomputable def bayesFactor (i : Fin k) (y : σ i) : ℝ := M.sel i y / M.neut i y

/-- The CMS score: the product of the component Bayes factors. -/
noncomputable def cms : ℝ := ∏ i, M.bayesFactor i (x i)

/-- The normalized composite score: the normalized ratio of the products of the
component score functions. This is the posterior probability of selection given the
observed component values when the score functions are normalized densities
(see `sum_joint_eq_one` for the normalization hypothesis). -/
noncomputable def posterior : ℝ :=
  M.prior * (∏ i, M.sel i (x i)) /
    (M.prior * (∏ i, M.sel i (x i)) + (1 - M.prior) * ∏ i, M.neut i (x i))

/-- Every component Bayes factor is positive. -/
theorem bayesFactor_pos (i : Fin k) (y : σ i) : 0 < M.bayesFactor i y :=
  div_pos (M.sel_pos i y) (M.neut_pos i y)

theorem cms_pos : 0 < M.cms x :=
  Finset.prod_pos fun i _ => M.bayesFactor_pos i (x i)

private lemma selProd_pos : 0 < ∏ i, M.sel i (x i) :=
  Finset.prod_pos fun i _ => M.sel_pos i (x i)

private lemma neutProd_pos : 0 < ∏ i, M.neut i (x i) :=
  Finset.prod_pos fun i _ => M.neut_pos i (x i)

private lemma denom_pos :
    0 < M.prior * (∏ i, M.sel i (x i)) + (1 - M.prior) * ∏ i, M.neut i (x i) := by
  have h1 := M.prior_pos
  have h2 := M.prior_lt_one
  have hP := selProd_pos M x
  have hQ := neutProd_pos M x
  have : 0 < 1 - M.prior := by linarith
  positivity

/-- The CMS score is the ratio of the two joint densities. -/
theorem cms_eq_div : M.cms x = (∏ i, M.sel i (x i)) / ∏ i, M.neut i (x i) := by
  rw [cms, ← Finset.prod_div_distrib]
  rfl

theorem posterior_mem_Ioo : M.posterior x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hP := selProd_pos M x
  have hQ := neutProd_pos M x
  have hD := denom_pos M x
  have h1 := M.prior_pos
  have h2 : 0 < 1 - M.prior := by linarith [M.prior_lt_one]
  constructor
  · exact div_pos (by positivity) hD
  · rw [posterior, div_lt_one hD]
    nlinarith

/-- Bayes-rule identity for conditionally independent components: the posterior odds of
selection are the prior odds times the CMS score. This is an algebraic identity for the
normalized score; it is a genuine Bayes rule only under the normalization hypothesis of
`sum_joint_eq_one`. -/
theorem posterior_odds :
    M.posterior x / (1 - M.posterior x) = M.prior / (1 - M.prior) * M.cms x := by
  have hP := selProd_pos M x
  have hQ := neutProd_pos M x
  have hD := denom_pos M x
  have h1 := M.prior_pos
  have h2 : 0 < 1 - M.prior := by linarith [M.prior_lt_one]
  have hsub : 1 - M.posterior x
      = (1 - M.prior) * (∏ i, M.neut i (x i)) /
        (M.prior * (∏ i, M.sel i (x i)) + (1 - M.prior) * ∏ i, M.neut i (x i)) := by
    rw [posterior]
    field_simp
    ring
  rw [hsub, posterior, cms_eq_div]
  rw [div_div_div_comm]
  field_simp

/-- On the log scale the evidence is additive: the log posterior odds are the log prior odds
plus the sum of the log Bayes factors of the component statistics. -/
theorem log_posterior_odds :
    log (M.posterior x / (1 - M.posterior x))
      = log (M.prior / (1 - M.prior)) + ∑ i, log (M.bayesFactor i (x i)) := by
  have h1 := M.prior_pos
  have h2 : 0 < 1 - M.prior := by linarith [M.prior_lt_one]
  have hcms := cms_pos M x
  rw [posterior_odds, Real.log_mul (by positivity) hcms.ne', cms,
    Real.log_prod (s := Finset.univ) (f := fun i => M.bayesFactor i (x i))
      fun i _ => (M.bayesFactor_pos i (x i)).ne']

/-- The posterior probability is a strictly increasing function of the CMS score, so the two
rankings of sites agree. -/
theorem posterior_lt_posterior_of_cms_lt (y : ∀ i, σ i) (h : M.cms x < M.cms y) :
    M.posterior x < M.posterior y := by
  have h1 := M.prior_pos
  have h2 : 0 < 1 - M.prior := by linarith [M.prior_lt_one]
  have hform : ∀ z : (∀ i, σ i),
      M.posterior z = 1 / (1 + (1 - M.prior) / M.prior / M.cms z) := by
    intro z
    have hP := selProd_pos M z
    have hQ := neutProd_pos M z
    have hD := denom_pos M z
    rw [posterior, cms_eq_div]
    field_simp
  have hx := cms_pos M x
  have hy := cms_pos M y
  rw [hform x, hform y]
  have hlt : (1 - M.prior) / M.prior / M.cms y < (1 - M.prior) / M.prior / M.cms x :=
    div_lt_div_of_pos_left (by positivity) hx h
  have hpos : 0 < 1 + (1 - M.prior) / M.prior / M.cms y := by positivity
  exact one_div_lt_one_div_of_lt hpos (by linarith)

/-- The model is a probability model: with normalised component score functions (each a
density with respect to a common base measure), the joint distribution of the
observations sums to one. This is the validity hypothesis that makes `posterior` a
genuine Bayes posterior. -/
theorem sum_joint_eq_one [∀ i, Fintype (σ i)]
    (hsel : ∀ i, ∑ y, M.sel i y = 1) (hneut : ∀ i, ∑ y, M.neut i y = 1) :
    ∑ z : (∀ i, σ i),
      (M.prior * (∏ i, M.sel i (z i)) + (1 - M.prior) * ∏ i, M.neut i (z i)) = 1 := by
  have key : ∀ g : (∀ i, σ i → ℝ),
      (∏ i, ∑ y, g i y) = ∑ z : (∀ i, σ i), ∏ i, g i (z i) := by
    intro g
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr ?_ fun z _ => rfl
    simp [Fintype.piFinset_univ]
  have h1 : ∑ z : (∀ i, σ i), ∏ i, M.sel i (z i) = 1 := by
    rw [← key M.sel]
    simp [hsel]
  have h2 : ∑ z : (∀ i, σ i), ∏ i, M.neut i (z i) = 1 := by
    rw [← key M.neut]
    simp [hneut]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2]
  ring

end CompositeModel

/-! ### Identifiability of a sweep location and strength -/

/-- The probability that a lineage at position `y` escapes a sweep located at `x`, with
compound strength parameter `α > 0`: `1 - exp (-α |y - x|)` (Kim and Stephan 2002;
Nielsen et al. 2005). The parameter `α` is proportional to the recombination rate per unit
distance divided by the selection coefficient. -/
noncomputable def escapeProb (α x y : ℝ) : ℝ := 1 - exp (-α * |y - x|)

theorem escapeProb_mem_Ico {α : ℝ} (hα : 0 ≤ α) (x y : ℝ) :
    escapeProb α x y ∈ Set.Ico (0 : ℝ) 1 := by
  have habs : 0 ≤ |y - x| := abs_nonneg _
  constructor
  · have : exp (-α * |y - x|) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    simpa [escapeProb] using this
  · have : 0 < exp (-α * |y - x|) := exp_pos _
    simpa [escapeProb] using this

/-- No lineage escapes at the swept site itself, and nowhere else. -/
theorem escapeProb_eq_zero_iff {α : ℝ} (hα : 0 < α) (x y : ℝ) :
    escapeProb α x y = 0 ↔ y = x := by
  rw [escapeProb, sub_eq_zero]
  constructor
  · intro h
    have h0 : -α * |y - x| = 0 := by
      have := congrArg Real.log h.symm
      simpa using this
    have : |y - x| = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 (neg_ne_zero.mpr hα.ne')
      · exact h1
    have := abs_eq_zero.mp this
    linarith [sub_eq_zero.mp this]
  · intro h
    subst h
    simp

/-- The escape-probability profile determines the sweep location and its strength. Positivity
of one of the two strength parameters is enough: the location is the unique zero of that
profile, and the strengths then agree by injectivity of `exp`. -/
theorem escapeProb_inj {α₁ α₂ x₁ x₂ : ℝ} (hα₂ : 0 < α₂)
    (h : ∀ y, escapeProb α₁ x₁ y = escapeProb α₂ x₂ y) : x₁ = x₂ ∧ α₁ = α₂ := by
  have hx : x₁ = x₂ := by
    have h0 : escapeProb α₂ x₂ x₁ = 0 := by
      rw [← h x₁, escapeProb]
      simp
    exact ((escapeProb_eq_zero_iff hα₂ x₂ x₁).mp h0)
  subst hx
  refine ⟨rfl, ?_⟩
  have h1 := h (x₁ + 1)
  simp only [escapeProb, add_sub_cancel_left, abs_one, mul_one, sub_right_inj] at h1
  have := Real.exp_injective h1
  linarith

/-- A mixture of two distinct laws determines its mixing weight. -/
theorem mixture_weight_unique {β : Type*} {f g : β → ℝ} (hfg : f ≠ g) {p q : ℝ}
    (h : ∀ b, p * f b + (1 - p) * g b = q * f b + (1 - q) * g b) : p = q := by
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hfg
  have hzero : (p - q) * (f b - g b) = 0 := by linarith [h b]
  rcases mul_eq_zero.mp hzero with h1 | h1
  · linarith
  · exact absurd (sub_eq_zero.mp h1) hb

/-- Identifiability of the sweep parameters from the per-site frequency spectra. If the
neutral spectrum `f` and the post-sweep spectrum `g` differ, and two sweep parameter pairs
give the same mixture at every position, then the parameters coincide. This is what the
composite likelihood of SweepFinder maximises over. -/
theorem sweep_param_unique {β : Type*} {f g : β → ℝ} (hfg : f ≠ g) {α₁ α₂ x₁ x₂ : ℝ}
    (hα₂ : 0 < α₂)
    (h : ∀ y b, escapeProb α₁ x₁ y * f b + (1 - escapeProb α₁ x₁ y) * g b
      = escapeProb α₂ x₂ y * f b + (1 - escapeProb α₂ x₂ y) * g b) :
    x₁ = x₂ ∧ α₁ = α₂ := by
  refine escapeProb_inj hα₂ fun y => ?_
  exact mixture_weight_unique hfg (fun b => h y b)

end MathlibExt.Biology.PopulationGenetics.SelectionScan
