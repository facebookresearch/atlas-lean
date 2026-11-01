/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonGamma

/-!
# Gene constraint scores: LOEUF and pLI

A gene has `o` observed loss-of-function (LoF) variants and `E > 0` expected under neutrality;
the model is `o ~ Poisson(γ E)` with `γ` the observed/expected ratio.

**LOEUF** (Karczewski et al. 2020) is the upper end of a 90% interval for `γ` under this
Poisson model. Two readings of that interval agree exactly. Normalizing the likelihood of `o`
in `γ` (a flat-prior posterior, which is how the gnomAD methods library evaluates it, on a
finite grid of ratios) gives the Gamma law of shape `o + 1` and rate `E`
(`flatPosterior_density`); by Poisson–Gamma duality its upper `α`-quantile is exactly Garwood's
bound divided by `E` (`gammaMeasure_real_Iic_oeUpper`). So the score is the exact one-sided
`1 - α` upper confidence bound and covers the true `γ` with probability at least `1 - α`
(`oeUpper_coverage`). The finite grid of the implementation is not modeled.

**pLI** (Lek et al. 2016) is the posterior probability of the most depleted class in a
mixture of Poisson classes `o ~ Poisson(λ_c E)` with prior weights `π_c` (in the paper: null,
recessive, haploinsufficient, with fitted rates). For every prior and any rates, the posterior
of the class with the smallest rate is antitone in `o` (`classPosterior_antitone`), strictly
when another class with positive weight has a larger rate. The class rates themselves are
parameters here; the paper's fitted values are not used. The EM fit of the weights is in
`CSLibExt/Bioinformatics/StatisticalGenetics/PoissonClassEM.lean`.

## Main results

* `flatPosterior_density`: likelihood `×` flat prior, normalized, is `gammaPDFReal (o + 1) E`.
* `gammaMeasure_real_Iic_oeUpper`: the flat posterior puts mass `1 - α` below
  `oeUpper α E o = u_α(o) / E`.
* `oeUpper_coverage`: exact coverage `P(γ ≤ oeUpper α E o) ≥ 1 - α`.
* `loeuf_zero`: with no observed LoF variants, `LOEUF = log 20 / E`.
* `oeUpper_strictMono`, `oeUpper_strictAntiOn`: increasing in `o`, decreasing in `E`.
* `classPosterior_antitone`, `classPosterior_strictAnti`: pLI decreases with the observed
  count.

## References

* K. J. Karczewski et al., *The mutational constraint spectrum quantified from variation in
  141,456 humans*, Nature 581 (2020), 434–443.
* M. Lek et al., *Analysis of protein-coding genetic variation in 60,706 humans*, Nature 536
  (2016), 285–291.
* F. Garwood, *Fiducial limits for the Poisson distribution*, Biometrika 28 (1936), 437–442.
-/

@[expose] public section

open Real Finset MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal Nat

namespace MathlibExt.Biology.StatisticalGenetics.GeneConstraint

/-- The Poisson likelihood `e^{-μ} μ^o / (o!)` of an observed count `o` at mean `μ`. -/
noncomputable def poissonLik (μ : ℝ) (o : ℕ) : ℝ := exp (-μ) * μ ^ o / (o ! : ℝ)

/-- The likelihood is positive at a positive mean. -/
theorem poissonLik_pos {μ : ℝ} (hμ : 0 < μ) (o : ℕ) : 0 < poissonLik μ o := by
  unfold poissonLik; positivity

/-! ### LOEUF -/

/-- **Flat-prior posterior of `γ`**: the likelihood `γ ↦ P(o | Poisson(γ E))` times `E` is the
Gamma density of shape `o + 1` and rate `E`. For `E > 0` that density integrates to one, so `E`
is the normalizing constant of the flat-prior posterior (the identity itself is algebraic and
holds for every real `E`). -/
theorem flatPosterior_density (E : ℝ) {γ : ℝ} (hγ : 0 ≤ γ) (o : ℕ) :
    E * poissonLik (γ * E) o = gammaPDFReal (o + 1) E γ := by
  have hG : Gamma ((o : ℝ) + 1) = (o ! : ℝ) := Real.Gamma_nat_eq_factorial o
  simp only [gammaPDFReal, hγ, ↓reduceIte]
  rw [hG, add_sub_cancel_right, Real.rpow_natCast,
    show ((o : ℝ) + 1) = ((o + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, poissonLik]
  rw [mul_pow, pow_succ, mul_comm γ E]
  ring

/-- The upper confidence bound for the observed/expected ratio at level `α`:
`u_α(o) / E`, with `u_α` Garwood's bound for the Poisson mean. -/
noncomputable def oeUpper (α E : ℝ) (o : ℕ) : ℝ := garwoodUpper α o / E

/-- **LOEUF**: the upper end of the 90% interval, `oeUpper (1/20)`. -/
noncomputable def loeuf (E : ℝ) (o : ℕ) : ℝ := oeUpper (1 / 20) E o

/-- **The flat-prior posterior quantile is Garwood's bound**: the Gamma(`o + 1`, `E`) posterior
puts mass exactly `1 - α` below `oeUpper α E o`. -/
theorem gammaMeasure_real_Iic_oeUpper {α E : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hE : 0 < E)
    (o : ℕ) : (gammaMeasure (o + 1) E).real (Iic (oeUpper α E o)) = 1 - α := by
  have := isProbabilityMeasure_gammaMeasure (a := (o : ℝ) + 1) (by positivity) hE
  have hu := garwoodUpper_pos hα0 hα1 o
  rw [← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi, oeUpper,
    gammaMeasure_real_Ioi o hE (div_nonneg hu.le hE.le), mul_div_cancel₀ _ hE.ne',
    poissonCDF_garwoodUpper hα0 hα1]

/-- **Exact coverage**: for every true ratio `γ ≥ 0` and `E > 0`, when `o ~ Poisson(γ E)`,
`P(γ ≤ oeUpper α E o) ≥ 1 - α`. -/
theorem oeUpper_coverage {α E : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hE : 0 < E) (γ : ℝ≥0) :
    1 - α ≤ (poissonMeasure (γ * ⟨E, hE.le⟩)).real {o | (γ : ℝ) ≤ oeUpper α E o} := by
  have h := garwoodUpper_coverage (γ * ⟨E, hE.le⟩) hα0 hα1
  have hset : {o | (γ : ℝ) ≤ oeUpper α E o} =
      {k | ((γ * ⟨E, hE.le⟩ : ℝ≥0) : ℝ) ≤ garwoodUpper α k} := by
    ext o
    simp only [Set.mem_ofPred_eq, oeUpper, le_div_iff₀ hE]
    rfl
  rwa [hset]

/-- With no observed variants the bound is `log (1 / α) / E`. -/
theorem oeUpper_zero {α E : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    oeUpper α E 0 = log (1 / α) / E := by
  rw [oeUpper, garwoodUpper_zero hα0 hα1]

/-- **LOEUF of a gene with no observed LoF variants** is `log 20 / E`. -/
theorem loeuf_zero (E : ℝ) : loeuf E 0 = log 20 / E := by
  rw [loeuf, oeUpper_zero (by norm_num) (by norm_num)]
  norm_num

/-- The bound is strictly increasing in the observed count. -/
theorem oeUpper_strictMono {α E : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hE : 0 < E) :
    StrictMono (oeUpper α E) := fun _ _ h =>
  div_lt_div_of_pos_right (garwoodUpper_strictMono hα0 hα1 h) hE

/-- The bound is strictly decreasing in the expected count `E > 0`. -/
theorem oeUpper_strictAntiOn {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (o : ℕ) :
    StrictAntiOn (fun E => oeUpper α E o) (Ioi 0) := fun _ ha _ _ h =>
  div_lt_div_of_pos_left (garwoodUpper_pos hα0 hα1 o) ha h

/-! ### pLI -/

variable {ι : Type*} [Fintype ι]

/-- The posterior probability of class `c` for a gene with `o` observed and `E` expected LoF
variants, in the Poisson mixture with prior weights `w` and class rates `rate`:
`w_c P(o | rate_c E) / ∑_{c'} w_{c'} P(o | rate_{c'} E)`. pLI is this at the class with the smallest
rate. -/
noncomputable def classPosterior (w rate : ι → ℝ) (E : ℝ) (o : ℕ) (c : ι) : ℝ :=
  w c * poissonLik (rate c * E) o / ∑ c', w c' * poissonLik (rate c' * E) o

/-- The class posteriors sum to one. -/
theorem sum_classPosterior {w rate : ι → ℝ} {E : ℝ} (hw : ∀ c, 0 < w c) (hrate : ∀ c, 0 < rate c)
    (hE : 0 < E) [Nonempty ι] (o : ℕ) : ∑ c, classPosterior w rate E o c = 1 := by
  have hpos : 0 < ∑ c', w c' * poissonLik (rate c' * E) o := Finset.sum_pos
    (fun c _ => mul_pos (hw c) (poissonLik_pos (mul_pos (hrate c) hE) o)) Finset.univ_nonempty
  unfold classPosterior
  rw [← Finset.sum_div, div_self hpos.ne']

/-- The likelihood recursion `P(o + 1 | μ) = P(o | μ) μ / (o + 1)`. -/
theorem poissonLik_succ (μ : ℝ) (o : ℕ) :
    poissonLik μ (o + 1) = poissonLik μ o * μ / (o + 1) := by
  unfold poissonLik
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

private theorem classPosterior_succ_le {w rate : ι → ℝ} {E : ℝ} (hw : ∀ c, 0 < w c)
    (hrate : ∀ c, 0 < rate c) (hE : 0 < E) {c₀ : ι} (hmin : ∀ c, rate c₀ ≤ rate c) (o : ℕ) :
    (classPosterior w rate E (o + 1) c₀ ≤ classPosterior w rate E o c₀) ∧
    ((∃ c, rate c₀ < rate c) →
      classPosterior w rate E (o + 1) c₀ < classPosterior w rate E o c₀) := by
  have hL : ∀ c, 0 < poissonLik (rate c * E) o := fun c => poissonLik_pos (mul_pos (hrate c) hE) o
  have hS : 0 < ∑ c, w c * poissonLik (rate c * E) o := by
    have : Nonempty ι := ⟨c₀⟩
    exact Finset.sum_pos (fun c _ => mul_pos (hw c) (hL c)) Finset.univ_nonempty
  have ho : (0 : ℝ) < o + 1 := by positivity
  have hS1 : ∑ c, w c * poissonLik (rate c * E) (o + 1) =
      (∑ c, w c * poissonLik (rate c * E) o * (rate c * E)) / (o + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [poissonLik_succ]; ring
  have key : ∀ c, w c * poissonLik (rate c * E) o * (rate c₀ * E) ≤
      w c * poissonLik (rate c * E) o * (rate c * E) := fun c =>
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmin c) hE.le)
      (mul_pos (hw c) (hL c)).le
  have hP0 : 0 < w c₀ * poissonLik (rate c₀ * E) o := mul_pos (hw c₀) (hL c₀)
  have hT : 0 < ∑ c, w c * poissonLik (rate c * E) o * (rate c * E) := by
    have : Nonempty ι := ⟨c₀⟩
    exact Finset.sum_pos (fun c _ => mul_pos (mul_pos (hw c) (hL c)) (mul_pos (hrate c) hE))
      Finset.univ_nonempty
  unfold classPosterior
  rw [hS1, poissonLik_succ]
  have e : w c₀ * (poissonLik (rate c₀ * E) o * (rate c₀ * E) / (↑o + 1)) /
      ((∑ c, w c * poissonLik (rate c * E) o * (rate c * E)) / (↑o + 1)) =
      w c₀ * poissonLik (rate c₀ * E) o * (rate c₀ * E) /
      (∑ c, w c * poissonLik (rate c * E) o * (rate c * E)) := by
    field_simp
  rw [e]
  have hsum : rate c₀ * E * ∑ c, w c * poissonLik (rate c * E) o ≤
      ∑ c, w c * poissonLik (rate c * E) o * (rate c * E) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => by linarith [key c]
  constructor
  · rw [div_le_div_iff₀ hT hS]
    calc w c₀ * poissonLik (rate c₀ * E) o * (rate c₀ * E) * ∑ c, w c * poissonLik (rate c * E) o
        = w c₀ * poissonLik (rate c₀ * E) o *
            (rate c₀ * E * ∑ c, w c * poissonLik (rate c * E) o) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hP0.le
  · rintro ⟨c₁, hc₁⟩
    have hlt : rate c₀ * E * ∑ c, w c * poissonLik (rate c * E) o <
        ∑ c, w c * poissonLik (rate c * E) o * (rate c * E) := by
      rw [Finset.mul_sum]
      refine Finset.sum_lt_sum (fun c _ => by linarith [key c]) ⟨c₁, Finset.mem_univ _, ?_⟩
      have h1 : rate c₀ * E < rate c₁ * E := mul_lt_mul_of_pos_right hc₁ hE
      have h2 := mul_pos (hw c₁) (hL c₁)
      nlinarith
    rw [div_lt_div_iff₀ hT hS]
    calc w c₀ * poissonLik (rate c₀ * E) o * (rate c₀ * E) * ∑ c, w c * poissonLik (rate c * E) o
        = w c₀ * poissonLik (rate c₀ * E) o *
            (rate c₀ * E * ∑ c, w c * poissonLik (rate c * E) o) := by ring
      _ < _ := mul_lt_mul_of_pos_left hlt hP0

/-- **pLI is antitone in the observed count**: the posterior of a class `c₀` whose rate is the
smallest is antitone in `o`, for every prior. -/
theorem classPosterior_antitone {w rate : ι → ℝ} {E : ℝ} (hw : ∀ c, 0 < w c)
    (hrate : ∀ c, 0 < rate c) (hE : 0 < E) {c₀ : ι} (hmin : ∀ c, rate c₀ ≤ rate c) :
    Antitone fun o => classPosterior w rate E o c₀ :=
  antitone_nat_of_succ_le fun o =>
    (classPosterior_succ_le hw hrate hE hmin o).1

/-- Strictly antitone when some class has a strictly larger rate. -/
theorem classPosterior_strictAnti {w rate : ι → ℝ} {E : ℝ} (hw : ∀ c, 0 < w c)
    (hrate : ∀ c, 0 < rate c) (hE : 0 < E) {c₀ : ι} (hmin : ∀ c, rate c₀ ≤ rate c)
    (hlt : ∃ c, rate c₀ < rate c) : StrictAnti fun o => classPosterior w rate E o c₀ :=
  strictAnti_nat_of_succ_lt fun o =>
    (classPosterior_succ_le hw hrate hE hmin o).2 hlt

end MathlibExt.Biology.StatisticalGenetics.GeneConstraint
