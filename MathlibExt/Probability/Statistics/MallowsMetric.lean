/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Mallows metric and sums of independent random variables

The Mallows metric `d_p` of Bickel and Freedman (P. J. Bickel and D. A. Freedman, "Some
asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Section 8) is the
Wasserstein distance `W_p` of `MathlibExt.MeasureTheory.OptimalTransport.Wasserstein`: the
infimum of `(E‖X - Y‖^p)^(1/p)` over couplings of the two laws. This file proves the lemmas of
Bickel and Freedman's Section 8 that control `d_p` along sums of independent variables, and Mallows'
contraction of normalised sums, the key step of their proof of the bootstrap for the mean.

Laws of sums of independent variables are convolutions of probability measures (`conv`).

## Main results

* `wasserstein_conv_le` (Lemma 8.6, two summands): `d_p(U₁ + U₂, V₁ + V₂) ≤ d_p(U₁, V₁) +
  d_p(U₂, V₂)` for independent pairs, `p ≥ 1`.
* `wasserstein_convPow_le` (Lemma 8.6, `m` identically distributed pairs):
  `d_p(μ^{∗m}, ν^{∗m}) ≤ m d_p(μ, ν)`.
* `wasserstein_map_smul` (equation (8.2)): `d_p(aU, aV) = |a| d_p(U, V)`.
* `transportCost_two_conv_le` (Lemma 8.7, two summands): in a Hilbert space, if `U₂` and `V₂`
  have the same mean, `d₂(U₁ + U₂, V₁ + V₂)² ≤ d₂(U₁, V₁)² + d₂(U₂, V₂)²`.
* `transportCost_two_center_add_le` and `transportCost_two_eq_center_add` (Lemma 8.8):
  `d₂(U, V)² = d₂(U - EU, V - EV)² + ‖EU - EV‖²`.
* `wasserstein_two_normalizedSum_le` (equation (2.2), C. L. Mallows, "A note on asymptotic joint
  normality", *Ann. Math. Statist.* 43 (1972) 508–515, Lemma 3 as quoted by Bickel and
  Freedman): the law `G⁽ᵐ⁾` of `m^{-1/2} ∑_{j<m} (Z_j - E Z_j)` satisfies
  `d₂(G⁽ᵐ⁾, H⁽ᵐ⁾) ≤ d₂(G, H)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExt.Probability.Statistics.MallowsMetric

section Normed

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- **Convolution of probability measures.** `conv μ ν` is the law of `U + V` for independent
`U ∼ μ` and `V ∼ ν`: the image of `μ ⊗ ν` under addition (`MeasureTheory.Measure.conv`). -/
noncomputable def conv (μ ν : ProbabilityMeasure E) : ProbabilityMeasure E :=
  ⟨(μ : Measure E) ∗ (ν : Measure E), inferInstance⟩

omit [BorelSpace E] [SecondCountableTopology E] in
@[simp] theorem toMeasure_conv (μ ν : ProbabilityMeasure E) :
    (conv μ ν : Measure E) = (μ : Measure E) ∗ (ν : Measure E) := rfl

theorem measurable_addPairs :
    Measurable (fun w : (E × E) × (E × E) => (w.1.1 + w.2.1, w.1.2 + w.2.2)) := by
  fun_prop

/-- **Coupling of convolutions.** If `π₁` couples `μ₁` with `ν₁` and `π₂` couples `μ₂` with
`ν₂`, then the law of `(X₁ + X₂, Y₁ + Y₂)` for independent pairs `(X₁, Y₁) ∼ π₁` and
`(X₂, Y₂) ∼ π₂` couples `μ₁ ∗ μ₂` with `ν₁ ∗ ν₂` (Bickel and Freedman, *Ann. Statist.* 9 (1981),
proof of Lemma 8.6: "assume ... that the pairs `(U_j, V_j)` are independent"). -/
theorem isCoupling_conv {μ₁ ν₁ μ₂ ν₂ : ProbabilityMeasure E}
    {π₁ π₂ : ProbabilityMeasure (E × E)} (h₁ : IsCoupling μ₁ ν₁ π₁) (h₂ : IsCoupling μ₂ ν₂ π₂) :
    IsCoupling (conv μ₁ μ₂) (conv ν₁ ν₂)
      ((π₁.prod π₂).map (fun w => (w.1.1 + w.2.1, w.1.2 + w.2.2))) := by
  obtain ⟨h1f, h1s⟩ := h₁
  obtain ⟨h2f, h2s⟩ := h₂
  constructor
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst measurable_addPairs,
      toMeasure_conv, Measure.conv, h1f, h2f, ProbabilityMeasure.toMeasure_prod,
      Measure.map_prod_map _ _ measurable_fst measurable_fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_snd measurable_addPairs,
      toMeasure_conv, Measure.conv, h1s, h2s, ProbabilityMeasure.toMeasure_prod,
      Measure.map_prod_map _ _ measurable_snd measurable_snd,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

private theorem lintegral_comp_fst_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (π₁ : ProbabilityMeasure α) (π₂ : ProbabilityMeasure β) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ w, f w.1 ∂((π₁.prod π₂ : ProbabilityMeasure (α × β)) : Measure (α × β)) =
      ∫⁻ x, f x ∂(π₁ : Measure α) := by
  rw [ProbabilityMeasure.toMeasure_prod]
  exact (measurePreserving_fst.lintegral_comp hf)

private theorem lintegral_comp_snd_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (π₁ : ProbabilityMeasure α) (π₂ : ProbabilityMeasure β) {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ w, f w.2 ∂((π₁.prod π₂ : ProbabilityMeasure (α × β)) : Measure (α × β)) =
      ∫⁻ x, f x ∂(π₂ : Measure β) := by
  rw [ProbabilityMeasure.toMeasure_prod]
  exact (measurePreserving_snd.lintegral_comp hf)

/-- **Mallows metric of sums of independent variables** (Bickel and Freedman, *Ann. Statist.* 9
(1981), Lemma 8.6, case of two summands). For `p ≥ 1` and probability measures on a separable
normed group, `d_p(μ₁ ∗ μ₂, ν₁ ∗ ν₂) ≤ d_p(μ₁, ν₁) + d_p(μ₂, ν₂)`: if `U₁, U₂` are independent
and `V₁, V₂` are independent, `d_p(U₁ + U₂, V₁ + V₂) ≤ d_p(U₁, V₁) + d_p(U₂, V₂)`. The proof
couples the pairs independently and applies Minkowski's inequality. No moment assumption is
needed, since `d_p` takes values in `[0, ∞]`. -/
theorem wasserstein_conv_le {p : ℝ} (hp : 1 ≤ p) (μ₁ ν₁ μ₂ ν₂ : ProbabilityMeasure E) :
    wasserstein p (conv μ₁ μ₂) (conv ν₁ ν₂) ≤ wasserstein p μ₁ ν₁ + wasserstein p μ₂ ν₂ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hed : Measurable (fun z : E × E => edist z.1 z.2 ^ p) :=
    (measurable_fst.edist measurable_snd).pow_const p
  rw [wasserstein_eq_iInf hp0 μ₁ ν₁, wasserstein_eq_iInf hp0 μ₂ ν₂]
  refine ENNReal.le_iInf_add_iInf fun π₁ π₂ => ENNReal.le_iInf_add_iInf fun h₁ h₂ => ?_
  refine (wasserstein_le_of_isCoupling hp0.le (isCoupling_conv h₁ h₂)).trans ?_
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hed measurable_addPairs]
  set P : Measure ((E × E) × (E × E)) :=
    ((π₁.prod π₂ : ProbabilityMeasure ((E × E) × (E × E))) : Measure ((E × E) × (E × E)))
    with hP
  have hf : Measurable (fun w : (E × E) × (E × E) => edist w.1.1 w.1.2) := by fun_prop
  have hg : Measurable (fun w : (E × E) × (E × E) => edist w.2.1 w.2.2) := by fun_prop
  calc (∫⁻ w : (E × E) × (E × E), edist (w.1.1 + w.2.1) (w.1.2 + w.2.2) ^ p ∂P) ^ (1 / p)
      ≤ (∫⁻ w : (E × E) × (E × E), ((fun w : (E × E) × (E × E) => edist w.1.1 w.1.2) +
          (fun w : (E × E) × (E × E) => edist w.2.1 w.2.2)) w ^ p ∂P) ^ (1 / p) := by
        gcongr with w
        exact edist_add_add_le _ _ _ _
    _ ≤ (∫⁻ w : (E × E) × (E × E), edist w.1.1 w.1.2 ^ p ∂P) ^ (1 / p) +
        (∫⁻ w : (E × E) × (E × E), edist w.2.1 w.2.2 ^ p ∂P) ^ (1 / p) :=
        ENNReal.lintegral_Lp_add_le hf.aemeasurable hg.aemeasurable hp
    _ = _ := by
        rw [hP, lintegral_comp_fst_prod π₁ π₂ hed, lintegral_comp_snd_prod π₁ π₂ hed]

/-- **Convolution powers.** `convPow μ m` is the law of `Z₁ + ⋯ + Z_m` for independent
`Z_j ∼ μ` (the Dirac mass at `0` for `m = 0`), defined by `μ^{∗(m+1)} = μ^{∗m} ∗ μ`. -/
noncomputable def convPow (μ : ProbabilityMeasure E) : ℕ → ProbabilityMeasure E
  | 0 => ⟨Measure.dirac 0, inferInstance⟩
  | m + 1 => conv (convPow μ m) μ

/-- **Mallows metric of convolution powers, general `p`** (Bickel and Freedman, *Ann. Statist.* 9
(1981), Lemma 8.6 for `m` identically distributed pairs). For `p ≥ 1`,
`d_p(μ^{∗m}, ν^{∗m}) ≤ m · d_p(μ, ν)`. -/
theorem wasserstein_convPow_le {p : ℝ} (hp : 1 ≤ p) (μ ν : ProbabilityMeasure E) :
    ∀ m : ℕ, wasserstein p (convPow μ m) (convPow ν m) ≤ m * wasserstein p μ ν
  | 0 => by
      have hρ : convPow ν 0 = convPow μ 0 := rfl
      rw [hρ, wasserstein_self (lt_of_lt_of_le zero_lt_one hp)]
      exact zero_le
  | m + 1 => by
      refine (wasserstein_conv_le hp (convPow μ m) (convPow ν m) μ ν).trans ?_
      refine (add_le_add (wasserstein_convPow_le hp μ ν m) le_rfl).trans (le_of_eq ?_)
      push_cast
      ring

end Normed

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

private theorem wasserstein_map_smul_le {p : ℝ} (hp : 0 < p) (a : ℝ)
    (μ ν : ProbabilityMeasure E) :
    wasserstein p (μ.map (a • ·)) (ν.map (a • ·)) ≤ ‖a‖ₑ * wasserstein p μ ν := by
  have hs : Measurable (fun x : E => a • x) := measurable_const_smul a
  have hed : Measurable (fun z : E × E => edist z.1 z.2 ^ p) :=
    (measurable_fst.edist measurable_snd).pow_const p
  have hpair : Measurable (fun z : E × E => (a • z.1, a • z.2)) := by fun_prop
  rcases eq_or_ne a 0 with rfl | ha
  · have h0 : ∀ ρ : ProbabilityMeasure E, ρ.map ((0 : ℝ) • ·) =
        (ProbabilityMeasure.map μ (fun _ : E => (0 : E))) := by
      intro ρ
      apply Subtype.ext
      change (ρ : Measure E).map _ = (μ : Measure E).map _
      simp only [zero_smul, Measure.map_const, measure_univ, one_smul]
    rw [h0 μ, h0 ν, wasserstein_self hp]
    exact zero_le
  have hne : ‖a‖ₑ ≠ 0 := by simpa using ha
  rw [wasserstein_eq_iInf hp μ ν, ENNReal.mul_iInf_of_ne hne enorm_ne_top]
  refine le_iInf fun π => ?_
  rw [ENNReal.mul_iInf_of_ne hne enorm_ne_top]
  refine le_iInf fun h => ?_
  have hc : IsCoupling (μ.map (a • ·)) (ν.map (a • ·)) (π.map (fun z => (a • z.1, a • z.2))) := by
    obtain ⟨h1, h2⟩ := h
    constructor
    · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map, h1,
        Measure.map_map hs measurable_fst, Measure.map_map measurable_fst hpair]
      rfl
    · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map, h2,
        Measure.map_map hs measurable_snd, Measure.map_map measurable_snd hpair]
      rfl
  refine (wasserstein_le_of_isCoupling hp.le hc).trans (le_of_eq ?_)
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hed hpair]
  dsimp only
  have hsm : ∀ x y : E, edist (a • x) (a • y) = ‖a‖ₑ * edist x y := fun x y => by
    rw [edist_smul₀, ENNReal.smul_def, smul_eq_mul]; rfl
  simp_rw [hsm]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul' _ _ (by simp [ENNReal.rpow_eq_top_iff, hp, hp.le]),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
    ENNReal.rpow_one]

/-- **Scaling of the Mallows metric** (Bickel and Freedman, *Ann. Statist.* 9 (1981),
equation (8.2)): `d_p(aU, aV) = |a| · d_p(U, V)` for every real scalar `a`, here for laws on a
separable real normed space and `p > 0`. -/
theorem wasserstein_map_smul {p : ℝ} (hp : 0 < p) (a : ℝ) (μ ν : ProbabilityMeasure E) :
    wasserstein p (μ.map (a • ·)) (ν.map (a • ·)) = ‖a‖ₑ * wasserstein p μ ν := by
  refine le_antisymm (wasserstein_map_smul_le hp a μ ν) ?_
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hs : Measurable (fun x : E => a • x) := measurable_const_smul a
  have hinv : ∀ ρ : ProbabilityMeasure E, (ρ.map (a • ·)).map (a⁻¹ • ·) = ρ := by
    intro ρ
    apply Subtype.ext
    change ((ρ : Measure E).map (a • ·)).map (a⁻¹ • ·) = (ρ : Measure E)
    rw [Measure.map_map (measurable_const_smul _) hs]
    simp [Function.comp_def, smul_smul, inv_mul_cancel₀ ha]
  have key := wasserstein_map_smul_le hp a⁻¹ (μ.map (a • ·)) (ν.map (a • ·))
  rw [hinv, hinv] at key
  have hne : ‖a‖ₑ ≠ 0 := by simpa using ha
  calc ‖a‖ₑ * wasserstein p μ ν
      ≤ ‖a‖ₑ * (‖a⁻¹‖ₑ * wasserstein p (μ.map (a • ·)) (ν.map (a • ·))) := by gcongr
    _ = wasserstein p (μ.map (a • ·)) (ν.map (a • ·)) := by
        rw [← mul_assoc, enorm_inv ha, ENNReal.mul_inv_cancel hne enorm_ne_top, one_mul]

end Scaling

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
private theorem edist_rpow_two (x y : E) :
    edist x y ^ (2 : ℝ) = ENNReal.ofReal (‖x - y‖ ^ 2) := by
  rw [edist_dist, dist_eq_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem memLp_fst_of_isCoupling {μ ν : ProbabilityMeasure E}
    {π : ProbabilityMeasure (E × E)} (h : IsCoupling μ ν π) (hμ : MemLp id 2 (μ : Measure E)) :
    MemLp (fun z : E × E => z.1) 2 (π : Measure (E × E)) := by
  rw [h.1] at hμ
  exact (memLp_map_measure_iff aestronglyMeasurable_id measurable_fst.aemeasurable).1 hμ

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem memLp_snd_of_isCoupling {μ ν : ProbabilityMeasure E}
    {π : ProbabilityMeasure (E × E)} (h : IsCoupling μ ν π) (hν : MemLp id 2 (ν : Measure E)) :
    MemLp (fun z : E × E => z.2) 2 (π : Measure (E × E)) := by
  rw [h.2] at hν
  exact (memLp_map_measure_iff aestronglyMeasurable_id measurable_snd.aemeasurable).1 hν

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem memLp_sub_of_isCoupling {μ ν : ProbabilityMeasure E}
    {π : ProbabilityMeasure (E × E)} (h : IsCoupling μ ν π) (hμ : MemLp id 2 (μ : Measure E))
    (hν : MemLp id 2 (ν : Measure E)) :
    MemLp (fun z : E × E => z.1 - z.2) 2 (π : Measure (E × E)) :=
  (memLp_fst_of_isCoupling h hμ).sub (memLp_snd_of_isCoupling h hν)

omit [CompleteSpace E] in
private theorem integral_sub_of_isCoupling {μ ν : ProbabilityMeasure E}
    {π : ProbabilityMeasure (E × E)} (h : IsCoupling μ ν π) (hμ : MemLp id 2 (μ : Measure E))
    (hν : MemLp id 2 (ν : Measure E)) :
    ∫ z, (z.1 - z.2) ∂(π : Measure (E × E)) =
      ∫ x, x ∂(μ : Measure E) - ∫ x, x ∂(ν : Measure E) := by
  rw [integral_sub ((memLp_fst_of_isCoupling h hμ).integrable one_le_two)
    ((memLp_snd_of_isCoupling h hν).integrable one_le_two), h.1, h.2,
    integral_map (f := fun x : E => x) measurable_fst.aemeasurable aestronglyMeasurable_id,
    integral_map (f := fun x : E => x) measurable_snd.aemeasurable aestronglyMeasurable_id]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The transport cost of a square-integrable plan as a Bochner integral. -/
private theorem lintegral_edist_rpow_two {π : Measure (E × E)}
    (hπ : MemLp (fun z : E × E => z.1 - z.2) 2 π) :
    ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂π = ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ^ 2 ∂π) := by
  simp_rw [edist_rpow_two]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hπ.aestronglyMeasurable).1 hπ)
    (ae_of_all _ fun _ => by positivity)).symm

omit [BorelSpace E] in
/-- The cost of the independent coupling of two plans, when the second plan has mean
displacement zero: the cross term `2 E⟨X₁ - Y₁, X₂ - Y₂⟩` vanishes. -/
private theorem lintegral_conv_coupling {π₁ π₂ : ProbabilityMeasure (E × E)}
    (h₁ : MemLp (fun z : E × E => z.1 - z.2) 2 (π₁ : Measure (E × E)))
    (h₂ : MemLp (fun z : E × E => z.1 - z.2) 2 (π₂ : Measure (E × E)))
    (hm : ∫ z, (z.1 - z.2) ∂(π₂ : Measure (E × E)) = 0) :
    ∫⁻ w, edist (w.1.1 + w.2.1) (w.1.2 + w.2.2) ^ (2 : ℝ)
        ∂((π₁.prod π₂ : ProbabilityMeasure ((E × E) × (E × E))) : Measure ((E × E) × (E × E))) =
      ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(π₁ : Measure (E × E)) +
        ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(π₂ : Measure (E × E)) := by
  set a : E × E → E := fun z => z.1 - z.2 with ha
  set P : Measure ((E × E) × (E × E)) := (π₁ : Measure (E × E)).prod (π₂ : Measure (E × E))
    with hP
  have hmp₁ : MeasurePreserving Prod.fst P (π₁ : Measure (E × E)) := measurePreserving_fst
  have hmp₂ : MeasurePreserving Prod.snd P (π₂ : Measure (E × E)) := measurePreserving_snd
  have hA : MemLp (fun w : (E × E) × (E × E) => a w.1) 2 P := h₁.comp_measurePreserving hmp₁
  have hB : MemLp (fun w : (E × E) × (E × E) => a w.2) 2 P := h₂.comp_measurePreserving hmp₂
  rw [ProbabilityMeasure.toMeasure_prod, ← hP, lintegral_edist_rpow_two h₁,
    lintegral_edist_rpow_two h₂]
  have hsq : ∀ w : (E × E) × (E × E), edist (w.1.1 + w.2.1) (w.1.2 + w.2.2) ^ (2 : ℝ) =
      ENNReal.ofReal (‖a w.1 + a w.2‖ ^ 2) := fun w => by
    rw [edist_rpow_two]; congr 2; simp [ha]; abel_nf
  simp_rw [hsq]
  have iA := (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).1 hA
  have iB := (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).1 hB
  have hS : MemLp (fun w : (E × E) × (E × E) => a w.1 + a w.2) 2 P := hA.add hB
  have iS := (memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).1 hS
  have iC : Integrable (fun w : (E × E) × (E × E) => ⟪a w.1, a w.2⟫_ℝ) P := by
    have : (fun w : (E × E) × (E × E) => ⟪a w.1, a w.2⟫_ℝ) =
        fun w => (‖a w.1 + a w.2‖ ^ 2 - ‖a w.1‖ ^ 2 - ‖a w.2‖ ^ 2) / 2 := by
      funext w; rw [norm_add_sq_real]; ring
    rw [this]
    exact ((iS.sub iA).sub iB).div_const 2
  have hcross : ∫ w, ⟪a w.1, a w.2⟫_ℝ ∂P = 0 := by
    rw [hP, integral_prod _ iC]
    refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [integral_inner (h₂.integrable one_le_two), hm, inner_zero_right]
    rfl
  have hexp : ∫ w, ‖a w.1 + a w.2‖ ^ 2 ∂P =
      ∫ z, ‖a z‖ ^ 2 ∂(π₁ : Measure (E × E)) + ∫ z, ‖a z‖ ^ 2 ∂(π₂ : Measure (E × E)) := by
    have e : (fun w : (E × E) × (E × E) => ‖a w.1 + a w.2‖ ^ 2) =
        fun w => (‖a w.1‖ ^ 2 + 2 * ⟪a w.1, a w.2⟫_ℝ) + ‖a w.2‖ ^ 2 := by
      funext w; rw [norm_add_sq_real]
    have iAC : Integrable (fun w : (E × E) × (E × E) => ‖a w.1‖ ^ 2 + 2 * ⟪a w.1, a w.2⟫_ℝ) P :=
      iA.add (iC.const_mul 2)
    rw [e, integral_add iAC iB, integral_add iA (iC.const_mul 2),
      integral_const_mul, hcross, mul_zero, add_zero, hP,
      integral_fun_fst (fun z => ‖a z‖ ^ 2), integral_fun_snd (fun z => ‖a z‖ ^ 2)]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal iS (ae_of_all _ fun _ => by positivity), hexp,
    ENNReal.ofReal_add (integral_nonneg fun _ => by positivity)
      (integral_nonneg fun _ => by positivity)]

/-- **Mallows metric of sums in a Hilbert space** (Bickel and Freedman, *Ann. Statist.* 9 (1981),
Lemma 8.7, case of two summands, in squared form `d₂² = transportCost 2`). Let `E` be a separable
real Hilbert space and `μ₁, ν₁, μ₂, ν₂` laws on `E` with finite second moments. If `μ₂` and `ν₂`
have the same mean, then `d₂(μ₁ ∗ μ₂, ν₁ ∗ ν₂)² ≤ d₂(μ₁, ν₁)² + d₂(μ₂, ν₂)²`. Bickel and
Freedman assume `E(U_j) = E(V_j)` for every `j`; equality of the means of one pair suffices,
since the cross term of the independent coupling is the inner product of the two mean
displacements. -/
theorem transportCost_two_conv_le (μ₁ ν₁ μ₂ ν₂ : ProbabilityMeasure E)
    (hμ₁ : MemLp id 2 (μ₁ : Measure E)) (hν₁ : MemLp id 2 (ν₁ : Measure E))
    (hμ₂ : MemLp id 2 (μ₂ : Measure E)) (hν₂ : MemLp id 2 (ν₂ : Measure E))
    (hmean : ∫ x, x ∂(μ₂ : Measure E) = ∫ x, x ∂(ν₂ : Measure E)) :
    transportCost 2 (conv μ₁ μ₂) (conv ν₁ ν₂) ≤
      transportCost 2 μ₁ ν₁ + transportCost 2 μ₂ ν₂ := by
  unfold transportCost
  refine ENNReal.le_iInf_add_iInf fun π₁ π₂ => ENNReal.le_iInf_add_iInf fun h₁ h₂ => ?_
  refine (iInf₂_le _ (isCoupling_conv h₁ h₂)).trans (le_of_eq ?_)
  have hed : Measurable (fun z : E × E => edist z.1 z.2 ^ (2 : ℝ)) :=
    (measurable_fst.edist measurable_snd).pow_const _
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hed measurable_addPairs]
  exact lintegral_conv_coupling (memLp_sub_of_isCoupling h₁ hμ₁ hν₁)
    (memLp_sub_of_isCoupling h₂ hμ₂ hν₂)
    (by rw [integral_sub_of_isCoupling h₂ hμ₂ hν₂, hmean, sub_self])

/-- **Bickel–Freedman Lemma 8.7 for `d₂`** (*Ann. Statist.* 9 (1981), Lemma 8.7, two
summands): under the hypotheses of `transportCost_two_conv_le`,
`d₂(μ₁ ∗ μ₂, ν₁ ∗ ν₂)² ≤ d₂(μ₁, ν₁)² + d₂(μ₂, ν₂)²` for the Wasserstein distance `W₂`. -/
theorem wasserstein_two_conv_sq_le (μ₁ ν₁ μ₂ ν₂ : ProbabilityMeasure E)
    (hμ₁ : MemLp id 2 (μ₁ : Measure E)) (hν₁ : MemLp id 2 (ν₁ : Measure E))
    (hμ₂ : MemLp id 2 (μ₂ : Measure E)) (hν₂ : MemLp id 2 (ν₂ : Measure E))
    (hmean : ∫ x, x ∂(μ₂ : Measure E) = ∫ x, x ∂(ν₂ : Measure E)) :
    wasserstein 2 (conv μ₁ μ₂) (conv ν₁ ν₂) ^ (2 : ℝ) ≤
      wasserstein 2 μ₁ ν₁ ^ (2 : ℝ) + wasserstein 2 μ₂ ν₂ ^ (2 : ℝ) := by
  simp only [wasserstein, ← ENNReal.rpow_mul]
  norm_num
  exact transportCost_two_conv_le μ₁ ν₁ μ₂ ν₂ hμ₁ hν₁ hμ₂ hν₂ hmean

/-- **Centring decreases the Mallows metric by the squared distance of the means**
(Bickel and Freedman, *Ann. Statist.* 9 (1981), Lemma 8.8, the inequality
`d₂(U - EU, V - EV)² ≤ d₂(U, V)² - ‖EU - EV‖²` proved first there). For laws `μ, ν` with finite
second moments on a separable real Hilbert space, with means `a = ∫ x dμ` and `b = ∫ x dν`, the
centred laws `μ.map (· - a)` (the law of `U - EU`) and `ν.map (· - b)` satisfy
`d₂(μ.map (· - a), ν.map (· - b))² + ‖a - b‖² ≤ d₂(μ, ν)²`. The equality is
`transportCost_two_eq_center_add`. -/
theorem transportCost_two_center_add_le (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E)) :
    transportCost 2 (μ.map (· - ∫ x, x ∂(μ : Measure E))) (ν.map (· - ∫ x, x ∂(ν : Measure E))) +
        ENNReal.ofReal (‖∫ x, x ∂(μ : Measure E) - ∫ x, x ∂(ν : Measure E)‖ ^ 2) ≤
      transportCost 2 μ ν := by
  set a := ∫ x, x ∂(μ : Measure E)
  set b := ∫ x, x ∂(ν : Measure E)
  have hed : Measurable (fun z : E × E => edist z.1 z.2 ^ (2 : ℝ)) :=
    (measurable_fst.edist measurable_snd).pow_const _
  have hsh : Measurable (fun z : E × E => (z.1 - a, z.2 - b)) := by fun_prop
  refine le_iInf₂ fun π h => ?_
  have hc : IsCoupling (μ.map (· - a)) (ν.map (· - b)) (π.map (fun z => (z.1 - a, z.2 - b))) := by
    obtain ⟨h1, h2⟩ := h
    constructor
    · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map, h1,
        Measure.map_map (by fun_prop) measurable_fst, Measure.map_map measurable_fst hsh]
      rfl
    · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map, h2,
        Measure.map_map (by fun_prop) measurable_snd, Measure.map_map measurable_snd hsh]
      rfl
  refine (add_le_add (transportCost_le_of_isCoupling hc) le_rfl).trans (le_of_eq ?_)
  have hd := memLp_sub_of_isCoupling h hμ hν
  have hmean := integral_sub_of_isCoupling h hμ hν
  have iD := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd
  have iI := hd.integrable one_le_two
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hed hsh, lintegral_edist_rpow_two hd]
  have hsq : ∀ z : E × E, edist (z.1 - a) (z.2 - b) ^ (2 : ℝ) =
      ENNReal.ofReal (‖(z.1 - z.2) - (a - b)‖ ^ 2) := fun z => by
    rw [edist_rpow_two]; congr 2; abel_nf
  simp only [hsq]
  have hexp : ∀ z : E × E, ‖(z.1 - z.2) - (a - b)‖ ^ 2 =
      ‖z.1 - z.2‖ ^ 2 - 2 * ⟪z.1 - z.2, a - b⟫_ℝ + ‖a - b‖ ^ 2 := fun z => norm_sub_sq_real _ _
  have iG : Integrable (fun z : E × E => ⟪z.1 - z.2, a - b⟫_ℝ) (π : Measure (E × E)) := by
    simp_rw [real_inner_comm (a - b)]
    exact iI.const_inner (a - b)
  have hG : ∫ z, ⟪z.1 - z.2, a - b⟫_ℝ ∂(π : Measure (E × E)) = ‖a - b‖ ^ 2 := by
    simp_rw [real_inner_comm (a - b)]
    rw [integral_inner iI, hmean, real_inner_self_eq_norm_sq]
  have iE : Integrable (fun z : E × E => ‖z.1 - z.2‖ ^ 2 - 2 * ⟪z.1 - z.2, a - b⟫_ℝ)
      (π : Measure (E × E)) := iD.sub (iG.const_mul 2)
  have iF : Integrable (fun z : E × E => ‖(z.1 - z.2) - (a - b)‖ ^ 2) (π : Measure (E × E)) := by
    simp_rw [hexp]; exact iE.add (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal iF (ae_of_all _ fun _ => by positivity),
    ← ENNReal.ofReal_add (integral_nonneg fun _ => by positivity) (by positivity)]
  congr 1
  simp_rw [hexp]
  rw [integral_add iE (integrable_const _), integral_sub iD (iG.const_mul 2), integral_const_mul,
    hG]
  simp
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Second moments of a convolution.** If `μ` and `ν` have finite second moments, so does
`μ ∗ ν`, since `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
theorem memLp_conv {μ ν : ProbabilityMeasure E} (hμ : MemLp id 2 (μ : Measure E))
    (hν : MemLp id 2 (ν : Measure E)) : MemLp id 2 (conv μ ν : Measure E) := by
  rw [toMeasure_conv, Measure.conv]
  refine (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 ?_
  exact (hμ.comp_measurePreserving measurePreserving_fst).add
    (hν.comp_measurePreserving measurePreserving_snd)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Second moments of a translate.** If `μ` has a finite second moment, so does the law of
`U - c` for `U ∼ μ`. -/
theorem memLp_map_sub {μ : ProbabilityMeasure E} (hμ : MemLp id 2 (μ : Measure E)) (c : E) :
    MemLp id 2 (μ.map (· - c) : Measure E) := by
  rw [ProbabilityMeasure.toMeasure_map]
  refine (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 ?_
  exact hμ.sub (memLp_const c)

/-- **Mean of a translate.** The mean of the law of `U - c` is `EU - c`. -/
theorem integral_map_sub {μ : ProbabilityMeasure E} (hμ : MemLp id 2 (μ : Measure E)) (c : E) :
    ∫ x, x ∂(μ.map (· - c) : Measure E) = ∫ x, x ∂(μ : Measure E) - c := by
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (f := fun x : E => x) (by fun_prop) aestronglyMeasurable_id,
    integral_sub (f := fun x : E => x) (hμ.integrable one_le_two) (integrable_const c)]
  simp

/-- **Mallows metric and centring** (Bickel and Freedman, *Ann. Statist.* 9 (1981), Lemma 8.8).
For laws `μ, ν` with finite second moments on a separable real Hilbert space, with means
`a = ∫ x dμ` and `b = ∫ x dν`,
`d₂(μ, ν)² = d₂(μ.map (· - a), ν.map (· - b))² + ‖a - b‖²`: the squared Mallows distance splits
into the distance of the centred laws and the squared distance of the means. -/
theorem transportCost_two_eq_center_add (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E)) :
    transportCost 2 μ ν =
      transportCost 2 (μ.map (· - ∫ x, x ∂(μ : Measure E)))
          (ν.map (· - ∫ x, x ∂(ν : Measure E))) +
        ENNReal.ofReal (‖∫ x, x ∂(μ : Measure E) - ∫ x, x ∂(ν : Measure E)‖ ^ 2) := by
  refine le_antisymm ?_ (transportCost_two_center_add_le μ ν hμ hν)
  set a := ∫ x, x ∂(μ : Measure E)
  set b := ∫ x, x ∂(ν : Measure E)
  set μc := μ.map (· - a)
  set νc := ν.map (· - b)
  have hμc : MemLp id 2 (μc : Measure E) := memLp_map_sub hμ a
  have hνc : MemLp id 2 (νc : Measure E) := memLp_map_sub hν b
  have hed : Measurable (fun z : E × E => edist z.1 z.2 ^ (2 : ℝ)) :=
    (measurable_fst.edist measurable_snd).pow_const _
  have hsh : Measurable (fun z : E × E => (z.1 + a, z.2 + b)) := by fun_prop
  have hback : ∀ (ρ : ProbabilityMeasure E) (c : E), ((ρ.map (· - c)).map (· + c)) = ρ := by
    intro ρ c
    apply Subtype.ext
    change ((ρ : Measure E).map (· - c)).map (· + c) = (ρ : Measure E)
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  conv_rhs => rw [transportCost]
  rw [ENNReal.iInf_add]
  refine le_iInf fun π => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun h => ?_
  have hc : IsCoupling μ ν (π.map (fun z => (z.1 + a, z.2 + b))) := by
    obtain ⟨h1, h2⟩ := h
    have e1 := congrArg (fun ρ : ProbabilityMeasure E => (ρ : Measure E)) (hback μ a)
    have e2 := congrArg (fun ρ : ProbabilityMeasure E => (ρ : Measure E)) (hback ν b)
    simp only [ProbabilityMeasure.toMeasure_map] at e1 e2
    constructor
    · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst hsh, ← e1]
      change ((μc : Measure E)).map (· + a) = _
      rw [h1, Measure.map_map (by fun_prop) measurable_fst]
      rfl
    · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_snd hsh, ← e2]
      change ((νc : Measure E)).map (· + b) = _
      rw [h2, Measure.map_map (by fun_prop) measurable_snd]
      rfl
  refine (transportCost_le_of_isCoupling hc).trans (le_of_eq ?_)
  have hd := memLp_sub_of_isCoupling h hμc hνc
  have hmean : ∫ z, (z.1 - z.2) ∂(π : Measure (E × E)) = 0 := by
    rw [integral_sub_of_isCoupling h hμc hνc, integral_map_sub hμ, integral_map_sub hν]
    simp [a, b]
  have iD := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd
  have iI := hd.integrable one_le_two
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hed hsh, lintegral_edist_rpow_two hd]
  have hsq : ∀ z : E × E, edist (z.1 + a) (z.2 + b) ^ (2 : ℝ) =
      ENNReal.ofReal (‖(z.1 - z.2) + (a - b)‖ ^ 2) := fun z => by
    rw [edist_rpow_two]; congr 2; abel_nf
  simp only [hsq]
  have hexp : ∀ z : E × E, ‖(z.1 - z.2) + (a - b)‖ ^ 2 =
      ‖z.1 - z.2‖ ^ 2 + 2 * ⟪z.1 - z.2, a - b⟫_ℝ + ‖a - b‖ ^ 2 := fun z => norm_add_sq_real _ _
  have iG : Integrable (fun z : E × E => ⟪z.1 - z.2, a - b⟫_ℝ) (π : Measure (E × E)) := by
    simp_rw [real_inner_comm (a - b)]
    exact iI.const_inner (a - b)
  have hG : ∫ z, ⟪z.1 - z.2, a - b⟫_ℝ ∂(π : Measure (E × E)) = 0 := by
    simp_rw [real_inner_comm (a - b)]
    rw [integral_inner iI, hmean, inner_zero_right]
  have iE : Integrable (fun z : E × E => ‖z.1 - z.2‖ ^ 2 + 2 * ⟪z.1 - z.2, a - b⟫_ℝ)
      (π : Measure (E × E)) := iD.add (iG.const_mul 2)
  have iF : Integrable (fun z : E × E => ‖(z.1 - z.2) + (a - b)‖ ^ 2) (π : Measure (E × E)) := by
    simp_rw [hexp]; exact iE.add (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal iF (ae_of_all _ fun _ => by positivity),
    ← ENNReal.ofReal_add (integral_nonneg fun _ => by positivity) (by positivity)]
  congr 1
  simp_rw [hexp]
  rw [integral_add iE (integrable_const _), integral_add iD (iG.const_mul 2), integral_const_mul,
    hG]
  simp

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Second moments of convolution powers.** If `μ` has a finite second moment, so does every
convolution power `μ^{∗m}`. -/
theorem memLp_convPow {μ : ProbabilityMeasure E} (hμ : MemLp id 2 (μ : Measure E)) :
    ∀ m, MemLp id 2 (convPow μ m : Measure E)
  | 0 => by
      change MemLp id 2 (Measure.dirac (0 : E))
      refine MemLp.of_bound aestronglyMeasurable_id 0 ?_
      rw [ae_dirac_iff (measurableSet_le (by fun_prop) (by fun_prop))]
      simp
  | m + 1 => memLp_conv (memLp_convPow hμ m) hμ

/-- **Mallows metric of convolution powers.** For laws `μ, ν` with finite second moments and
equal means on a separable real Hilbert space, `d₂(μ^{∗m}, ν^{∗m})² ≤ m · d₂(μ, ν)²`: Lemma 8.7
of Bickel and Freedman (*Ann. Statist.* 9 (1981)) applied to `m` independent pairs. -/
theorem transportCost_two_convPow_le {μ ν : ProbabilityMeasure E}
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hmean : ∫ x, x ∂(μ : Measure E) = ∫ x, x ∂(ν : Measure E)) :
    ∀ m : ℕ, transportCost 2 (convPow μ m) (convPow ν m) ≤ m * transportCost 2 μ ν
  | 0 => by
      have hρ : convPow ν 0 = convPow μ 0 := rfl
      rw [hρ]
      refine (transportCost_le_of_isCoupling (isCoupling_diag (convPow μ 0))).trans ?_
      have hd : Measurable (fun x : E => (x, x)) := by fun_prop
      rw [ProbabilityMeasure.toMeasure_map,
        lintegral_map ((measurable_fst.edist measurable_snd).pow_const _) hd]
      simp
  | m + 1 => by
      refine (transportCost_two_conv_le (convPow μ m) (convPow ν m) μ ν (memLp_convPow hμ m)
        (memLp_convPow hν m) hμ hν hmean).trans ?_
      refine (add_le_add (transportCost_two_convPow_le hμ hν hmean m) le_rfl).trans
        (le_of_eq ?_)
      push_cast
      ring

/-- **Mallows' contraction of normalised sums** (C. L. Mallows, *Ann. Math. Statist.* 43 (1972),
Lemma 3, as used in P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap",
*Ann. Statist.* 9 (1981), equation (2.2)). Let `G` and `H` be laws with finite second moments on
a separable real Hilbert space, and let `G⁽ᵐ⁾` be the law of `m^{-1/2} ∑_{j=1}^m (Z_j - E Z_j)`
for i.i.d. `Z_j ∼ G` (similarly `H⁽ᵐ⁾`). Then `d₂(G⁽ᵐ⁾, H⁽ᵐ⁾) ≤ d₂(G, H)` for every `m`. Here
`G⁽ᵐ⁾` is the image of the `m`-th convolution power of the centred law `G(· + EZ)` under
`x ↦ m^{-1/2} x`; for `m = 0` both sides of the comparison are the Dirac mass at `0`. Bickel and
Freedman state (2.2) on the line and derive it from their Lemmas 8.7 and 8.8 and (8.2). -/
theorem wasserstein_two_normalizedSum_le (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E)) (m : ℕ) :
    wasserstein 2
        ((convPow (μ.map (· - ∫ x, x ∂(μ : Measure E))) m).map ((Real.sqrt m)⁻¹ • ·))
        ((convPow (ν.map (· - ∫ x, x ∂(ν : Measure E))) m).map ((Real.sqrt m)⁻¹ • ·)) ≤
      wasserstein 2 μ ν := by
  set μc := μ.map (· - ∫ x, x ∂(μ : Measure E))
  set νc := ν.map (· - ∫ x, x ∂(ν : Measure E))
  have hμc : MemLp id 2 (μc : Measure E) := memLp_map_sub hμ _
  have hνc : MemLp id 2 (νc : Measure E) := memLp_map_sub hν _
  have hmc : ∫ x, x ∂(μc : Measure E) = ∫ x, x ∂(νc : Measure E) := by
    rw [integral_map_sub hμ, integral_map_sub hν, sub_self, sub_self]
  have h1 := transportCost_two_convPow_le hμc hνc hmc m
  have h2 : transportCost 2 μc νc ≤ transportCost 2 μ ν :=
    le_self_add.trans (transportCost_two_center_add_le μ ν hμ hν)
  have hkey : ‖(Real.sqrt m)⁻¹‖ₑ * (m : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
    rw [show (m : ℝ≥0∞) = ENNReal.ofReal m by simp,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.enorm_of_nonneg (inv_nonneg.2 hs.le), ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le),
      inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one]
  rw [wasserstein_map_smul two_pos]
  calc ‖(Real.sqrt m)⁻¹‖ₑ * wasserstein 2 (convPow μc m) (convPow νc m)
      ≤ ‖(Real.sqrt m)⁻¹‖ₑ * ((m : ℝ≥0∞) * transportCost 2 μ ν) ^ (1 / 2 : ℝ) := by
        unfold wasserstein
        gcongr
        exact h1.trans (by gcongr)
    _ = (‖(Real.sqrt m)⁻¹‖ₑ * (m : ℝ≥0∞) ^ (1 / 2 : ℝ)) * wasserstein 2 μ ν := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), wasserstein, mul_assoc]
    _ ≤ 1 * wasserstein 2 μ ν := by gcongr
    _ = wasserstein 2 μ ν := one_mul _

end Hilbert

end MathlibExt.Probability.Statistics.MallowsMetric
