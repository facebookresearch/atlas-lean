/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FisherInformation
public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.EValues

/-!
# Universal inference: the split likelihood-ratio test

Wasserman, Ramdas and Balakrishnan's **universal inference** builds a test of a composite null
`H₀ : θ ∈ Θ₀` with finite-sample validity and no regularity conditions. Split the data into an
inference part `D₀` and an estimation part `D₁`, independent of each other. Fit *any* estimator
`θ̂₁` on `D₁`, and let `θ̂₀` maximize the likelihood of `D₀` over the null `Θ₀`. The **split
likelihood ratio**

  `T = L₀(θ̂₁) / L₀(θ̂₀)`,  `L₀(θ) = p_θ(D₀)`,

is an e-value under every null parameter: `E_{θ⋆}[T] ≤ 1` for `θ⋆ ∈ Θ₀`. Hence the split LRT,
which rejects when `T > 1 / α`, has type-I error at most `α`, uniformly over the null, at every
sample size.

The argument: `L₀(θ̂₀) ≥ L₀(θ⋆)` because `θ̂₀` maximizes over a set containing `θ⋆`, so
`T ≤ L₀(θ̂₁) / L₀(θ⋆)`; conditionally on `D₁` the estimate `θ̂₁` is a fixed parameter and
`E_{θ⋆}[p_{θ̂₁}(D₀) / p_{θ⋆}(D₀)] ≤ ∫ p_{θ̂₁} ≤ 1`.

## Main results

* `isEValue_splitLR_section`: **conditional validity**. For every value of the estimation split,
  the split likelihood ratio, as a function of `D₀`, is an e-value under the law of `D₀`. Only the
  denominator's domination of the true density `p θ⋆` is used, so this covers the null MLE, any
  null likelihood upper bound, and the true density itself.
* `isEValue_splitLR`: the split likelihood ratio is an e-value under the joint law
  `P_{θ⋆} ⊗ ν` of `(D₀, D₁)`, for an arbitrary law `ν` of `D₁` (independence of the splits is the
  product structure).
* `isEValue_splitLRT`: the split LRT with a null MLE `θ̂₀` (`IsNullMLE`) is an e-value under every
  null parameter `θ⋆ ∈ Θ₀`.
* `measure_splitLRTRejects_le`: **finite-sample type-I error control**,
  `P_{θ⋆} {T > 1 / α} ≤ α` for every `θ⋆ ∈ Θ₀`.
* `isValidPValue_splitLRT`: `(max T 1)⁻¹` is a valid p-value.
* `measure_not_mem_universalConfidenceSet_le`: the **universal confidence set**
  `{θ | L₀(θ̂₁) / L₀(θ) ≤ 1 / α}` covers the true parameter with probability at least `1 - α`.
* `measure_splitLRTRejectsClosed_le` and `measure_not_mem_universalConfidenceSetStrict_le`: the
  same bounds for the boundary variants `T ≥ 1 / α` and `{θ | L₀(θ̂₁) / L₀(θ) < 1 / α}` with the
  real ratio, which are not the cited constructions.

The e-value consequences (Markov bound, e-to-p calibration) are those of `EValues.lean`; this
file proves only that the split construction produces an e-value.

Only the split half is formalized: the swapped statistic (roles of `D₀` and `D₁` exchanged) and
the crossfit averages of Wasserman, Ramdas and Balakrishnan (2020), `Sₙ(θ)` in eq. (5) and
`Wₙ = (Uₙ + Uₙ^swap) / 2` in eq. (10), are out of scope.

## Implementation notes

The law of `D₀` under `θ` is `ref.withDensity (ofReal ∘ p θ)` (`FisherInformation.lawOf`) for real
nonnegative densities `p θ` with `∫⁻ ofReal (p θ) ∂ref ≤ 1`; the sample space `X₀` is arbitrary,
so an i.i.d. sample of size `n` is the case `X₀ = Fin n → X` with a product density. The ratio
uses real division, so a zero denominator gives `T = 0`; validity needs no positivity, since
`p θ⋆ ≤ L` makes `p θ⋆ · (q / L) ≤ q` hold pointwise, including where `L = 0`. The rejection
region `splitLRTRejects` and the confidence set `universalConfidenceSet` compare likelihoods in
cross-multiplied form (`L₀(θ̂₀) < α · L₀(θ̂₁)` and `α · L₀(θ̂₁) ≤ L₀(θ)`), so they do not depend
on the value of `x / 0`: a positive numerator over a zero denominator counts as exceeding `1 / α`,
and `0 / 0` does not. Their bounds follow from the real-valued e-value because a denominator that
dominates `p θ⋆` vanishes with probability zero (`measure_setOf_denom_eq_zero`). The variants
`splitLRTRejectsClosed` and `universalConfidenceSetStrict` use the real ratio and the opposite
boundary; Markov's inequality bounds them directly. The joint law is `lawOf ref p θ⋆ ⊗ ν` with
`ν` the law of `D₁`; the theorems allow any probability measure `ν`, in particular the model law
of `D₁` under `θ⋆`.

## References

* L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, Proc. Natl. Acad. Sci.
  USA 117 (2020), 16880–16890; arXiv:1912.11436 (Theorem 1: universal confidence set; Theorem 3:
  split LRT). Theorem and equation numbers follow arXiv version 3.
* A. Ramdas, P. Grünwald, V. Vovk and G. Shafer, *Game-theoretic statistics and safe anytime-valid
  inference*, Statist. Sci. 38 (2023), 576–601.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting.UniversalInference

open MeasureTheory
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)

variable {Θ X₀ X₁ : Type*} {m₀ : MeasurableSpace X₀} {m₁ : MeasurableSpace X₁}

/-! ### Definitions -/

/-- The law `lawOf ref p θ` of the inference split, with density `p θ` with respect to an
s-finite reference measure `ref`, is s-finite. -/
instance (ref : Measure X₀) [SFinite ref] (p : Θ → X₀ → ℝ) (θ : Θ) :
    SFinite (lawOf ref p θ) := by
  unfold lawOf
  infer_instance

/-- The **split likelihood ratio** with denominator `L`: at `z = (D₀, D₁)` it is
`p_{θ̂₁(D₁)}(D₀) / L(D₀)`, the likelihood of the inference split at the estimate fitted on the
estimation split, divided by `L(D₀)`. The split LRT takes `L(D₀)` to be the maximized null
likelihood (`splitLRT`); `L = p θ` gives the statistic `Tₙ(θ)` of the universal confidence set.
Real division makes the ratio `0` where `L(D₀) = 0`.

Source: Wasserman, Ramdas and Balakrishnan (2020), eq. (3). -/
noncomputable def splitLR (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (L : X₀ → ℝ) (z : X₀ × X₁) : ℝ :=
  p (θ₁ z.2) z.1 / L z.1

/-- `θ₀` is a **null maximum-likelihood estimator** on the inference split: it takes values in
the null `Θ₀` and maximizes the likelihood `p θ x` over `θ ∈ Θ₀` at every observation `x`. -/
structure IsNullMLE (p : Θ → X₀ → ℝ) (Θ₀ : Set Θ) (θ₀ : X₀ → Θ) : Prop where
  /-- The null MLE lies in the null. -/
  mem : ∀ x, θ₀ x ∈ Θ₀
  /-- The null MLE maximizes the likelihood over the null. -/
  le_max : ∀ x, ∀ θ ∈ Θ₀, p θ x ≤ p (θ₀ x) x

/-- The **split likelihood-ratio test statistic** `T = L₀(θ̂₁) / L₀(θ̂₀)`: the estimate `θ̂₁` is
fitted on `D₁`, the null MLE `θ̂₀` on `D₀`, and both likelihoods are evaluated on `D₀`.

Source: Wasserman, Ramdas and Balakrishnan (2020), eq. (9). -/
noncomputable def splitLRT (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (θ₀ : X₀ → Θ) : X₀ × X₁ → ℝ :=
  splitLR p θ₁ fun x => p (θ₀ x) x

/-- The rejection region of the level-`α` split LRT, `T > 1 / α`, in cross-multiplied form
`L₀(θ̂₀) < α · L₀(θ̂₁)`. Where the null likelihood `L₀(θ̂₀)` is positive and `α > 0`, this is
`α⁻¹ < splitLRT p θ₁ θ₀ z` (`mem_splitLRTRejects_iff`); where it vanishes, the test rejects
exactly when `L₀(θ̂₁) > 0` (for `α > 0`).

Source: Wasserman, Ramdas and Balakrishnan (2020), eq. (9). -/
def splitLRTRejects (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (θ₀ : X₀ → Θ) (α : ℝ) : Set (X₀ × X₁) :=
  {z | p (θ₀ z.1) z.1 < α * p (θ₁ z.2) z.1}

/-- The boundary-inclusive variant `T ≥ 1 / α` of the split-LRT rejection region, with the real
ratio. This is not the cited test: it also rejects on the boundary `T = 1 / α`, and for `α > 0`
it never rejects where the null likelihood vanishes (there the real ratio is `0`). It is the
event that Markov's inequality bounds directly (`measure_splitLRTRejectsClosed_le`). -/
def splitLRTRejectsClosed (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (θ₀ : X₀ → Θ) (α : ℝ) :
    Set (X₀ × X₁) :=
  {z | α⁻¹ ≤ splitLRT p θ₁ θ₀ z}

/-- The **universal confidence set** at level `α`: the parameters `θ` with
`Tₙ(θ) = L₀(θ̂₁) / L₀(θ) ≤ 1 / α`, in cross-multiplied form `α · L₀(θ̂₁) ≤ L₀(θ)`. Where
`L₀(θ) > 0` and `α > 0`, this is `splitLR p θ₁ (p θ) z ≤ α⁻¹`
(`mem_universalConfidenceSet_iff`). For `α > 0` and nonnegative densities, a parameter with
`L₀(θ) = 0` belongs to the set only if `L₀(θ̂₁) = 0`.

Source: Wasserman, Ramdas and Balakrishnan (2020), eq. (4). -/
def universalConfidenceSet (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (α : ℝ) (z : X₀ × X₁) : Set Θ :=
  {θ | α * p (θ₁ z.2) z.1 ≤ p θ z.1}

/-- The strict variant `Tₙ(θ) < 1 / α` of the universal confidence set, with the real ratio.
This is not the cited set: it excludes the boundary `Tₙ(θ) = 1 / α`, and for `α > 0` it contains
every parameter with `L₀(θ) = 0` (there the real ratio is `0`). Its coverage is the Markov bound
applied directly (`measure_not_mem_universalConfidenceSetStrict_le`). -/
def universalConfidenceSetStrict (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (α : ℝ) (z : X₀ × X₁) :
    Set Θ :=
  {θ | splitLR p θ₁ (p θ) z < α⁻¹}

/-- Where the null likelihood is positive and `α > 0`, the rejection region is
`α⁻¹ < splitLRT`. -/
theorem mem_splitLRTRejects_iff {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θ₀ : X₀ → Θ} {α : ℝ}
    {z : X₀ × X₁} (hα : 0 < α) (hz : 0 < p (θ₀ z.1) z.1) :
    z ∈ splitLRTRejects p θ₁ θ₀ α ↔ α⁻¹ < splitLRT p θ₁ θ₀ z := by
  change p (θ₀ z.1) z.1 < α * p (θ₁ z.2) z.1 ↔ α⁻¹ < p (θ₁ z.2) z.1 / p (θ₀ z.1) z.1
  rw [lt_div_iff₀ hz, inv_mul_lt_iff₀ hα]

/-- Where `L₀(θ) > 0` and `α > 0`, membership in the universal confidence set is
`Tₙ(θ) ≤ α⁻¹`. -/
theorem mem_universalConfidenceSet_iff {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {α : ℝ}
    {z : X₀ × X₁} {θ : Θ} (hα : 0 < α) (hθ : 0 < p θ z.1) :
    θ ∈ universalConfidenceSet p θ₁ α z ↔ splitLR p θ₁ (p θ) z ≤ α⁻¹ := by
  change α * p (θ₁ z.2) z.1 ≤ p θ z.1 ↔ p (θ₁ z.2) z.1 / p θ z.1 ≤ α⁻¹
  rw [div_le_iff₀ hθ, le_inv_mul_iff₀ hα]

/-! ### Validity of the split likelihood ratio -/

/-- The pointwise inequality behind universal inference: if `0 ≤ a ≤ L` and `0 ≤ q`, then
`a · (q / L) ≤ q`; for `L = 0` both sides of the ratio vanish under real division. -/
private theorem mul_div_le_of_le {a q L : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (h : a ≤ L) :
    a * (q / L) ≤ q := by
  rcases (ha.trans h).eq_or_lt with hL | hL
  · rw [← hL, div_zero, mul_zero]
    exact hq
  · rw [← mul_div_assoc, div_le_iff₀ hL]
    nlinarith

/-- The split likelihood ratio is measurable when the fitted likelihood and the denominator
are. -/
theorem measurable_splitLR {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {L : X₀ → ℝ}
    (hnum : Measurable fun z : X₀ × X₁ => p (θ₁ z.2) z.1) (hL : Measurable L) :
    Measurable (splitLR p θ₁ L) :=
  hnum.div (hL.comp measurable_fst)

/-- **Conditional validity of the split likelihood ratio.** Fix the estimation split `y`. If
the denominator `L` dominates the true density `p θ⋆`, then the split likelihood ratio, as a
function of the inference split, is an e-value under the law of `D₀` at `θ⋆`.

Source: Wasserman, Ramdas and Balakrishnan (2020), proof of Theorem 1, eq. (6). -/
theorem isEValue_splitLR_section {ref : Measure X₀} {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ}
    {L : X₀ → ℝ} {θstar : Θ} (hp : ∀ θ x, 0 ≤ p θ x)
    (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1) (hpstar : Measurable (p θstar))
    (hT : Measurable (splitLR p θ₁ L)) (hdom : ∀ x, p θstar x ≤ L x) (y : X₁) :
    IsEValue (lawOf ref p θstar) fun x => splitLR p θ₁ L (x, y) where
  nonneg x := div_nonneg (hp _ _) ((hp _ _).trans (hdom x))
  measurable := hT.comp measurable_prodMk_right
  lintegral_le_one := by
    have hg : Measurable fun x => ENNReal.ofReal (splitLR p θ₁ L (x, y)) :=
      (hT.comp measurable_prodMk_right).ennreal_ofReal
    rw [lawOf, lintegral_withDensity_eq_lintegral_mul _ hpstar.ennreal_ofReal hg]
    refine le_trans (lintegral_mono fun x => ?_) (hdens (θ₁ y))
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hp _ _)]
    exact ENNReal.ofReal_le_ofReal (mul_div_le_of_le (hp _ _) (hp _ _) (hdom x))

/-- **The split likelihood ratio is an e-value** under the joint law `P_{θ⋆} ⊗ ν` of the two
independent splits, whenever its denominator dominates the true density `p θ⋆`. The law `ν` of
the estimation split is arbitrary.

Source: Wasserman, Ramdas and Balakrishnan (2020), proofs of Theorems 1 and 3. -/
theorem isEValue_splitLR {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {L : X₀ → ℝ} {θstar : Θ}
    (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hpstar : Measurable (p θstar)) (hT : Measurable (splitLR p θ₁ L))
    (hdom : ∀ x, p θstar x ≤ L x) :
    IsEValue ((lawOf ref p θstar).prod ν) (splitLR p θ₁ L) where
  nonneg z := div_nonneg (hp _ _) ((hp _ _).trans (hdom z.1))
  measurable := hT
  lintegral_le_one := by
    rw [lintegral_prod_symm _ hT.ennreal_ofReal.aemeasurable]
    calc ∫⁻ y, ∫⁻ x, ENNReal.ofReal (splitLR p θ₁ L (x, y)) ∂lawOf ref p θstar ∂ν
        ≤ ∫⁻ _y, 1 ∂ν := lintegral_mono fun y =>
          (isEValue_splitLR_section hp hdens hpstar hT hdom y).lintegral_le_one
      _ = 1 := by simp

/-- **Universal inference: the split LRT is an e-value under every null parameter.** If `θ̂₀`
is a null MLE on the inference split and `θ⋆ ∈ Θ₀`, then `T = L₀(θ̂₁) / L₀(θ̂₀)` is an e-value
under `P_{θ⋆} ⊗ ν`, whatever the estimator `θ̂₁` fitted on the estimation split.

Source: Wasserman, Ramdas and Balakrishnan (2020), proof of Theorem 3. -/
theorem isEValue_splitLRT {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θ₀ : X₀ → Θ} {Θ₀ : Set Θ}
    {θstar : Θ} (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hmle : IsNullMLE p Θ₀ θ₀) (hstar : θstar ∈ Θ₀) (hpstar : Measurable (p θstar))
    (hT : Measurable (splitLRT p θ₁ θ₀)) :
    IsEValue ((lawOf ref p θstar).prod ν) (splitLRT p θ₁ θ₀) :=
  isEValue_splitLR hp hdens hpstar hT fun x => hmle.le_max x θstar hstar

/-- A denominator that dominates the true density `p θ⋆` vanishes with probability zero under
`P_{θ⋆} ⊗ ν`. -/
theorem measure_setOf_denom_eq_zero {ref : Measure X₀} {ν : Measure X₁}
    [SFinite ν] {p : Θ → X₀ → ℝ} {L : X₀ → ℝ} {θstar : Θ} (hp : ∀ θ x, 0 ≤ p θ x)
    (hpstar : Measurable (p θstar)) (hdom : ∀ x, p θstar x ≤ L x) :
    (lawOf ref p θstar).prod ν {z | L z.1 = 0} = 0 := by
  have h0 : lawOf ref p θstar {x | p θstar x = 0} = 0 := by
    rw [lawOf, withDensity_apply_eq_zero' hpstar.ennreal_ofReal.aemeasurable]
    refine measure_mono_null (fun x hx => ?_) measure_empty
    exact hx.1 (by rw [hx.2, ENNReal.ofReal_zero])
  refine measure_mono_null (t := {x | p θstar x = 0} ×ˢ Set.univ) (fun z hz => ?_) ?_
  · exact ⟨le_antisymm ((hdom z.1).trans_eq hz) (hp _ _), Set.mem_univ _⟩
  · rw [Measure.prod_prod, h0, zero_mul]

/-- **The split likelihood ratio exceeds `1 / α` with probability at most `α`.** If `L`
dominates the true density `p θ⋆`, the event `L(D₀) < α · p_{θ̂₁(D₁)}(D₀)`, that is
`p_{θ̂₁(D₁)}(D₀) / L(D₀) > 1 / α` with a positive numerator over a zero denominator counted as
exceeding `1 / α`, has probability at most `α` under `P_{θ⋆} ⊗ ν`. -/
theorem measure_setOf_lt_mul_le {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {L : X₀ → ℝ} {θstar : Θ}
    (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hpstar : Measurable (p θstar)) (hT : Measurable (splitLR p θ₁ L))
    (hdom : ∀ x, p θstar x ≤ L x) {α : ℝ} (hα : 0 < α) :
    (lawOf ref p θstar).prod ν {z | L z.1 < α * p (θ₁ z.2) z.1} ≤ ENNReal.ofReal α := by
  have hsub : {z : X₀ × X₁ | L z.1 < α * p (θ₁ z.2) z.1} ⊆
      {z | α⁻¹ ≤ splitLR p θ₁ L z} ∪ {z | L z.1 = 0} := by
    intro z hz
    rcases ((hp θstar z.1).trans (hdom z.1)).eq_or_lt with h0 | hpos
    · exact Or.inr h0.symm
    · refine Or.inl ?_
      change α⁻¹ ≤ p (θ₁ z.2) z.1 / L z.1
      refine le_of_lt ?_
      rw [lt_div_iff₀ hpos, inv_mul_lt_iff₀ hα]
      exact hz
  have hM := (isEValue_splitLR (ν := ν) hp hdens hpstar hT hdom).measure_ge_le (inv_pos.2 hα)
  rw [inv_inv] at hM
  calc (lawOf ref p θstar).prod ν {z | L z.1 < α * p (θ₁ z.2) z.1}
      ≤ (lawOf ref p θstar).prod ν ({z | α⁻¹ ≤ splitLR p θ₁ L z} ∪ {z | L z.1 = 0}) :=
        measure_mono hsub
    _ ≤ (lawOf ref p θstar).prod ν {z | α⁻¹ ≤ splitLR p θ₁ L z} +
          (lawOf ref p θstar).prod ν {z | L z.1 = 0} := measure_union_le _ _
    _ ≤ ENNReal.ofReal α := by
        rw [measure_setOf_denom_eq_zero hp hpstar hdom, add_zero]
        exact hM

/-- **Finite-sample type-I error control of the split LRT.** For every null parameter
`θ⋆ ∈ Θ₀` and every `α > 0`, the test rejecting when `T > 1 / α` has
`P_{θ⋆} (reject) ≤ α`.

Source: Wasserman, Ramdas and Balakrishnan (2020), Theorem 3. -/
theorem measure_splitLRTRejects_le {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θ₀ : X₀ → Θ} {Θ₀ : Set Θ}
    {θstar : Θ} (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hmle : IsNullMLE p Θ₀ θ₀) (hstar : θstar ∈ Θ₀) (hpstar : Measurable (p θstar))
    (hT : Measurable (splitLRT p θ₁ θ₀)) {α : ℝ} (hα : 0 < α) :
    (lawOf ref p θstar).prod ν (splitLRTRejects p θ₁ θ₀ α) ≤ ENNReal.ofReal α :=
  measure_setOf_lt_mul_le hp hdens hpstar hT (fun x => hmle.le_max x θstar hstar) hα

/-- **Type-I error control of the boundary-inclusive split LRT.** For every null parameter
`θ⋆ ∈ Θ₀` and every `α > 0`, the variant rejecting when `T ≥ 1 / α` also has
`P_{θ⋆} (reject) ≤ α`. -/
theorem measure_splitLRTRejectsClosed_le {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θ₀ : X₀ → Θ} {Θ₀ : Set Θ}
    {θstar : Θ} (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hmle : IsNullMLE p Θ₀ θ₀) (hstar : θstar ∈ Θ₀) (hpstar : Measurable (p θstar))
    (hT : Measurable (splitLRT p θ₁ θ₀)) {α : ℝ} (hα : 0 < α) :
    (lawOf ref p θstar).prod ν (splitLRTRejectsClosed p θ₁ θ₀ α) ≤ ENNReal.ofReal α := by
  have h := (isEValue_splitLRT (ν := ν) hp hdens hmle hstar hpstar hT).measure_ge_le
    (inv_pos.2 hα)
  rwa [inv_inv] at h

/-- **The split-LRT p-value is valid.** Under every null parameter, `(max T 1)⁻¹` is a valid
p-value, when the law of the inference split is a probability measure. -/
theorem isValidPValue_splitLRT {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θ₀ : X₀ → Θ} {Θ₀ : Set Θ}
    {θstar : Θ} [IsProbabilityMeasure (lawOf ref p θstar)] (hp : ∀ θ x, 0 ≤ p θ x)
    (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1) (hmle : IsNullMLE p Θ₀ θ₀)
    (hstar : θstar ∈ Θ₀) (hpstar : Measurable (p θstar)) (hT : Measurable (splitLRT p θ₁ θ₀)) :
    IsValidPValue ((lawOf ref p θstar).prod ν) fun z => (max (splitLRT p θ₁ θ₀ z) 1)⁻¹ :=
  (isEValue_splitLRT hp hdens hmle hstar hpstar hT).isValidPValue

/-- **Coverage of the universal confidence set.** The true parameter lies outside the level-`α`
universal confidence set with probability at most `α`.

Source: Wasserman, Ramdas and Balakrishnan (2020), Theorem 1. -/
theorem measure_not_mem_universalConfidenceSet_le {ref : Measure X₀} [SFinite ref]
    {ν : Measure X₁} [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θstar : Θ}
    (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hpstar : Measurable (p θstar)) (hT : Measurable (splitLR p θ₁ (p θstar))) {α : ℝ}
    (hα : 0 < α) :
    (lawOf ref p θstar).prod ν {z | θstar ∉ universalConfidenceSet p θ₁ α z} ≤
      ENNReal.ofReal α := by
  have hset : {z | θstar ∉ universalConfidenceSet p θ₁ α z} =
      {z | p θstar z.1 < α * p (θ₁ z.2) z.1} := by
    ext z
    simp [universalConfidenceSet]
  rw [hset]
  exact measure_setOf_lt_mul_le hp hdens hpstar hT (fun _ => le_rfl) hα

/-- **Coverage of the strict universal confidence set.** The true parameter lies outside the
strict variant `{θ | Tₙ(θ) < 1 / α}` with probability at most `α`. -/
theorem measure_not_mem_universalConfidenceSetStrict_le {ref : Measure X₀} [SFinite ref]
    {ν : Measure X₁} [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θstar : Θ}
    (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hpstar : Measurable (p θstar)) (hT : Measurable (splitLR p θ₁ (p θstar))) {α : ℝ}
    (hα : 0 < α) :
    (lawOf ref p θstar).prod ν {z | θstar ∉ universalConfidenceSetStrict p θ₁ α z} ≤
      ENNReal.ofReal α := by
  have hset : {z | θstar ∉ universalConfidenceSetStrict p θ₁ α z} =
      {z | α⁻¹ ≤ splitLR p θ₁ (p θstar) z} := by
    ext z
    simp [universalConfidenceSetStrict]
  have h := (isEValue_splitLR (ν := ν) hp hdens hpstar hT fun _ => le_rfl).measure_ge_le
    (inv_pos.2 hα)
  rwa [inv_inv, ← hset] at h

end MathlibExt.Probability.Statistics.MultipleTesting.UniversalInference
