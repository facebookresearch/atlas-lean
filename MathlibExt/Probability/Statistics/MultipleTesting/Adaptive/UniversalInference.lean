/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.EValues

/-!
# Universal inference: the split likelihood-ratio test

Wasserman, Ramdas and Balakrishnan's **universal inference** builds a test of a composite null
`H₀ : θ ∈ Θ₀` with finite-sample validity and no regularity conditions. Split the data into an
inference part `D₀` and an estimation part `D₁`, independent of each other. Fit *any* estimator
`θ̂₁` on `D₁`, and let `θ̂₀` maximize the likelihood of `D₀` over the null `Θ₀`. The **split
likelihood ratio**

  `T = L₀(θ̂₁) / L₀(θ̂₀)`,  `L₀(θ) = p_θ(D₀)`,

is an e-value under every null parameter: `E_{θ⋆}[T] ≤ 1` for `θ⋆ ∈ Θ₀`. Hence rejecting when
`T ≥ 1 / α` has type-I error at most `α`, uniformly over the null, at every sample size.

The argument: `L₀(θ̂₀) ≥ L₀(θ⋆)` because `θ̂₀` maximizes over a set containing `θ⋆`, so
`T ≤ L₀(θ̂₁) / L₀(θ⋆)`; conditionally on `D₁` the estimate `θ̂₁` is a fixed parameter and
`E_{θ⋆}[p_{θ̂₁}(D₀) / p_{θ⋆}(D₀)] = ∫ p_{θ̂₁} ≤ 1`.

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
  `P_{θ⋆} {T ≥ 1 / α} ≤ α` for every `θ⋆ ∈ Θ₀`.
* `isValidPValue_splitLRT`: `(max T 1)⁻¹` is a valid p-value.
* `measure_not_mem_universalConfidenceSet_le`: the **universal confidence set**
  `{θ | L₀(θ̂₁) / L₀(θ) < 1 / α}` covers the true parameter with probability at least `1 - α`.

The e-value consequences (Markov bound, e-to-p calibration) are those of `EValues.lean`; this
file proves only that the split construction produces an e-value.

Only the split half is formalized: the swapped statistic (roles of `D₀` and `D₁` exchanged) and
the cross-fit average `Wₙ = (Uₙ + Uₙ^swap) / 2` of Wasserman, Ramdas and Balakrishnan (2020),
eq. (5), are out of scope.

## Implementation notes

The law of `D₀` under `θ` is `ref.withDensity (ofReal ∘ p θ)` (`modelLaw`) for real
nonnegative densities `p θ` with `∫⁻ ofReal (p θ) ∂ref ≤ 1`; the sample space `X₀` is arbitrary,
so an i.i.d. sample of size `n` is the case `X₀ = Fin n → X` with a product density. The ratio
uses real division, so a zero denominator gives `T = 0`; validity needs no positivity, since
`p θ⋆ ≤ L` makes `p θ⋆ · (q / L) ≤ q` hold pointwise, including where `L = 0`. Where the
denominator vanishes and the numerator does not, the paper's statistic is `+∞` and this one is
`0`; that costs power off the null and puts zero-likelihood parameters into the confidence set,
but under `θ⋆` it happens with probability `0`, so the theorems are unaffected. The joint law is
`modelLaw ref p θ⋆ ⊗ ν` with `ν` the law of `D₁`; the theorems allow any probability measure
`ν`, in particular the model law of `D₁` under `θ⋆`.

## References

* L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, Proc. Natl. Acad. Sci.
  USA 117 (2020), 16880–16890 (Theorem 1: universal confidence set; Theorem 3: split LRT).
* A. Ramdas, P. Grünwald, V. Vovk and G. Shafer, *Game-theoretic statistics and safe anytime-valid
  inference*, Statist. Sci. 38 (2023), 576–601.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting.UniversalInference

open MeasureTheory

variable {Θ X₀ X₁ : Type*} {m₀ : MeasurableSpace X₀} {m₁ : MeasurableSpace X₁}

/-! ### Definitions -/

/-- The law of the inference split `D₀` under the parameter `θ`: the measure with density
`p θ` with respect to the reference measure `ref`. -/
noncomputable def modelLaw (ref : Measure X₀) (p : Θ → X₀ → ℝ) (θ : Θ) : Measure X₀ :=
  ref.withDensity fun x => ENNReal.ofReal (p θ x)

instance (ref : Measure X₀) [SFinite ref] (p : Θ → X₀ → ℝ) (θ : Θ) :
    SFinite (modelLaw ref p θ) := by
  unfold modelLaw
  infer_instance

/-- The **split likelihood ratio** with denominator `L`: at `z = (D₀, D₁)` it is
`p_{θ̂₁(D₁)}(D₀) / L(D₀)`, the likelihood of the inference split at the estimate fitted on the
estimation split, divided by `L(D₀)`. The split LRT takes `L(D₀)` to be the maximized null
likelihood (`splitLRT`); the universal confidence set takes `L = p θ` (`universalConfidenceSet`).

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

Source: Wasserman, Ramdas and Balakrishnan (2020), Section 2. -/
noncomputable def splitLRT (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (θ₀ : X₀ → Θ) : X₀ × X₁ → ℝ :=
  splitLR p θ₁ fun x => p (θ₀ x) x

/-- The rejection region of the level-`α` split LRT: `T ≥ 1 / α`. -/
def splitLRTRejects (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (θ₀ : X₀ → Θ) (α : ℝ) : Set (X₀ × X₁) :=
  {z | α⁻¹ ≤ splitLRT p θ₁ θ₀ z}

/-- The **universal confidence set** at level `α`: the parameters `θ` whose split likelihood
ratio `L₀(θ̂₁) / L₀(θ)` is below `1 / α`.

Source: Wasserman, Ramdas and Balakrishnan (2020), eq. (4). -/
def universalConfidenceSet (p : Θ → X₀ → ℝ) (θ₁ : X₁ → Θ) (α : ℝ) (z : X₀ × X₁) : Set Θ :=
  {θ | splitLR p θ₁ (p θ) z < α⁻¹}

/-! ### Validity of the split likelihood ratio -/

/-- The pointwise inequality behind universal inference: if `0 ≤ a ≤ L` and `0 ≤ q`, then
`a · (q / L) ≤ q`; for `L = 0` both sides of the ratio vanish under real division. -/
theorem mul_div_le_of_le {a q L : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (h : a ≤ L) :
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

Source: Wasserman, Ramdas and Balakrishnan (2020), proof of Theorem 1. -/
theorem isEValue_splitLR_section {ref : Measure X₀} {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ}
    {L : X₀ → ℝ} {θstar : Θ} (hp : ∀ θ x, 0 ≤ p θ x)
    (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1) (hpstar : Measurable (p θstar))
    (hT : Measurable (splitLR p θ₁ L)) (hdom : ∀ x, p θstar x ≤ L x) (y : X₁) :
    IsEValue (modelLaw ref p θstar) fun x => splitLR p θ₁ L (x, y) where
  nonneg x := div_nonneg (hp _ _) ((hp _ _).trans (hdom x))
  measurable := hT.comp measurable_prodMk_right
  lintegral_le_one := by
    have hg : Measurable fun x => ENNReal.ofReal (splitLR p θ₁ L (x, y)) :=
      (hT.comp measurable_prodMk_right).ennreal_ofReal
    rw [modelLaw, lintegral_withDensity_eq_lintegral_mul _ hpstar.ennreal_ofReal hg]
    refine le_trans (lintegral_mono fun x => ?_) (hdens (θ₁ y))
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hp _ _)]
    exact ENNReal.ofReal_le_ofReal (mul_div_le_of_le (hp _ _) (hp _ _) (hdom x))

/-- **The split likelihood ratio is an e-value** under the joint law `P_{θ⋆} ⊗ ν` of the two
independent splits, whenever its denominator dominates the true density `p θ⋆`. The law `ν` of
the estimation split is arbitrary.

Source: Wasserman, Ramdas and Balakrishnan (2020), Theorem 3. -/
theorem isEValue_splitLR {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {L : X₀ → ℝ} {θstar : Θ}
    (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hpstar : Measurable (p θstar)) (hT : Measurable (splitLR p θ₁ L))
    (hdom : ∀ x, p θstar x ≤ L x) :
    IsEValue ((modelLaw ref p θstar).prod ν) (splitLR p θ₁ L) where
  nonneg z := div_nonneg (hp _ _) ((hp _ _).trans (hdom z.1))
  measurable := hT
  lintegral_le_one := by
    rw [lintegral_prod_symm _ hT.ennreal_ofReal.aemeasurable]
    calc ∫⁻ y, ∫⁻ x, ENNReal.ofReal (splitLR p θ₁ L (x, y)) ∂modelLaw ref p θstar ∂ν
        ≤ ∫⁻ _y, 1 ∂ν := lintegral_mono fun y =>
          (isEValue_splitLR_section hp hdens hpstar hT hdom y).lintegral_le_one
      _ = 1 := by simp

/-- **Universal inference: the split LRT is an e-value under every null parameter.** If `θ̂₀`
is a null MLE on the inference split and `θ⋆ ∈ Θ₀`, then `T = L₀(θ̂₁) / L₀(θ̂₀)` is an e-value
under `P_{θ⋆} ⊗ ν`, whatever the estimator `θ̂₁` fitted on the estimation split.

Source: Wasserman, Ramdas and Balakrishnan (2020), Theorem 3. -/
theorem isEValue_splitLRT {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θ₀ : X₀ → Θ} {Θ₀ : Set Θ}
    {θstar : Θ} (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hmle : IsNullMLE p Θ₀ θ₀) (hstar : θstar ∈ Θ₀) (hpstar : Measurable (p θstar))
    (hT : Measurable (splitLRT p θ₁ θ₀)) :
    IsEValue ((modelLaw ref p θstar).prod ν) (splitLRT p θ₁ θ₀) :=
  isEValue_splitLR hp hdens hpstar hT fun x => hmle.le_max x θstar hstar

/-- **Finite-sample type-I error control of the split LRT.** For every null parameter
`θ⋆ ∈ Θ₀` and every `α > 0`, the test rejecting when `T ≥ 1 / α` has
`P_{θ⋆} (reject) ≤ α`.

Source: Wasserman, Ramdas and Balakrishnan (2020), Theorem 3. -/
theorem measure_splitLRTRejects_le {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θ₀ : X₀ → Θ} {Θ₀ : Set Θ}
    {θstar : Θ} (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hmle : IsNullMLE p Θ₀ θ₀) (hstar : θstar ∈ Θ₀) (hpstar : Measurable (p θstar))
    (hT : Measurable (splitLRT p θ₁ θ₀)) {α : ℝ} (hα : 0 < α) :
    (modelLaw ref p θstar).prod ν (splitLRTRejects p θ₁ θ₀ α) ≤ ENNReal.ofReal α := by
  have h := (isEValue_splitLRT (ν := ν) hp hdens hmle hstar hpstar hT).measure_ge_le
    (inv_pos.2 hα)
  rwa [inv_inv] at h

/-- **The split-LRT p-value is valid.** Under every null parameter, `(max T 1)⁻¹` is a valid
p-value, when the law of the inference split is a probability measure. -/
theorem isValidPValue_splitLRT {ref : Measure X₀} [SFinite ref] {ν : Measure X₁}
    [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θ₀ : X₀ → Θ} {Θ₀ : Set Θ}
    {θstar : Θ} [IsProbabilityMeasure (modelLaw ref p θstar)] (hp : ∀ θ x, 0 ≤ p θ x)
    (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1) (hmle : IsNullMLE p Θ₀ θ₀)
    (hstar : θstar ∈ Θ₀) (hpstar : Measurable (p θstar)) (hT : Measurable (splitLRT p θ₁ θ₀)) :
    IsValidPValue ((modelLaw ref p θstar).prod ν) fun z => (max (splitLRT p θ₁ θ₀ z) 1)⁻¹ :=
  (isEValue_splitLRT hp hdens hmle hstar hpstar hT).isValidPValue

/-- **Coverage of the universal confidence set.** The true parameter lies outside the level-`α`
universal confidence set with probability at most `α`.

Source: Wasserman, Ramdas and Balakrishnan (2020), Theorem 1. -/
theorem measure_not_mem_universalConfidenceSet_le {ref : Measure X₀} [SFinite ref]
    {ν : Measure X₁} [IsProbabilityMeasure ν] {p : Θ → X₀ → ℝ} {θ₁ : X₁ → Θ} {θstar : Θ}
    (hp : ∀ θ x, 0 ≤ p θ x) (hdens : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂ref ≤ 1)
    (hpstar : Measurable (p θstar)) (hT : Measurable (splitLR p θ₁ (p θstar))) {α : ℝ}
    (hα : 0 < α) :
    (modelLaw ref p θstar).prod ν {z | θstar ∉ universalConfidenceSet p θ₁ α z} ≤
      ENNReal.ofReal α := by
  have hset : {z | θstar ∉ universalConfidenceSet p θ₁ α z} =
      {z | α⁻¹ ≤ splitLR p θ₁ (p θstar) z} := by
    ext z
    simp [universalConfidenceSet]
  have h := (isEValue_splitLR (ν := ν) hp hdens hpstar hT fun _ => le_rfl).measure_ge_le
    (inv_pos.2 hα)
  rwa [inv_inv, ← hset] at h

end MathlibExt.Probability.Statistics.MultipleTesting.UniversalInference
