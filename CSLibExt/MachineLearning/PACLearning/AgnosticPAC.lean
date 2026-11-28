/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.MachineLearning.PACLearning.Defs
public import CSLibExt.MachineLearning.GeneralizationBounds.ApproximationEstimation
public import CSLibExt.MachineLearning.PACLearning.RiskBridge

/-!
# Agnostic PAC learnability for general losses

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to
Algorithms* (Cambridge University Press, 2014), Definition 3.4 (p. 49): a
hypothesis class `H` is agnostic PAC learnable for a loss on a set `Z` when a
sample-complexity function and an algorithm exist such that, for every accuracy
and confidence parameter in `(0, 1)` and every distribution over `Z`, at every
sample size at least the sample complexity the algorithm returns `h ∈ H` whose
expected loss is at most `min_{h' ∈ H} L_D(h') + ε` with probability at least
`1 - δ`. A generalized loss is any function from `H × Z` to the nonnegative
reals; risk is expected loss (Section 3.2.2, pp. 48-49). Each loss is viewed as
a random variable whose expectation requires measurability (Remark 3.1, p. 49).
Proper learning returns a hypothesis in `H`; representation-independent
learning may return one outside it (Remark 3.2, p. 49).

This file states the general-loss notion as a separate predicate, mirroring
CSLib's fixed-sample 0-1 predicates rather than the source
sample-complexity-function syntax. CSLib's `IsPACLearnerFor m ε δ C 𝒟`
existentially provides a learner at a fixed sample size `m`, with accuracy and
confidence in `Set.Ioo (0 : ℝ≥0) 1`, an arbitrary distribution family, outer
`ℝ≥0∞` measure, and the `optimalError` benchmark; `IsPACLearnable` quantifies
over accuracy and confidence and existentially provides `m`. The predicates
below have the analogous fixed-`m` and learnable layers, benchmark by
`approximationError`, and measure the failure event with the product measure,
so the 0-1 bridge and monotonicity lemmas compose with the CSLib API. The
fixed-sample predicate is a per-sample-size statement: a learner is provided
per accuracy, confidence, and sample size. The learnability predicate packages
the CSLib existential sample-size form, providing some sample size per
accuracy and confidence. This file does not introduce a sample-complexity
function or state an equivalence theorem with the source all-larger-sample-size
syntax. A source uniform algorithm restricts to a witnessed sample size,
modulo the finite-risk reading below. This is a representation decision, not a
claim that the two syntaxes are definitionally identical.

The learner is not required to land in `C`: the benchmark is over `C` but the
existential learner is unrestricted, matching `IsPACLearnerFor`. This is
representation-independent learning in Remark 3.2 terminology; it does not
encode the source proper-return requirement.

Risks are genuine expectations: for each admitted probability law, every
hypothesis loss used in a risk expression (the class members feeding the
benchmark and the learner outputs feeding the failure event) is integrable
and almost-everywhere nonnegative. Without integrability the real integral
is junk (zero on nonintegrable functions), so the bound would be meaningless;
the predicate asserts these facts rather than gating on them.

## Main definitions

* `IsAgnosticPACLearnerFor`: fixed-sample general-loss PAC learner.
* `IsAgnosticPACLearnable`: general-loss PAC learnability.

## Main statements

* `IsAgnosticPACLearnerFor.mono_δ`, `.mono_ε`, `.antitone_family`.
* `IsPACLearnerFor.toIsAgnosticPACLearnerFor_zeroOneLoss`: the 0-1 bridge.

No uniform-convergence, ERM-learnability, or randomized-learner statements:
this file defines the predicates, the valid CSLib-shape monotonicity lemmas,
and the one-direction 0-1 bridge only. Class antitonicity is not stated: the
`sInf`-image benchmark needs a nonempty class for monotonicity, and on the
empty class the benchmark is `sInf ∅ = 0`, so the unguarded form fails.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open CSLibExt.MachineLearning.GeneralizationBounds (risk approximationError)
open scoped ENNReal NNReal

/-- **Fixed-sample agnostic PAC learner for a general loss.**
`IsAgnosticPACLearnerFor L m ε δ C 𝒟` asserts that some learner using `m`
samples is `(ε, δ)`-correct for the class `C` over the distribution family
`𝒟`: for every probability law `D ∈ 𝒟`, the class losses and the learner
outputs are integrable and almost-everywhere nonnegative (so every risk below
is a genuine expectation), and the product measure of the samples on which
the output risk exceeds the infimum class risk `approximationError L D C` by
more than `ε` is at most `δ`.

The accuracy and confidence parameters are `Set.Ioo (0 : ℝ≥0) 1` elements, as
in `IsPACLearnerFor`, so the endpoints `0` and `1` are excluded. No
measurability is required of the learner or of the failure event; the product
measure of that event is read as outer measure, as in CSLib. Risks are finite
real expectations under this predicate, with no extended infinite-risk
reading. Over broad families, especially the universal family, used losses
must still be integrable and almost-everywhere nonnegative under every
admitted law, so unbounded losses require restricting the distribution family
to laws under which the used losses are integrable. The output is
representation-independent (Remark 3.2): it need not lie in `C`. On the
empty class the benchmark is `sInf ∅ = 0`, so the predicate demands risk at
most `ε` with probability at least `1 - δ`; unlike `IsPACLearnerFor`, it is
not vacuous there. -/
def IsAgnosticPACLearnerFor {H Z : Type*} [MeasurableSpace Z]
    (L : H → Z → ℝ) (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (C : Set H) (𝒟 : Set (Measure Z)) : Prop :=
  ∃ A : (Fin m → Z) → H,
    ∀ (D : Measure Z) [IsProbabilityMeasure D], D ∈ 𝒟 →
      (∀ h ∈ C, Integrable (L h) D) ∧
      (∀ h ∈ C, ∀ᵐ z ∂D, 0 ≤ L h z) ∧
      (∀ S : Fin m → Z, Integrable (L (A S)) D) ∧
      (∀ S : Fin m → Z, ∀ᵐ z ∂D, 0 ≤ L (A S) z) ∧
      (Measure.pi (fun _ : Fin m => D))
        {S : Fin m → Z |
          approximationError L D C + (ε.val : ℝ) < risk L D (A S)} ≤
        (δ.val : ℝ≥0∞)

/-- **Agnostic PAC learnability for a general loss.** The class `C` is
learnable over `𝒟` when for every accuracy `ε` and confidence `δ` in `(0, 1)`
some sample size admits an `(ε, δ)`-learner. This mirrors `IsPACLearnable`:
one learner per accuracy, confidence, and sample size, not one algorithm
uniform over all larger sample sizes. Here `agnostic` means competing with
the infimum risk over `C` without a realizability assumption, while the
distribution family remains explicit. The finite-risk convention from
`IsAgnosticPACLearnerFor` applies. The output is representation-independent
and may leave `C`; proper learning is recovered by taking hypotheses in the
subtype of `C`, restricting the loss, and using the universal class there. -/
def IsAgnosticPACLearnable {H Z : Type*} [MeasurableSpace Z]
    (L : H → Z → ℝ) (C : Set H) (𝒟 : Set (Measure Z)) : Prop :=
  ∀ (ε δ : Set.Ioo (0 : ℝ≥0) 1),
    ∃ m, IsAgnosticPACLearnerFor L m ε δ C 𝒟

/-- A general-loss PAC learner with confidence `δ₁` is also one with any
weaker confidence `δ₂ ≥ δ₁`: the failure-probability bound only gets
looser. -/
theorem IsAgnosticPACLearnerFor.mono_δ {H Z : Type*} [MeasurableSpace Z]
    {L : H → Z → ℝ} {m : ℕ} {ε : Set.Ioo (0 : ℝ≥0) 1}
    {δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val)
    {C : Set H} {𝒟 : Set (Measure Z)}
    (h : IsAgnosticPACLearnerFor L m ε δ₁ C 𝒟) :
    IsAgnosticPACLearnerFor L m ε δ₂ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => ?_⟩
  obtain ⟨hintC, hnnC, hintA, hnnA, hmeas⟩ := @hA D inst hD
  refine ⟨hintC, hnnC, hintA, hnnA, le_trans hmeas ?_⟩
  exact_mod_cast hδ

/-- A general-loss PAC learner with accuracy `ε₁` is also one with any weaker
accuracy `ε₂ ≥ ε₁`: the bad event only shrinks. -/
theorem IsAgnosticPACLearnerFor.mono_ε {H Z : Type*} [MeasurableSpace Z]
    {L : H → Z → ℝ} {m : ℕ} {δ : Set.Ioo (0 : ℝ≥0) 1}
    {ε₁ ε₂ : Set.Ioo (0 : ℝ≥0) 1} (hε : ε₁.val ≤ ε₂.val)
    {C : Set H} {𝒟 : Set (Measure Z)}
    (h : IsAgnosticPACLearnerFor L m ε₁ δ C 𝒟) :
    IsAgnosticPACLearnerFor L m ε₂ δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => ?_⟩
  obtain ⟨hintC, hnnC, hintA, hnnA, hmeas⟩ := @hA D inst hD
  refine ⟨hintC, hnnC, hintA, hnnA, le_trans (measure_mono ?_) hmeas⟩
  intro S hS
  have hε' : (ε₁.val : ℝ) ≤ (ε₂.val : ℝ) := by exact_mod_cast hε
  have hS' : approximationError L D C + (ε₂.val : ℝ) < risk L D (A S) := hS
  exact lt_of_le_of_lt (add_le_add_right hε' _) hS'

/-- The general-loss PAC learner predicate is antitone in the distribution
family: a learner for a larger family is also a learner for any
subfamily. -/
theorem IsAgnosticPACLearnerFor.antitone_family {H Z : Type*} [MeasurableSpace Z]
    {L : H → Z → ℝ} {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : Set H} {𝒟 𝒟' : Set (Measure Z)}
    (h𝒟 : 𝒟 ⊆ 𝒟') (h : IsAgnosticPACLearnerFor L m ε δ C 𝒟') :
    IsAgnosticPACLearnerFor L m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, fun D inst hD => @hA D inst (h𝒟 hD)⟩

/-- **The 0-1 bridge: a CSLib PAC learner is a general-loss PAC learner at
`zeroOneLoss`.** Given a 0-1 `(ε, δ)`-learner for `C` over `𝒟`, the same
learner witnesses the general-loss predicate at the 0-1 loss, provided the
class is nonempty (without nonemptiness, the 0-1 side is vacuous while the
general-loss side has benchmark zero and need not hold; nonemptiness also
keeps the benchmark finite when carrying the strict failure inequality from
ENNReal to the reals) and every disagreement set is measurable (so each 0-1
risk is the real
error). The 0-1 integrability, nonnegativity, and finiteness facts are
derived from measurability and the probability instance during the proof,
not taken as hypotheses. The measurability hypothesis ranges over every
classifier: the CSLib predicate hides its learner, so the statement cannot
restrict to class members or attained outputs. On domains admitting
nonmeasurable classifiers, such as Borel real inputs with `Bool` labels, it
may be unsatisfiable. Direct use is therefore for settings where every
disagreement set is measurable, in particular discrete settings. A
learner-explicit bridge for general Borel domains is a separate statement
and is not introduced in this file. CSLib 0-1 semantics are unchanged: this
is one direction only, at `zeroOneLoss`. -/
theorem IsPACLearnerFor.toIsAgnosticPACLearnerFor_zeroOneLoss
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass X Y} {𝒟 : Set (Measure (X × Y))}
    (h : IsPACLearnerFor m ε δ C 𝒟) (hne : C.Nonempty)
    (hmeas : ∀ h : X → Y, MeasurableSet {p : X × Y | h p.1 ≠ p.2}) :
    IsAgnosticPACLearnerFor zeroOneLoss m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => ?_⟩
  have hzo : ∀ h : X → Y,
      zeroOneLoss h = {p : X × Y | h p.1 ≠ p.2}.indicator (fun _ => 1) :=
    fun h => rfl
  have hInt : ∀ h : X → Y, Integrable (zeroOneLoss h) D := by
    intro h
    rw [hzo h, integrable_indicator_iff (hmeas h)]
    exact (integrable_const 1).integrableOn
  have hnn : ∀ h : X → Y, ∀ᵐ z ∂D, 0 ≤ zeroOneLoss h z := by
    intro h
    rw [hzo h]
    exact Filter.Eventually.of_forall fun z =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) z
  have hrisk : ∀ h : X → Y, risk zeroOneLoss D h = (error D h).toReal :=
    fun h => risk_zeroOneLoss_eq_toReal_error D h (hmeas h)
  have herr1 : ∀ h : X → Y, error D h ≤ 1 := fun h => prob_le_one
  have herrNe : ∀ h : X → Y, error D h ≠ ⊤ := fun h =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (herr1 h)
  obtain ⟨c₀, hc₀⟩ := hne
  have hopt_le : optimalError D C ≤ error D c₀ := by
    unfold optimalError
    exact iInf₂_le c₀ hc₀
  have hoptNe : optimalError D C ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans hopt_le (herr1 c₀))
  have himg : risk zeroOneLoss D '' C = ENNReal.toReal '' (error D '' C) := by
    rw [Set.image_image]
    exact Set.image_congr (fun c _ => hrisk c)
  have hfin : ∀ r ∈ error D '' C, r ≠ ⊤ := by
    rintro r ⟨c, _, rfl⟩
    exact herrNe c
  have happ : approximationError zeroOneLoss D C = (optimalError D C).toReal := by
    simp only [approximationError, optimalError]
    rw [himg, ← ENNReal.toReal_sInf _ hfin, sInf_image]
  have hcoe : ((ε.val : ℝ≥0) : ℝ≥0∞).toReal = (ε.val : ℝ) :=
    (congrArg ENNReal.toReal (ENNReal.coe_nnreal_eq _)).trans
      (ENNReal.toReal_ofReal (NNReal.coe_nonneg _))
  have hsum : (optimalError D C + (ε.val : ℝ≥0∞)).toReal
      = (optimalError D C).toReal + (ε.val : ℝ) := by
    rw [ENNReal.toReal_add hoptNe ENNReal.coe_ne_top, hcoe]
  have hsumNe : optimalError D C + (ε.val : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hoptNe, ENNReal.coe_ne_top⟩
  have hfail : {S : Fin m → X × Y |
        approximationError zeroOneLoss D C + (ε.val : ℝ) < risk zeroOneLoss D (A S)} =
      {S : Fin m → X × Y |
        optimalError D C + (ε.val : ℝ≥0∞) < error D (A S)} := by
    ext S
    simp only [Set.mem_ofPred_eq]
    rw [happ, hrisk (A S), ← hsum, ENNReal.toReal_lt_toReal hsumNe (herrNe (A S))]
  refine ⟨fun c _ => hInt c, fun c _ => hnn c, fun S => hInt (A S),
    fun S => hnn (A S), ?_⟩
  rw [hfail]
  exact @hA D inst hD

end Cslib.MachineLearning.PACLearning
