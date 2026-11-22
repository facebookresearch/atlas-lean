/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMarkovProperty
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Tests for the generic independent-increments path identity

The historical import/API is exercised along with a nonstationary square-path model.
The bounded functional observes different centered future laws at times zero and one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.BrownianMarkovProperty
open scoped ENNReal NNReal

namespace MathlibExtTest.BrownianMarkovProperty

/-- A degenerate process: identically zero. -/
def zeroPath : ℝ≥0 → ℝ → ℝ := fun _ _ => 0

/-- The bottom filtration on `ℝ`. -/
def botFiltration : Filtration ℝ≥0 Real.measurableSpace :=
  ⟨fun _ => ⊥, fun _ _ _ => bot_le, fun _ => bot_le⟩

example : BmAdapted zeroPath botFiltration := by
  intro t
  exact measurable_const

example : BmIndepIncrements zeroPath botFiltration (Measure.dirac (0 : ℝ)) := by
  intro s t _
  have hfun : (fun ω : ℝ => zeroPath t ω - zeroPath s ω) = fun _ => (0 : ℝ) := by
    funext ω
    simp [zeroPath]
  rw [hfun, MeasurableSpace.comap_const]
  show Indep (⊥ : MeasurableSpace ℝ) ⊥ (Measure.dirac (0 : ℝ))
  exact indep_bot_left ⊥

example (Y : (ℝ≥0 → ℝ) → ℝ) (hY : Measurable Y) (x : ℝ) :
    bmPathExpectation zeroPath (Measure.dirac (0 : ℝ)) 0 Y x = Y (fun _ => x) := by
  have hmeas : Measurable fun f : ℝ≥0 → ℝ => Y (fun t => x + f t) := by
    apply hY.comp
    apply Measurable.of_eval
    intro t
    exact measurable_const.add (measurable_pi_apply t)
  have hmeasShift : Measurable (bmCenteredShift zeroPath 0) := by
    apply Measurable.of_eval
    intro t
    show Measurable fun _ : ℝ => (0 : ℝ) - 0
    exact measurable_const
  show (∫ f, Y (fun t => x + f t)
    ∂(bmCenteredLaw zeroPath (Measure.dirac (0 : ℝ)) 0)) = Y (fun _ => x)
  show (∫ f, Y (fun t => x + f t)
    ∂(Measure.map (bmCenteredShift zeroPath 0) (Measure.dirac (0 : ℝ)))) = Y (fun _ => x)
  rw [MeasureTheory.integral_map hmeasShift.aemeasurable hmeas.aestronglyMeasurable,
    MeasureTheory.integral_dirac]
  congr 1
  funext t
  simp [bmCenteredShift, zeroPath]

example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 m0} (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) (s : ℝ≥0) {Y : (ℝ≥0 → ℝ) → ℝ}
    (hY : Measurable Y) {C : ℝ} (hYb : ∀ p, |Y p| ≤ C) (A : Set Ω)
    (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, Y (bmShifted B s ω) ∂μ
      = ∫ ω in A, bmPathExpectation B μ s Y (B s ω) ∂μ :=
  brownian_markov_setIntegral hAd hInd s hY hYb A hA

example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 m0} (hAd : BmAdapted B ℱ)
    (hInd : BmIndepIncrements B ℱ μ) (s : ℝ≥0) {Y : (ℝ≥0 → ℝ) → ℝ}
    (hY : Measurable Y) {C : ℝ} (hYb : ∀ p, |Y p| ≤ C) :
    μ[fun ω => Y (bmShifted B s ω) | ℱ s] =ᵐ[μ]
      fun ω => bmPathExpectation B μ s Y (B s ω) :=
  brownian_markov_condExp hAd hInd s hY hYb


/-- A deterministic process with nonstationary increments. -/
private noncomputable def squarePath : ℝ≥0 → ℝ → ℝ := fun t _ => (t : ℝ) ^ 2

private lemma squarePath_adapted : BmAdapted squarePath botFiltration := by
  intro t
  exact measurable_const

private lemma squarePath_indep :
    BmIndepIncrements squarePath botFiltration (Measure.dirac (0 : ℝ)) := by
  intro s t _
  change Indep (⊥ : MeasurableSpace ℝ)
    (MeasurableSpace.comap (fun _ : ℝ => (t : ℝ) ^ 2 - (s : ℝ) ^ 2) inferInstance)
    (Measure.dirac (0 : ℝ))
  rw [MeasurableSpace.comap_const]
  exact indep_bot_left ⊥

/-- A bounded measurable functional of the path at time one. -/
private noncomputable def boundedEval (p : ℝ≥0 → ℝ) : ℝ := p 1 / (1 + |p 1|)

private lemma boundedEval_measurable : Measurable boundedEval := by
  have h : Measurable (fun p : ℝ≥0 → ℝ => p 1) := measurable_pi_apply 1
  have habs : Measurable (fun p : ℝ≥0 → ℝ => |p 1|) := by
    simpa only [Real.norm_eq_abs] using (Measurable.norm h)
  exact Measurable.div h (measurable_const.add habs)

private lemma boundedEval_bound (p : ℝ≥0 → ℝ) : |boundedEval p| ≤ 1 := by
  unfold boundedEval
  rw [abs_div, abs_of_pos (by positivity : 0 < 1 + |p 1|)]
  exact (div_le_one (by positivity : 0 < 1 + |p 1|)).mpr (by linarith)

private lemma squarePath_expectation (s : ℝ≥0) (x : ℝ) :
    bmPathExpectation squarePath (Measure.dirac (0 : ℝ)) s boundedEval x =
      boundedEval (fun t => x + (((s + t : ℝ≥0) : ℝ) ^ 2 - (s : ℝ) ^ 2)) := by
  have htrans : Measurable fun f : ℝ≥0 → ℝ => boundedEval (fun t => x + f t) := by
    apply boundedEval_measurable.comp
    apply Measurable.of_eval
    intro t
    exact measurable_const.add (measurable_pi_apply t)
  unfold bmPathExpectation bmCenteredLaw
  rw [MeasureTheory.integral_map (measurable_bmCenteredShift squarePath_adapted s).aemeasurable
    htrans.aestronglyMeasurable, MeasureTheory.integral_dirac]
  rfl

/-- At the same starting state, the centered future expectation varies with absolute time. -/
example :
    bmPathExpectation squarePath (Measure.dirac (0 : ℝ)) 0 boundedEval 0 = 1 / 2 ∧
    bmPathExpectation squarePath (Measure.dirac (0 : ℝ)) 1 boundedEval 0 = 3 / 4 := by
  constructor <;> rw [squarePath_expectation] <;> norm_num [boundedEval]

/-- The nonstationary expectations are distinct. -/
example :
    bmPathExpectation squarePath (Measure.dirac (0 : ℝ)) 0 boundedEval 0 ≠
      bmPathExpectation squarePath (Measure.dirac (0 : ℝ)) 1 boundedEval 0 := by
  rw [squarePath_expectation, squarePath_expectation]
  norm_num [boundedEval]

/-- The generic identity still gives the actual shifted-path conditional expectation. -/
example :
    (Measure.dirac (0 : ℝ))[fun ω => boundedEval (bmShifted squarePath 1 ω) |
      botFiltration 1] =ᵐ[Measure.dirac (0 : ℝ)] fun _ => (4 : ℝ) / 5 := by
  have h := MathlibExt.Probability.IndependentIncrementsMarkovProperty.independent_increments_condExp
    squarePath_adapted squarePath_indep 1 boundedEval_measurable boundedEval_bound
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  change bmPathExpectation squarePath (Measure.dirac (0 : ℝ)) 1 boundedEval
    (squarePath 1 ω) = (4 : ℝ) / 5
  rw [squarePath_expectation]
  norm_num [boundedEval, squarePath]

end MathlibExtTest.BrownianMarkovProperty

#print axioms MathlibExt.Probability.BrownianMarkovProperty.brownian_markov_setIntegral
#print axioms MathlibExt.Probability.BrownianMarkovProperty.brownian_markov_condExp

#eval "Independent increments: legacy API, zero process, and nonstationary square process checked"

-- Every original source-level public name remains accessible through the legacy module.
#check MathlibExt.Probability.BrownianMarkovProperty.bmPrev
#check MathlibExt.Probability.BrownianMarkovProperty.bmInc
#check MathlibExt.Probability.BrownianMarkovProperty.bmShifted
#check MathlibExt.Probability.BrownianMarkovProperty.bmCenteredShift
#check MathlibExt.Probability.BrownianMarkovProperty.bmCenteredLaw
#check MathlibExt.Probability.BrownianMarkovProperty.bmPathExpectation
#check MathlibExt.Probability.BrownianMarkovProperty.BmAdapted
#check MathlibExt.Probability.BrownianMarkovProperty.BmIndepIncrements
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_bmShifted
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_bmCenteredShift
#check MathlibExt.Probability.BrownianMarkovProperty.bmCenteredLaw_isProbabilityMeasure
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_bmInc_of_le
#check MathlibExt.Probability.BrownianMarkovProperty.bmPrev_insert_of_lt
#check MathlibExt.Probability.BrownianMarkovProperty.bmPrev_insert_self
#check MathlibExt.Probability.BrownianMarkovProperty.measure_inter_biInter_bmInc
#check MathlibExt.Probability.BrownianMarkovProperty.sum_bmInc_eq
#check MathlibExt.Probability.BrownianMarkovProperty.bmCentered_eq_sum_bmInc
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_bmInc
#check MathlibExt.Probability.BrownianMarkovProperty.bmIncRectangles
#check MathlibExt.Probability.BrownianMarkovProperty.bmIncSigma
#check MathlibExt.Probability.BrownianMarkovProperty.measurableSet_bmInc_preimage
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_bmInc_incSigma
#check MathlibExt.Probability.BrownianMarkovProperty.indep_bmIncSigma
#check MathlibExt.Probability.BrownianMarkovProperty.bmCenteredCylinders
#check MathlibExt.Probability.BrownianMarkovProperty.measurableSet_bmCentered_cylinder
#check MathlibExt.Probability.BrownianMarkovProperty.measurableSet_pi_eval_preimage
#check MathlibExt.Probability.BrownianMarkovProperty.indep_bmCenteredShift
#check MathlibExt.Probability.BrownianMarkovProperty.bmPathCylinders
#check MathlibExt.Probability.BrownianMarkovProperty.isPiSystem_bmPathCylinders
#check MathlibExt.Probability.BrownianMarkovProperty.pi_eq_generateFrom_bmPathCylinders
#check MathlibExt.Probability.BrownianMarkovProperty.bmCylRectangles
#check MathlibExt.Probability.BrownianMarkovProperty.isPiSystem_bmCylRectangles
#check MathlibExt.Probability.BrownianMarkovProperty.mem_generateFrom_bmCylRectangles
#check MathlibExt.Probability.BrownianMarkovProperty.prod_eq_generateFrom_bmCylRectangles
#check MathlibExt.Probability.BrownianMarkovProperty.bmPair
#check MathlibExt.Probability.BrownianMarkovProperty.bmPhi
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_bmPair
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_bmPhi
#check MathlibExt.Probability.BrownianMarkovProperty.bmPhi_bmPair
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_section_bmCenteredLaw
#check MathlibExt.Probability.BrownianMarkovProperty.pair_section_rectangle
#check MathlibExt.Probability.BrownianMarkovProperty.pair_section_lintegral
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_lintegral_bmPhi
#check MathlibExt.Probability.BrownianMarkovProperty.brownian_lintegral_shift
#check MathlibExt.Probability.BrownianMarkovProperty.measurable_bmPathExpectation
#check MathlibExt.Probability.BrownianMarkovProperty.bmPathExpectation_bound
#check MathlibExt.Probability.BrownianMarkovProperty.bmPathExpectation_setIntegral
#check MathlibExt.Probability.BrownianMarkovProperty.brownian_markov_setIntegral
#check MathlibExt.Probability.BrownianMarkovProperty.brownian_markov_condExp
