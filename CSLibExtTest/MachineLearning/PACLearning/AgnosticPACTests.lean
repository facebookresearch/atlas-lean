/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.AgnosticPAC
public import CSLibExt.MachineLearning.PACLearning.AgnosticFiniteClass

@[expose] public section

/-!
# Agnostic PAC tests

Closed checks for the general-loss agnostic PAC predicates. A squared-error
singleton class on `Bool` is learnable by a constant learner; the empty-class
benchmark is zero; the zero loss is learner-correct at sample size zero; a
negative loss is rejected from the definition; the three monotonicity lemmas
apply to the closed singleton learner; and the 0-1 bridge applies to a
finite-class PAC learner on `Bool × Bool`.
-/

namespace CSLibExtTest.MachineLearning.PACLearning.AgnosticPAC

open MeasureTheory
open Cslib.MachineLearning.PACLearning
open CSLibExt.MachineLearning.GeneralizationBounds (risk approximationError)
open scoped ENNReal NNReal

/-- Closed accuracy `1 / 4`. -/
private noncomputable def epsQ : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 4, by norm_num, by norm_num⟩

/-- Closed accuracy `1 / 2`. -/
private noncomputable def epsH : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Closed confidence `1 / 2`. -/
private noncomputable def delH : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Closed confidence `3 / 4`. -/
private noncomputable def delT : Set.Ioo (0 : ℝ≥0) 1 := ⟨3 / 4, by norm_num, by norm_num⟩

/-- Closed accuracy and confidence `4 / 5` for the 0-1 bridge instance. -/
private noncomputable def briE : Set.Ioo (0 : ℝ≥0) 1 := ⟨4 / 5, by norm_num, by norm_num⟩

/-- Squared error of a Boolean prediction against a Boolean label. -/
private def sqLoss : Bool → Bool → ℝ :=
  fun h z => ((if h then (1 : ℝ) else 0) - (if z then (1 : ℝ) else 0)) ^ 2

/-- The always-true hypothesis has integrable squared-error loss under every
probability law on `Bool`: measurability is by finiteness and the loss is
bounded by `1`. -/
private theorem sqLoss_int (D : Measure Bool) [IsProbabilityMeasure D] :
    Integrable (sqLoss true) D := by
  apply Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro z
  cases z <;> norm_num [sqLoss]

/-- The always-true squared-error loss is almost-everywhere nonnegative. -/
private theorem sqLoss_nn (D : Measure Bool) : ∀ᵐ z ∂D, 0 ≤ sqLoss true z := by
  apply Filter.Eventually.of_forall
  intro z
  simp only [sqLoss]
  positivity

/-- The singleton benchmark is the single risk. -/
private theorem sqLoss_approx (D : Measure Bool) [IsProbabilityMeasure D] :
    approximationError sqLoss D {true} = risk sqLoss D true := by
  simp only [approximationError, Set.image_singleton, csInf_singleton]

/-- The squared-error singleton is learner-correct by the constant learner at
every accuracy and confidence: the benchmark equals the output risk, so the
failure event is empty. -/
private theorem sqLearner (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    IsAgnosticPACLearnerFor sqLoss 5 ε δ {true} Set.univ := by
  refine ⟨fun _ => true, fun D inst _ => ?_⟩
  have hmem : ∀ h : Bool, h ∈ ({true} : Set Bool) → Integrable (sqLoss h) D := by
    intro h hh
    simp only [Set.mem_singleton_iff] at hh
    subst hh
    exact sqLoss_int D
  have hnnmem : ∀ h : Bool, h ∈ ({true} : Set Bool) → ∀ᵐ z ∂D, 0 ≤ sqLoss h z := by
    intro h hh
    simp only [Set.mem_singleton_iff] at hh
    subst hh
    exact sqLoss_nn D
  have hεpos : (0 : ℝ) < (ε.val : ℝ) := by exact_mod_cast ε.property.1
  have hsub : {S : Fin 5 → Bool |
      approximationError sqLoss D {true} + (ε.val : ℝ) < risk sqLoss D true} ⊆ ∅ := by
    intro S hS
    simp only [Set.mem_ofPred_eq, sqLoss_approx D] at hS
    have hcon : (ε.val : ℝ) < 0 := by linarith
    exact absurd hcon (not_lt.mpr hεpos.le)
  have htail : (Measure.pi fun _ : Fin 5 => D) ∅ ≤ (δ.val : ℝ≥0∞) := by simp
  refine ⟨hmem, hnnmem, fun S => sqLoss_int D, fun S => sqLoss_nn D, ?_⟩
  exact le_trans (measure_mono hsub) htail

/-- The closed singleton learner at accuracy `1 / 4`, confidence `1 / 2`. -/
private theorem sqClosed :
    IsAgnosticPACLearnerFor sqLoss 5 epsQ delH {true} Set.univ :=
  sqLearner epsQ delH

private theorem epsQ_le_epsH : epsQ.val ≤ epsH.val := by
  show (1 / 4 : ℝ≥0) ≤ 1 / 2
  rw [← NNReal.coe_le_coe]
  norm_num

private theorem delH_le_delT : delH.val ≤ delT.val := by
  show (1 / 2 : ℝ≥0) ≤ 3 / 4
  rw [← NNReal.coe_le_coe]
  norm_num

/-- The identically-zero loss. -/
private def zeroLoss : Unit → Bool → ℝ := fun _ _ => 0

private theorem zeroLoss_int (D : Measure Bool) [IsProbabilityMeasure D] (h : Unit) :
    Integrable (zeroLoss h) D := by
  have hz : zeroLoss h = fun _ => (0 : ℝ) := rfl
  rw [hz]
  exact integrable_const 0

private theorem zeroLoss_nn (D : Measure Bool) (h : Unit) :
    ∀ᵐ z ∂D, 0 ≤ zeroLoss h z :=
  Filter.Eventually.of_forall fun _ => le_refl 0

private theorem zeroLoss_risk (D : Measure Bool) [IsProbabilityMeasure D] (h : Unit) :
    risk zeroLoss D h = 0 := by
  simp only [risk, zeroLoss, integral_zero]

private theorem zeroLoss_approx (D : Measure Bool) [IsProbabilityMeasure D] :
    approximationError zeroLoss D {()} = 0 := by
  simp only [approximationError, Set.image_singleton, zeroLoss_risk, csInf_singleton]

/-- The identically-`(-1)` loss, violating almost-everywhere nonnegativity. -/
private def negLoss : Unit → Bool → ℝ := fun _ _ => -1

/-- A squared-error singleton class on a finite example space is agnostic PAC
learnable: the constant learner works at every accuracy and confidence. -/
example : IsAgnosticPACLearnable sqLoss {true} Set.univ := fun ε δ => ⟨5, sqLearner ε δ⟩

/-- Confidence monotonicity on the closed singleton learner. -/
example : IsAgnosticPACLearnerFor sqLoss 5 epsQ delT {true} Set.univ :=
  sqClosed.mono_δ delH_le_delT

/-- Accuracy monotonicity on the closed singleton learner. -/
example : IsAgnosticPACLearnerFor sqLoss 5 epsH delH {true} Set.univ :=
  sqClosed.mono_ε epsQ_le_epsH

/-- Distribution-family antitonicity on the closed singleton learner. -/
example : IsAgnosticPACLearnerFor sqLoss 5 epsQ delH {true} {Measure.dirac true} :=
  sqClosed.antitone_family (Set.subset_univ _)

/-- The empty-class benchmark is `sInf ∅ = 0`. -/
example : approximationError sqLoss (Measure.dirac true) ∅ = 0 := by
  simp [approximationError, Real.sInf_empty]

/-- The zero loss is learner-correct by a constant learner at sample size zero. -/
example : IsAgnosticPACLearnerFor zeroLoss 0 epsQ delH {()} Set.univ := by
  refine ⟨fun _ => (), fun D inst _ => ?_⟩
  have hεpos : (0 : ℝ) < (epsQ.val : ℝ) := by exact_mod_cast epsQ.property.1
  have hsub : {S : Fin 0 → Bool |
      approximationError zeroLoss D {()} + (epsQ.val : ℝ) < risk zeroLoss D ()} ⊆ ∅ := by
    intro S hS
    simp only [Set.mem_ofPred_eq, zeroLoss_approx, zeroLoss_risk, zero_add] at hS
    exact absurd hS (not_lt.mpr hεpos.le)
  have htail : (Measure.pi fun _ : Fin 0 => D) ∅ ≤ (delH.val : ℝ≥0∞) := by simp
  refine ⟨fun h _ => zeroLoss_int D h, fun h _ => zeroLoss_nn D h,
    fun S => zeroLoss_int D _, fun S => zeroLoss_nn D _, ?_⟩
  exact le_trans (measure_mono hsub) htail

/-- A negative loss cannot satisfy the predicate: the definition requires
almost-everywhere nonnegative losses, but `0 ≤ -1` holds nowhere. -/
example : ¬ IsAgnosticPACLearnerFor negLoss 3 epsQ delH {()} {Measure.dirac true} := by
  intro hcon
  obtain ⟨A, hA⟩ := hcon
  have hmem : Measure.dirac true ∈ ({Measure.dirac true} : Set (Measure Bool)) := by simp
  have hfull := @hA (Measure.dirac true) _ hmem
  have hae := hfull.2.1 () (by simp)
  simp only [negLoss] at hae
  have hex := hae.exists
  obtain ⟨z, hz⟩ := hex
  norm_num at hz

/-- Log sample bound for the singleton bridge instance. -/
private theorem bridge_log :
    Real.log (2 * ((1 : ℕ) : ℝ) / (4 / 5)) / (2 * (2 / 5) ^ 2) ≤ ((5 : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) < 2 * (2 / 5) ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  have harg : (0 : ℝ) < 2 * ((1 : ℕ) : ℝ) / (4 / 5) := by norm_num
  have hlog := Real.log_le_sub_one_of_pos harg
  norm_num at hlog ⊢
  linarith

private theorem bridge_eps : ((briE.val : ℝ≥0) : ℝ) = 2 * (2 / 5) := by norm_num [briE]

private theorem bridge_del : ((briE.val : ℝ≥0) : ℝ) = 4 / 5 := by norm_num [briE]

/-- The 0-1 bridge on `Bool` inputs and labels: the finite-class ERM supplier
gives a PAC learner for the always-true singleton, and the bridge turns it
into a general-loss learner at `zeroOneLoss`. Disagreement measurability is by
discreteness. -/
example : IsAgnosticPACLearnerFor zeroOneLoss 5 briE briE
    (Set.range (fun _ : Fin 1 => fun _ : Bool => true)) Set.univ := by
  have hPAC : IsPACLearnerFor 5 briE briE
      (Set.range (fun _ : Fin 1 => fun _ : Bool => true)) Set.univ :=
    agnosticFiniteClass_isPACLearner (M := 1) (m := 5) (by norm_num) (fun _ _ => true)
      (fun j p =>
        if (fun _ : Fin 1 => fun _ : Bool => true) j p.1 ≠ p.2 then (1 : ℝ) else 0)
      (fun j p => rfl) (fun _ => MeasurableSet.of_discrete)
      (ε := 2 / 5) (by norm_num) (by norm_num) (δ := 4 / 5) (by norm_num) (by norm_num)
      bridge_log briE briE bridge_eps bridge_del
  have hne : (Set.range (fun _ : Fin 1 => fun _ : Bool => true)).Nonempty :=
    ⟨fun _ => true, 0, rfl⟩
  exact hPAC.toIsAgnosticPACLearnerFor_zeroOneLoss hne (fun _ => MeasurableSet.of_discrete)

#print axioms IsAgnosticPACLearnerFor.mono_δ
#print axioms IsAgnosticPACLearnerFor.mono_ε
#print axioms IsAgnosticPACLearnerFor.antitone_family
#print axioms IsPACLearnerFor.toIsAgnosticPACLearnerFor_zeroOneLoss

end CSLibExtTest.MachineLearning.PACLearning.AgnosticPAC
