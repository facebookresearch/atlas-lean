/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.AgnosticFiniteClass

@[expose] public section

namespace CSLibExtTest.MachineLearning.PACLearning.AgnosticFiniteClass

open MeasureTheory ProbabilityTheory
open Cslib.MachineLearning.PACLearning
open scoped ENNReal NNReal

/-- Use case: singleton class. The single hypothesis is PAC with the Hoeffding rate,
with no realizability assumption. -/
example {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm_log : Real.log (2 * ((1 : ℕ) : ℝ) / δ) / (2 * ε ^ 2) ≤ (m : ℝ))
    (ε' δ' : Set.Ioo (0 : ℝ≥0) 1)
    (hε' : (ε'.val : ℝ) = 2 * ε) (hδ' : (δ'.val : ℝ) = δ) :
    IsPACLearnerFor m ε' δ' (Set.range (fun _ : Fin 1 => fun _ : Bool => true)) Set.univ := by
  have herr : ∀ _j : Fin 1,
      MeasurableSet {p : Bool × Bool | (fun _ : Fin 1 => fun _ : Bool => true) _j p.1 ≠ p.2} := by
    intro j
    have hEq : {p : Bool × Bool | (fun _ : Fin 1 => fun _ : Bool => true) j p.1 ≠ p.2}
        = Prod.snd ⁻¹' {(false : Bool)} := by
      ext p
      simp
    rw [hEq]
    exact measurable_snd (measurableSet_singleton false)
  exact agnosticFiniteClass_isPACLearner hm (fun _ _ => true)
    (fun j p => if (fun _ : Fin 1 => fun _ : Bool => true) j p.1 ≠ p.2 then (1 : ℝ) else 0)
    (fun j p => rfl) herr hε0 hε1 hδ0 hδ1 hm_log ε' δ' hε' hδ'

/-- Duplicate hypotheses: the bound is unchanged when two indices name the same classifier. -/
example {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm_log : Real.log (2 * ((2 : ℕ) : ℝ) / δ) / (2 * ε ^ 2) ≤ (m : ℝ))
    (ε' δ' : Set.Ioo (0 : ℝ≥0) 1)
    (hε' : (ε'.val : ℝ) = 2 * ε) (hδ' : (δ'.val : ℝ) = δ) :
    IsPACLearnerFor m ε' δ' (Set.range (fun _ : Fin 2 => fun _ : Bool => true)) Set.univ := by
  have herr : ∀ _j : Fin 2,
      MeasurableSet {p : Bool × Bool | (fun _ : Fin 2 => fun _ : Bool => true) _j p.1 ≠ p.2} := by
    intro j
    have hEq : {p : Bool × Bool | (fun _ : Fin 2 => fun _ : Bool => true) j p.1 ≠ p.2}
        = Prod.snd ⁻¹' {(false : Bool)} := by
      ext p
      simp
    rw [hEq]
    exact measurable_snd (measurableSet_singleton false)
  exact agnosticFiniteClass_isPACLearner hm (fun _ _ => true)
    (fun j p => if (fun _ : Fin 2 => fun _ : Bool => true) j p.1 ≠ p.2 then (1 : ℝ) else 0)
    (fun j p => rfl) herr hε0 hε1 hδ0 hδ1 hm_log ε' δ' hε' hδ'

/-- Nonempty class witness: the `[NeZero M]` class constraint supplies the `Fin M`
inhabitant used by `ermIdx`. There is no `NeZero 0` instance, so an empty index type
cannot instantiate the pinned theorems above. -/
example {M : ℕ} [NeZero M] : Nonempty (Fin M) :=
  Fin.pos_iff_nonempty.mp (NeZero.pos M)

/-- Empty class rejected: `NeZero 0` is contradictory, so `M := 0` can never supply
the class index the theorems require. -/
example (hne : NeZero (0 : ℕ)) : False :=
  lt_irrefl 0 (NeZero.pos 0)

/-- Fixed-class guard: the class is a closed term bound before the data law, so it
cannot mention the sample or the law; this closed constant-true application closes
by exact application of the pinned risk theorem. -/
example {m : ℕ} (hm : 0 < m)
    (F : Fin 1 → (Bool × Bool) → ℝ)
    (hF : ∀ (j : Fin 1) (p : Bool × Bool), F j p = if (true : Bool) ≠ p.2 then (1 : ℝ) else (0 : ℝ))
    (herr : ∀ _j : Fin 1, MeasurableSet {p : Bool × Bool | (true : Bool) ≠ p.2})
    (D : Measure (Bool × Bool)) [IsProbabilityMeasure D]
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin m => D).real
      {S : Fin m → Bool × Bool |
        (⨅ j, ∫ z, F j z ∂D) + 2 * ε < ∫ z, F (ermIdx F S) z ∂D} ≤
      2 * ((1 : ℕ) : ℝ) * Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  exact agnosticFiniteClass_excessRisk hm (fun _ _ => true) F hF herr D hε

/-- Empty class rejected at the target: `M := 0` cannot supply the class index.
Probed: elaboration fails with `failed to synthesize instance of type class `NeZero 0``. -/
example (D : Measure (Bool × Bool)) [IsProbabilityMeasure D] : True := by
  fail_if_success
    have hbad := agnosticFiniteClass_excessRisk (M := 0) (m := 5) _ _ _ _ _ D _
  trivial

/-- Sample-dependent class rejected: hypotheses must answer points, not whole samples.
The sample-eating variant takes an extra `Fin m → Bool × Bool` argument, so it does not
fit the target's `h : Fin M → (α → Bool)`; probed: elaboration fails with a function-type
mismatch (`Bool → Bool` against `Bool`). -/
example (D : Measure (Bool × Bool)) [IsProbabilityMeasure D] : True := by
  fail_if_success
    have hbad := agnosticFiniteClass_excessRisk (M := 1) (m := 5) _
      (fun _ (_ : Fin 5 → Bool × Bool) => (fun _ : Bool => true)) _ _ _ D _
  trivial

/-- Empty class rejected at the PAC target: `M := 0` cannot supply the class index.
Probed: elaboration fails with `failed to synthesize instance of type class `NeZero 0``. -/
example : True := by
  fail_if_success
    have hbad := agnosticFiniteClass_isPACLearner (M := 0) (m := 5) _ _ _ _ _ _ _ _ _ _ _ _ _
  trivial

/-- Sample-dependent class rejected at the PAC target: hypotheses must answer points, not
whole samples. The sample-eating variant takes an extra `Fin m → Bool × Bool` argument,
so it does not fit the target's `h`; probed: elaboration fails with a function-type
mismatch (`Bool → Bool` against `Bool`). -/
example : True := by
  fail_if_success
    have hbad := agnosticFiniteClass_isPACLearner (M := 1) (m := 5) _ (fun _ (_ : Fin 5 → Bool × Bool) => (fun _ : Bool => true)) _ _ _ _ _ _ _ _ _ _
  trivial

/-- Genuinely noisy law: the fair mixture over one feature gives both labels positive mass.
The always-false singleton class has error `1 / 2` and optimal error `1 / 2`: no
zero-error member exists. -/
example : error ((1/2 : ℝ≥0∞) • Measure.dirac ((false : Bool), true) +
    (1/2 : ℝ≥0∞) • Measure.dirac ((false : Bool), false)) (fun _ : Bool => false)
    = 1 / 2 := by
  unfold error
  have hmem : ((false : Bool), true) ∈ {p : Bool × Bool | (fun _ : Bool => false) p.1 ≠ p.2} := by
    simp
  have hnmem : ((false : Bool), false) ∉ {p : Bool × Bool | (fun _ : Bool => false) p.1 ≠ p.2} := by
    simp
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply,
    Set.indicator_of_mem hmem, Set.indicator_of_notMem hnmem]
  simp

example : optimalError ((1/2 : ℝ≥0∞) • Measure.dirac ((false : Bool), true) +
    (1/2 : ℝ≥0∞) • Measure.dirac ((false : Bool), false)) {fun _ : Bool => false}
    = 1 / 2 := by
  unfold optimalError
  rw [iInf_singleton]
  unfold error
  have hmem : ((false : Bool), true) ∈ {p : Bool × Bool | (fun _ : Bool => false) p.1 ≠ p.2} := by
    simp
  have hnmem : ((false : Bool), false) ∉ {p : Bool × Bool | (fun _ : Bool => false) p.1 ≠ p.2} := by
    simp
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply,
    Set.indicator_of_mem hmem, Set.indicator_of_notMem hnmem]
  simp

end CSLibExtTest.MachineLearning.PACLearning.AgnosticFiniteClass
