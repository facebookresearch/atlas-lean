/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Ergodicity

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Ergodicity`

For the Bernoulli product measure on `ConfigSpace ℤ` with `p = 1/2`, under the translation action of
`Multiplicative ℤ` on `ℤ`:
* the hypothesis of `bernoulli_ergodic` (each `{g | g • a = b}` is finite) holds: it is a
  singleton;
* `bernoulli_ergodic` applies to the translation-invariant event "every coordinate is closed",
  which therefore has probability `0` or `1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Ergodicity

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.ConfigSpace
open scoped NNReal

/-- Translations of `ℤ` moving `a` to `b`: at most one. -/
theorem translate_finite (a b : ℤ) : {g : Multiplicative ℤ | g • a = b}.Finite := by
  refine Set.Subsingleton.finite fun g hg g' hg' => ?_
  simp only [Set.mem_ofPred_eq] at hg hg'
  have h : Multiplicative.toAdd g + a = Multiplicative.toAdd g' + a := hg.trans hg'.symm
  exact Multiplicative.toAdd.injective (add_right_cancel h)

/-- The event "every coordinate is closed". -/
def allClosedEvent : Set (ConfigSpace ℤ) := {ω | ∀ e, ω e = false}

/-- The event "every coordinate is closed" is translation invariant. -/
theorem allClosedEvent_invariant (g : Multiplicative ℤ) :
    (shift g : ConfigSpace ℤ → ConfigSpace ℤ) ⁻¹' allClosedEvent = allClosedEvent := by
  ext ω
  simp only [allClosedEvent, Set.mem_preimage, Set.mem_ofPred_eq, shift_apply]
  exact ⟨fun h e => by simpa using h (g • e), fun h e => h _⟩

-- Zero–one law for the Bernoulli measure on the invariant event "all closed".
example : bernoulliProductMeasure (E := ℤ) (1 / 2 : ℝ≥0) (by norm_num) allClosedEvent = 0 ∨
    bernoulliProductMeasure (E := ℤ) (1 / 2 : ℝ≥0) (by norm_num) allClosedEvent = 1 := by
  have hm : MeasurableSet allClosedEvent := by
    simp only [allClosedEvent, Set.ofPred_forall]
    exact MeasurableSet.iInter fun e =>
      measurableSet_eq_fun (measurable_pi_apply e) measurable_const
  have h := bernoulli_ergodic (G := Multiplicative ℤ) translate_finite (1 / 2) (by norm_num) hm
    allClosedEvent_invariant
  rwa [measure_univ] at h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Ergodicity
