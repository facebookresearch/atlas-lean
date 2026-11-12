/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TimeSeries.RandomWalkVariance
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

/-!
# Tests for random-walk variance

Concrete non-vacuity: coordinate evaluations on the infinite product of
`gaussianReal 0 3` with itself. Independence, square-integrability, and the
common variance are all derived, and the single-innovation variance `3` is
computed, not assumed. The random-walk variance formula is applied at
horizons `0`, `1`, and `4` (giving `0`, `3`, and `12`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.TimeSeries.RandomWalkVariance

namespace MathlibExtTest.Probability.TimeSeries.RandomWalkVariance

/-!
# Concrete test for Atlas ST08.T03: Gaussian innovations with variance 3

Applies the frozen theorems to a concrete innovation family, proving the
hypotheses are jointly satisfiable: coordinate evaluations on the infinite
product of `gaussianReal 0 3` with itself. Independence, square-integrability,
and the common variance are all derived, and the single-innovation variance `3`
is computed, not assumed.
-/


/-- Concrete innovation law: Gaussian with mean `0` and variance `3`. -/
noncomputable def testLaw : Measure ℝ := gaussianReal 0 3

instance : IsProbabilityMeasure testLaw := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 3))

/-- Concrete sample space: infinite product of the innovation law with itself. -/
noncomputable def testMu : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => testLaw)

/-- Concrete innovations: coordinate evaluations. -/
noncomputable def testEps : ℕ → (ℕ → ℝ) → ℝ := fun i ω => ω i

/-- The coordinate evaluations are square-integrable. -/
theorem testEps_memLp (i : ℕ) : MemLp (testEps i) 2 testMu := by
  have h1 : MemLp id 2 (gaussianReal 0 3) := memLp_id_gaussianReal' 2 (by simp)
  have hmp : MeasurePreserving (Function.eval i) testMu (gaussianReal 0 3) :=
    measurePreserving_eval_infinitePi (fun _ => testLaw) i
  exact h1.comp_measurePreserving hmp

/-- The coordinate evaluations are independent. -/
theorem testEps_indep : iIndepFun testEps testMu :=
  iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)

/-- All coordinates share the same variance. -/
theorem testEps_variance (i : ℕ) :
    variance (testEps i) testMu = variance (testEps 0) testMu := by
  have hmp : ∀ j, MeasurePreserving (Function.eval j) testMu (gaussianReal 0 3) :=
    fun j => measurePreserving_eval_infinitePi (fun _ => testLaw) j
  have hi := (hmp i).variance_fun_comp (f := id) measurable_id.aemeasurable
  have h0 := (hmp 0).variance_fun_comp (f := id) measurable_id.aemeasurable
  calc variance (testEps i) testMu
      = variance id (gaussianReal 0 3) := hi
    _ = variance (testEps 0) testMu := h0.symm

/-- The computed single-innovation variance is `3`. -/
theorem testEps_variance_zero : variance (testEps 0) testMu = 3 := by
  have hmp : MeasurePreserving (Function.eval 0) testMu (gaussianReal 0 3) :=
    measurePreserving_eval_infinitePi (fun _ => testLaw) 0
  have h := hmp.variance_fun_comp (f := id) measurable_id.aemeasurable
  rw [variance_id_gaussianReal] at h
  have hcoe : ((3 : NNReal) : ℝ) = 3 := by simp
  rw [hcoe] at h
  exact h

/-- Horizon `0` gives `0`. -/
theorem test_randomWalk_h0 :
    variance (fun ω => ∑ k ∈ Finset.range 0, testEps k ω) testMu = 0 := by
  rw [randomWalk_variance testEps testEps_memLp testEps_indep testEps_variance 0]
  simp

/-- Horizon `1` gives the computed single-innovation variance `3`. -/
theorem test_randomWalk_h1 :
    variance (fun ω => ∑ k ∈ Finset.range 1, testEps k ω) testMu = 3 := by
  rw [randomWalk_variance testEps testEps_memLp testEps_indep testEps_variance 1,
    testEps_variance_zero]
  norm_num

/-- Horizon `4` with computed variance `3` gives `12`. -/
theorem test_randomWalk_h4 :
    variance (fun ω => ∑ k ∈ Finset.range 4, testEps k ω) testMu = 12 :=
  randomWalk_variance_four testEps testEps_memLp testEps_indep testEps_variance
    testEps_variance_zero

end MathlibExtTest.Probability.TimeSeries.RandomWalkVariance
