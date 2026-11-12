/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Donsker
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Moments.Variance

@[expose] public section

open scoped BigOperators

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.DonskerWanted

namespace MathlibExtTest.Probability.Donsker

-- At the right endpoint, polygonal interpolation is the normalized full partial sum.
example {Ω : Type*} (n : ℕ) (hn : n ≠ 0) (X : ℕ → Ω → ℝ) (ω : Ω) :
    donskerProcess n X ω ⟨1, zero_le_one, le_rfl⟩ =
      (∑ i ∈ Finset.range n, X i ω) / Real.sqrt (n : ℝ) := by
  simpa using
    donskerProcess_apply_eq (n := n) (X := X) (ω := ω)
      (t := ⟨1, zero_le_one, le_rfl⟩) hn

-- At the left endpoint every polygonal path is pinned at `0`; Donsker's tightness step feeds this
-- to `isTightMeasureSet_of_modulus`. For `n = 0` the process is `0` by definition.
example {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    donskerProcess n X ω ⟨0, le_rfl, zero_le_one⟩ = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [donskerProcess]
  · rw [donskerProcess_apply_eq n X ω _ hn]
    simp

-- Equal finite-dimensional laws of two Dirac measures determine the paths themselves.
example (f g : C(Set.Icc (0 : ℝ) 1, ℝ))
    (h : ∀ I : Finset (Set.Icc (0 : ℝ) 1),
      (Measure.dirac f).map (fun u => I.restrict (fun t => u t)) =
        (Measure.dirac g).map (fun u => I.restrict (fun t => u t))) :
    f = g := by
  apply MeasureTheory.injective_dirac
  exact continuousMap_measure_ext_of_finset_eval (Measure.dirac f) (Measure.dirac g) h

-- Etemadi and Chebyshev bound the running maximum by the partial-sum variances.
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (n : ℕ) (a : ℝ) (ha : 0 < a)
    (hLp : ∀ k, MemLp (fun ω => ∑ i ∈ Finset.range k, X i ω) 2 P)
    (hmean : ∀ k, ∫ ω, ∑ i ∈ Finset.range k, X i ω ∂P = 0) :
    P {ω | ∃ k ∈ Finset.range (n + 1),
        3 * a ≤ |∑ i ∈ Finset.range k, X i ω|} ≤
      3 * (⨆ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (Var[fun ω => ∑ i ∈ Finset.range k, X i ω; P] / a ^ 2)) := by
  calc
    P {ω | ∃ k ∈ Finset.range (n + 1),
        3 * a ≤ |∑ i ∈ Finset.range k, X i ω|} ≤
        3 * (⨆ k ∈ Finset.range (n + 1),
          P {ω | a ≤ |∑ i ∈ Finset.range k, X i ω|}) :=
      etemadi_maximal_inequality X hX hIndep n a
    _ ≤ 3 * (⨆ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (Var[fun ω => ∑ i ∈ Finset.range k, X i ω; P] / a ^ 2)) := by
      gcongr with k hk
      simpa [hmean k] using meas_ge_le_variance_div_sq (hLp k) ha

end MathlibExtTest.Probability.Donsker
