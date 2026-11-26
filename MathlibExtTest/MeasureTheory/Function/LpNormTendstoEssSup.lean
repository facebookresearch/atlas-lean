/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LpNormTendstoEssSup
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum

open Filter MeasureTheory
open MathlibExt.Analysis.FunctionalAnalysis.LpNormTendstoEssSupWanted
open scoped ENNReal NNReal Topology

local instance : MeasurableSpace Unit := ⊤

private noncomputable def ν : Measure Unit := Measure.dirac () + Measure.dirac ()

-- Total mass 2 ensures the finite-exponent norms carry a nonconstant mass factor.
example : Tendsto (fun p : ℝ≥0 => eLpNorm (fun _ : Unit => (-2 : ℝ)) p ν) atTop (𝓝 2) := by
  have hmass : ν Set.univ = 2 := by
    rw [ν, add_apply, Measure.dirac_apply_of_mem (Set.mem_univ ())]
    norm_num
  have hfin : ν Set.univ < ∞ := by rw [hmass]; simp
  let : IsFiniteMeasure ν := ⟨hfin⟩
  have hν : ν ≠ 0 := by
    intro hz
    simp [hz] at hmass
  have htop : eLpNorm (fun _ : Unit => (-2 : ℝ)) ∞ ν = 2 := by
    rw [eLpNorm_exponent_top aestronglyMeasurable_const, eLpNormEssSup_const _ hν, ← ofReal_norm]
    norm_num
  simpa only [htop] using tendsto_eLpNorm_atTop_eLpNorm_top_of_isFiniteMeasure hfin
    (memLp_const (-2 : ℝ))

-- The zero measure has no positive-mass sets, and all of the norms vanish.
example : Tendsto (fun p : ℝ≥0 => eLpNorm (fun _ : Unit => (3 : ℝ)) p (0 : Measure Unit))
    atTop (𝓝 0) := by
  have hfin : (0 : Measure Unit) Set.univ < ∞ := by simp
  simpa only [eLpNorm_measure_zero] using
    tendsto_eLpNorm_atTop_eLpNorm_top_of_isFiniteMeasure hfin (memLp_const (3 : ℝ))
