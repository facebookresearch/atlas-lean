/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.KimuraFixationSelection
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.NormNum

/-!
# Boundary tests for Kimura's fixation formula with selection

Examples at boundary selection and frequency values for allele-label symmetry, the
deleterious comparison, strict selection monotonicity, and the neutral derivative.
-/

open Set MathlibExt.Biology.PopulationGenetics.Diffusion

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.KimuraFixationSelection

example : kimuraFixation (0:ℝ) (1/3) = 1 - kimuraFixation 0 (2/3) := by
  have h := kimuraFixation_neg (0:ℝ) (1/3)
  have h0 : (-0:ℝ) = 0 := by norm_num
  have h13 : (1:ℝ) - 1/3 = 2/3 := by norm_num
  rw [h0, h13] at h
  exact h

example : kimuraFixation (1:ℝ) (1/4) = 1 - kimuraFixation (-1) (3/4) := by
  have h := kimuraFixation_neg (1:ℝ) (1/4)
  have h14 : (1:ℝ) - 1/4 = 3/4 := by norm_num
  rw [h14] at h
  exact h

example : kimuraFixation (-1:ℝ) (1/2) < 1/2 :=
  kimuraFixation_lt (by norm_num) (Set.mem_Ioo.mpr (by norm_num))

example : kimuraFixation (-1:ℝ) (1/2) < kimuraFixation 0 (1/2) := by
  have hmono :=
    strictMono_kimuraFixation_in_sigma (x := (1/2:ℝ)) (Set.mem_Ioo.mpr (by norm_num))
  exact hmono (show (-1:ℝ) < 0 by norm_num)

example : kimuraFixation (0:ℝ) (1/2) < kimuraFixation 1 (1/2) := by
  have hmono :=
    strictMono_kimuraFixation_in_sigma (x := (1/2:ℝ)) (Set.mem_Ioo.mpr (by norm_num))
  exact hmono (show (0:ℝ) < 1 by norm_num)

example : HasDerivAt (fun σ => kimuraFixation σ (0:ℝ)) 0 0 := by
  have h :=
    hasDerivAt_kimuraFixation_sigma_zero (x := (0:ℝ)) (Set.mem_Icc.mpr (by norm_num))
  have hval : (0:ℝ) * (1 - 0) = 0 := by norm_num
  rw [hval] at h
  exact h

example : HasDerivAt (fun σ => kimuraFixation σ (1/2:ℝ)) (1/4) 0 := by
  have h :=
    hasDerivAt_kimuraFixation_sigma_zero (x := (1/2:ℝ)) (Set.mem_Icc.mpr (by norm_num))
  have hval : (1/2:ℝ) * (1 - 1/2) = 1/4 := by norm_num
  rw [hval] at h
  exact h

example : HasDerivAt (fun σ => kimuraFixation σ (1:ℝ)) 0 0 := by
  have h :=
    hasDerivAt_kimuraFixation_sigma_zero (x := (1:ℝ)) (Set.mem_Icc.mpr (by norm_num))
  have hval : (1:ℝ) * (1 - 1) = 0 := by norm_num
  rw [hval] at h
  exact h

#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.kimuraFixation_neg
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.kimuraFixation_lt
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.strictMono_kimuraFixation_in_sigma
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.hasDerivAt_kimuraFixation_sigma_zero

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.KimuraFixationSelection
