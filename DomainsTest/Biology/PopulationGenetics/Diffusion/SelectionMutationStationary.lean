/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.PopulationGenetics.Diffusion.SelectionMutationStationary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Monotone.Basic

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SelectionMutationStationary

example : 0 < MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationPartition
    0 1 1 :=
  MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationPartition_pos 0
    zero_lt_one zero_lt_one

example : 0 < MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationPartition
    2 1 1 :=
  MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationPartition_pos 2
    zero_lt_one zero_lt_one

example : HasDerivAt
    (fun α => MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationMean α 1 1)
    (2 * MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationVariance 0 1 1)
    0 :=
  MathlibExt.Biology.PopulationGenetics.Diffusion.hasDerivAt_selectionMutationMean 0
    zero_lt_one zero_lt_one

example : MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationMean (-1) 1 1 <
    MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationMean 1 1 1 :=
  MathlibExt.Biology.PopulationGenetics.Diffusion.strictMono_selectionMutationMean
    zero_lt_one zero_lt_one (show (-1 : ℝ) < 1 by norm_num)

example : 0 < MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationVariance
    0 1 1 :=
  MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationVariance_pos 0
    zero_lt_one zero_lt_one

example : 0 < MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationPartition
    0 2 3 :=
  MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationPartition_pos 0
    (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 3 by norm_num)

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SelectionMutationStationary

#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.intervalIntegrable_selectionMutationSpeedDensity
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationPartition_pos
#print axioms
  MathlibExt.Biology.PopulationGenetics.Diffusion.hasDerivAt_log_selectionMutationPartition
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.hasDerivAt_selectionMutationMean
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.selectionMutationVariance_pos
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.strictMono_selectionMutationMean
