/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationStructure.GlobalAncestryBridge

/-!
# Tests for the global-ancestry frequency view
-/

namespace Cslib.Bioinformatics.PopulationStructure.AdmixtureEM

variable {I J K : Type*} [Fintype K]

example (θ : Params I J K) (i : I) (j : J) :
    ancestryFreq θ (Sum.inl i) j = ∑ k, θ.Q i k * ancestryFreq θ (Sum.inr k) j :=
  ancestryFreq_inl_eq_sum θ i j

/-- Raw proportions include pure-source rows. The first row mixes its sources in a 1:3 ratio;
    the second selects the first source without mixing. -/
example :
    let Q := ![![(1 : ℝ) / 4, 3 / 4], ![1, 0]]
    let F := fun k : Fin 2 => fun _ : Unit => ![(1 : ℝ) / 5, 3 / 5] k
    ancestryFreqOf Q F (.inl 0) () = 1 / 2 ∧
      ancestryFreqOf Q F (.inl 1) () = ancestryFreqOf Q F (.inr 0) () := by
  norm_num [ancestryFreqOf, Fin.sum_univ_two]

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
