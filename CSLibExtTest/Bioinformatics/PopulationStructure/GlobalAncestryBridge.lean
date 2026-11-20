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

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
