/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.ChineseRestaurant

/-!
# Transport to the Ewens sampling formula

Transport the native block-size law of the Chinese restaurant process
(Ewens 1972; Hoppe 1984) along an equality of partition laws.
-/

@[expose] public section

namespace Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge

/-- For `θ > 0`, a partition law equal to CRP has the native Ewens block-size distribution. -/
theorem map_blockSizes_of_eq_crp (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (law : PMF (Finpartition (Finset.univ : Finset (Fin n))))
    (heq : law = MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crp θ hθ n)
    (p : n.Partition) :
    (law.map MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.blockSizes) p =
      ENNReal.ofReal (MathlibExt.Biology.PopulationGenetics.Ewens.ewensProb θ p) := by
  rw [heq]
  exact MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crp_map_blockSizes hθ p

end Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge
