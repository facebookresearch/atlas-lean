/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge
public import DomainsTest.Biology.PopulationGenetics.Coalescent.EwensFreezeMergeBridge

/-!
# The terminal freeze-merge block-size law

Compose the terminal partition law's equality with CRP and the native
Ewens sampling formula for allele block sizes.
-/

@[expose] public section

namespace Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge

/-- For `θ > 0`, the terminal freeze-merge law has the native Ewens block-size distribution. -/
theorem terminalLaw_map_blockSizes (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (p : n.Partition) :
    ((terminalLaw θ hθ n).map
      MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.blockSizes) p =
      ENNReal.ofReal (MathlibExt.Biology.PopulationGenetics.Ewens.ewensProb θ p) := by
  exact map_blockSizes_of_eq_crp θ hθ n (terminalLaw θ hθ n)
    (terminalLaw_eq_crp θ hθ n) p

end Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge
