/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.FiniteAMModulator
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Communications.FiniteAMModulator ZMod

namespace PhyslibExtTest.Communications.FiniteAMModulator

/-- Constant message at `N = 4`: the DFT is the two carrier
impulses at `l = ±k` with weight `(A + μ c) * 4 / 2`. At `k = l = 1`
the value is `(A + μ c) * 2`. -/
example : 𝓕 (fun j => ((amSignal 4 1 (1 / 2) (fun _ => 2) 1 j : ℝ) : ℂ)) 1
    = ((1 + (1 / 2) * 2 : ℝ) : ℂ) * (4 : ℂ) / 2
      * (binImpulse 4 1 1 + binImpulse 4 (-1) 1) :=
  dft_amSignal_const_message 4 1 (1 / 2) 2 1 1

/-- The `N = 4` tone sidebands are not disjoint, through the public
lemma. -/
example : ¬ Disjoint (upperSidebandSupport 4 (carrierCos 4 1) 1)
    (lowerSidebandSupport 4 (carrierCos 4 1) 1) :=
  not_disjoint_sidebands_tone_four

end PhyslibExtTest.Communications.FiniteAMModulator
