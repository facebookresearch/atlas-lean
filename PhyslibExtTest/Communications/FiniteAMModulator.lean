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
      * ((Pi.single (1 : ZMod 4) (1 : ℂ) : ZMod 4 → ℂ) 1 + (Pi.single (-1 : ZMod 4) (1 : ℂ) : ZMod 4 → ℂ) 1) :=
  dft_amSignal_const_message 4 1 (1 / 2) 2 1 1

/-- The same fixture, independently simplified: the impulses
evaluate to `1 + 0`, so the DFT value is exactly `4`. -/
example : 𝓕 (fun j => ((amSignal 4 1 (1 / 2) (fun _ => 2) 1 j : ℝ) : ℂ)) 1 = 4 := by
  rw [dft_amSignal_const_message, Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1 : ZMod 4) ≠ -1 by decide)]
  norm_num

/-- The `N = 4` tone sidebands are not disjoint, through the public
lemma. -/
example : ¬ Disjoint (positiveShiftSupport 4 (carrierCos 4 1) 1)
    (negativeShiftSupport 4 (carrierCos 4 1) 1) :=
  not_disjoint_shifted_supports_tone_four

end PhyslibExtTest.Communications.FiniteAMModulator
