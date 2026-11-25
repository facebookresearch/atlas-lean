/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomialHarmonicExpansion

open MathlibExt.NumberTheory.DelannoyTriangleWanted

example (m : ℕ) : harmonicMod m 0 = 0 ∧ harmonic2Mod m 0 = 0 := by
  simp [harmonicMod, harmonic2Mod]

-- At the upper endpoint for p = 3, the second term contributes 1/2 or 1/4 modulo 27.
example : harmonicMod 27 2 = 15 ∧ harmonic2Mod 27 2 = 8 := by decide +kernel

-- For s = -1 and k = 3, the quadratic correction contributes to the residue of (-6 choose 3).
example : (∏ i ∈ Finset.Icc 1 (3 : ℕ), (((-1 : ℤ) * (5 : ℤ) - (i : ℤ)) : ZMod (5 ^ 3))) *
    (Nat.factorial 3 : ZMod (5 ^ 3))⁻¹ = 69 := by
  exact (choose_mul_sub_one_mod 5 (by decide) (by decide) (-1) 3 (by decide)).trans
    (by decide +kernel)
