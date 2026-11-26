/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.RegularTripartitionCongruencesRamanujanPsiPrimeDissection
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.Partition.RegularTripartitionCongruencesRamanujanPsiPrimeDissection

open MetaMathlibExt

-- The `p = 3` non-congruence at `m = 0`.
example : ¬ (0 ^ 2 + 0) / 2 ≡ (3 ^ 2 - 1) / 8 [MOD 3] := by
  have hq : ‖(0 : ℂ)‖ < 1 := by simp
  have h := (ramanujanPsi_prime_dissection 3 (by decide) (by decide) 0 hq).2
    0 (by decide)
  exact h

-- The `p = 3` dissection at `q = 1 / 2`, with the one-term sum unfolded.
example : ramanujanThetaRaw (1 / 2) ((1 / 2) ^ 3)
    = ramanujanThetaRaw ((1 / 2) ^ 6) ((1 / 2) ^ 3)
      + (1 / 2) * ramanujanThetaRaw ((1 / 2) ^ 9) ((1 / 2) ^ 27) := by
  have hq : ‖((1 / 2 : ℂ))‖ < 1 := by norm_num [Complex.norm_def]
  have h := (ramanujanPsi_prime_dissection 3 (by decide) (by decide) (1 / 2) hq).1
  simpa using h

-- The `p = 5` non-congruence at `m = 1`.
example : ¬ (1 ^ 2 + 1) / 2 ≡ (5 ^ 2 - 1) / 8 [MOD 5] := by
  have hq : ‖(0 : ℂ)‖ < 1 := by simp
  have h := (ramanujanPsi_prime_dissection 5 (by decide) (by decide) 0 hq).2
    1 (by decide)
  exact h

end MathlibExtTest.Combinatorics.Enumerative.Partition.RegularTripartitionCongruencesRamanujanPsiPrimeDissection
