/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddMonomial

/-! Original coordinate multiplicities are preserved by actual Golay permutation isometries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual Golay permutations preserve every original coordinate-magnitude multiplicity. -/
theorem leechNormSixPair_permutation_multiplicity (p : golayAutomorphismSubgroup)
    (u : leechIntegral) :
    leechNormEightMultiplicity (leechIntegralAction (golayPermutationIsometry p) u).val =
      leechNormEightMultiplicity u.val := by
  funext k
  have h := Equiv.sum_comp p.val.symm
    (fun i : Fin 24 => if (u.val i).natAbs = k.val then (1 : ℕ) else 0)
  simpa [leechNormEightMultiplicity, leechIntegralAction_golayPermutation,
    golayIntegerPermute] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
