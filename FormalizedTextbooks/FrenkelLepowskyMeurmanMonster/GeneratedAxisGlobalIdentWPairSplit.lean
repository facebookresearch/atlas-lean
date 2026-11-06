/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # The pair part of the pairing in two integer sums (r8f)

`pairSumZI fwd LM L W` is a matrix sum over the pair terms of `W` (integer numerators of the
transported integer block `LM`) plus a lookup sum of the pair terms of `L` at the pair terms of `W`.
For dense pair blocks the two integer sums are evaluated separately (`pairSumZI_eq`). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The matrix sum of the pair part: integer numerators at the pair terms of `W`. -/
def pairMZ (fwd : Bool) (LM : MatZ) (W : IdentVec) : ℤ :=
  (W.sh.pairs.map (fun q => q.2 * (if fwd then (if q.1 < 276 then 1 else -1) else 1) *
    LM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2)).sum

/-- The lookup sum of the pair part: pair terms of `L` at the pair terms of `W`. -/
def pairLZ (fwd : Bool) (L W : IdentVec) : ℤ :=
  (W.sh.pairs.map (fun q => q.2 *
    (if fwd then idxSum L.sh.pairs (q.1 % 276) - idxSum L.sh.pairs (276 + q.1 % 276)
     else if q.1 < 276 then idxSum L.sh.pairs (q.1 % 276) + idxSum L.sh.pairs (276 + q.1 % 276)
     else -(idxSum L.sh.pairs (q.1 % 276) + idxSum L.sh.pairs (276 + q.1 % 276))))).sum

/-- The pair part from its two integer sums. -/
theorem pairSumZI_eq (fwd : Bool) (LM : MatZ) (L W : IdentVec) :
    pairSumZI fwd LM L W =
      (pairMZ fwd LM W : ℚ) / (LM.den * 4 ^ LM.k) + L.sden * (pairLZ fwd L W : ℚ) / 2 := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
