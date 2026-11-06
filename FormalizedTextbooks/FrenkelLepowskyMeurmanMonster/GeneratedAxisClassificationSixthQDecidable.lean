/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

/-! Finite certificates compare genuine Q elements by both original extension coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact decidable equality for genuine Q, retaining the entire base and central coordinate. -/
def generatedSixthQDecidableEq : DecidableEq Q := fun q r =>
  match decEq q.base r.base with
  | isFalse hb => isFalse (fun h => hb (congrArg (fun z : Q => z.base) h))
  | isTrue hb =>
    match decEq q.coeff r.coeff with
    | isFalse hc => isFalse (fun h => hc (congrArg (fun z : Q => z.coeff) h))
    | isTrue hc => isTrue (by
      apply NormalizedCocycleExtension.Extension.ext
      · exact hb
      · exact hc)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
