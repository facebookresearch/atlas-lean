/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact literal target binding for the original f1 right-coset certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetProgram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The final actual index of the chronological original-source terminal certificate. -/
def y522CosetTerminalTarget : Fin 10296 := ⟨10295, by decide⟩

set_option maxRecDepth 100000 in
-- Both literal sides are checked without changing the decoded program or its finite bounds.
/-- The final claim is exactly original f1 versus the identity, with the original sign. -/
theorem y522CosetTerminalTarget_words :
    (y522CosetProgram y522CosetTerminalTarget).1.left =
      [(y522CosetGeneratorLetter 9, true)] ∧
    (y522CosetProgram y522CosetTerminalTarget).1.right = [] := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
