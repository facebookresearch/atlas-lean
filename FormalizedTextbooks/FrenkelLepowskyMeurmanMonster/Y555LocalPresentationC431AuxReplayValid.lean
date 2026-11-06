/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original C431 group equalities from the fully checked contextual equation trace. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayChecked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplaySources

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Every checked chronological equation holds at the actual original C431 word assignments. -/
theorem y431AuxReplayProgram_valid (i : Fin 3684) :
    (y431AuxReplayProgram i).1.Valid y431AuxReplaySymbol :=
  y322ContextEquationProgram_valid y431AuxReplaySymbol y431AuxReplaySourceEquation
    y431AuxReplaySourceEquation_valid y431AuxReplayProgram y431AuxReplayProgram_checked i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
