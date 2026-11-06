/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-group validity of every source used by the C431 contextual proof. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplaySourceBindings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Every declared replay source holds in the actual original C431/R group. -/
theorem y431AuxReplaySourceEquation_valid (i : Fin 856) :
    (y431AuxReplaySourceEquation i).Valid y431AuxReplaySymbol := by
  have hb := y431AuxReplaySource_bound i
  exact y322WordEquation_transport y431AuxReplaySymbol (y431AuxReplaySourceFamily i)
    (y431AuxReplaySourceEquation i) (y431AuxReplaySourceFamily_valid i) hb.1 hb.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
