/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact bindings of literal source words to independently proved original-source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceData14

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- At most 128 source pairs are compared literally, including all original signs and path parents.
/-- Every literal source pair freely matches its independently proved source family. -/
theorem y522CosetSourceBindings14 (i : Fin 71) :
    y322EquationsSameReduction (y522CosetSourceEquation14 i)
      (y522CosetSourceEquation (y522CosetSourceKind14 i)) := by
  revert i
  unfold y322EquationsSameReduction
  decide +kernel

/-- Every literal source in this interval is valid in the actual original Y555 group. -/
theorem y522CosetSourceEquation14_valid (i : Fin 71) :
    (y522CosetSourceEquation14 i).Valid y522CosetSymbol := by
  exact y322WordEquation_transport y522CosetSymbol _ _
    (y522CosetSourceEquation_valid (y522CosetSourceKind14 i))
    (y522CosetSourceBindings14 i).1 (y522CosetSourceBindings14 i).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
