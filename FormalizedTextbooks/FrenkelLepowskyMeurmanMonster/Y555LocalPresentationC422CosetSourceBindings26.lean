/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact bindings of literal source words to independently proved original-source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetSourceData26

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- At most 128 source pairs are compared literally, including all original signs and path parents.
/-- Every literal source pair freely matches its independently proved source family. -/
theorem y422CosetSourceBindings26 (i : Fin 128) :
    y322EquationsSameReduction (y422CosetSourceEquation26 i)
      (y422CosetSourceEquation (y422CosetSourceKind26 i)) := by
  revert i
  unfold y322EquationsSameReduction
  decide +kernel

/-- Every literal source in this interval is valid in the actual original C422/S/Q group. -/
theorem y422CosetSourceEquation26_valid (i : Fin 128) :
    (y422CosetSourceEquation26 i).Valid y422CosetSymbol := by
  exact y322WordEquation_transport y422CosetSymbol _ _
    (y422CosetSourceEquation_valid (y422CosetSourceKind26 i))
    (y422CosetSourceBindings26 i).1 (y422CosetSourceBindings26 i).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
