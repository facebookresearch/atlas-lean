/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitDataTables

/-! Ordinary-kernel bindings of finite parent indices and original generator basis images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 10000 in
-- The literal tables have135 nested finite entries.
/-- The two initial vertices are the original literal candidates0 and14. -/
theorem generatedAxisE8FrameSystemOrbit_root (k : Fin 2) :
    generatedAxisE8FrameSystemOrbitIndex k 0 = (if k = 0 then 0 else 14) := by
  revert k
  decide +kernel

set_option maxRecDepth 10000 in
-- The parent table has270 entries.
/-- Every noninitial parent edge decreases the actual finite tree index. -/
theorem generatedAxisE8FrameSystemOrbit_parent_lt (k : Fin 2) (i : Fin 135) (hi : i ≠ 0) :
    (generatedAxisE8FrameSystemOrbitParent k i).val < i.val := by
  revert k i hi
  decide +kernel

set_option maxRecDepth 10000 in
-- Compare the270 literal candidate indices.
/-- The two trees contain270 distinct genuine candidate indices. -/
theorem generatedAxisE8FrameSystemOrbitIndex_injective :
    Function.Injective (fun p : Fin 2 × Fin 135 =>
      generatedAxisE8FrameSystemOrbitIndex p.1 p.2) := by
  decide +kernel

set_option maxHeartbeats 1000000000 in
-- Bind270 edges times four basis vectors to the previously checked original root matrices.
set_option maxRecDepth 10000 in
-- The finite candidate and parent tables have deeply nested literal entries.
/-- Every parent edge is the original generator's action on all four actual basis columns. -/
theorem generatedAxisE8FrameSystemOrbit_edge_certificate :
    ∀ k : Fin 2, ∀ i : Fin 135, ∀ j : Fin 4,
      generatedFifthSectionGeneratorBinary (generatedAxisE8FrameSystemOrbitGenerator k i) *ᵥ
        generatedAxisE8FrameSystemCandidateBasis
          (generatedAxisE8FrameSystemOrbitIndex k (generatedAxisE8FrameSystemOrbitParent k i)) j =
      generatedAxisE8FrameSystemCandidateMap (generatedAxisE8FrameSystemOrbitIndex k i)
        (generatedAxisE8FrameSystemOrbitCoefficient k i j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
