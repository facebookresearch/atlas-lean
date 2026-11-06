/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact source trace-node bindings of finite representative matrix prefixes. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepresentatives

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The literal representative prefix has exactly the original source trace-node label. -/
def y322Orthogonal3TCRepresentativeCacheCheckAt (index : ℕ) : Prop :=
  if h : index < 3159 then
    let i : Fin 3159 := ⟨index, h⟩
    y322Orthogonal3TCCacheNode (y322Orthogonal3TCRepresentativeCache i) =
      y322TCIndexRepresentativeNode i
  else True

/-- Literal source trace-node comparisons are decidable on their finite exact indices. -/
instance y322Orthogonal3TCRepresentativeCacheCheckAtDecidable (index : ℕ) :
    Decidable (y322Orthogonal3TCRepresentativeCacheCheckAt index) := by
  unfold y322Orthogonal3TCRepresentativeCacheCheckAt
  split <;> infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
