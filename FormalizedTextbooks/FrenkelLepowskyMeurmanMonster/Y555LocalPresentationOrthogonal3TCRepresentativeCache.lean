/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Every actual source representative has its exact finite prefix node. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheBlock24

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every literal representative-node binding block passes its exact finite source check. -/
theorem y322Orthogonal3TCRepresentativeCache_block (block : Fin 25) (i : Fin 128) :
    y322Orthogonal3TCRepresentativeCacheCheckAt (block.val * 128 + i.val) := by
  fin_cases block
  · exact y322Orthogonal3TCRepresentativeCacheBlock00 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock01 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock02 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock03 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock04 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock05 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock06 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock07 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock08 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock09 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock10 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock11 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock12 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock13 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock14 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock15 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock16 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock17 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock18 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock19 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock20 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock21 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock22 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock23 i
  · exact y322Orthogonal3TCRepresentativeCacheBlock24 i

/-- Every finite prefix cache entry has exactly the actual original representative trace node. -/
theorem y322Orthogonal3TCRepresentativeCache_node (i : Fin 3159) :
    y322Orthogonal3TCCacheNode (y322Orthogonal3TCRepresentativeCache i) =
      y322TCIndexRepresentativeNode i := by
  let block : Fin 25 := ⟨i.val / 128, by omega⟩
  let offset : Fin 128 := ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩
  have h := y322Orthogonal3TCRepresentativeCache_block block offset
  have he : block.val * 128 + offset.val = i.val := by
    dsimp [block, offset]
    omega
  rw [he] at h
  simpa only [y322Orthogonal3TCRepresentativeCacheCheckAt, dite_eq_left i.isLt] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
