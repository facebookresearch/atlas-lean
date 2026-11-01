/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinMasks

/-! Complete bounded physical coordinate indexing for the original integer spin certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A complete sixteen-by-256 indexing of all original physical spin output coordinates. -/
def generatedAxisGlobalOddSpinOutputBlock (b : Fin 16) (n : Fin 256) : Fin 4096 :=
  ⟨256 * b.val + n.val, by have hb := b.isLt; have hn := n.isLt; omega⟩

/-- Every original physical output coordinate belongs to exactly its displayed complete block. -/
theorem generatedAxisGlobalOddSpinOutputBlock_roundtrip (k : Fin 4096) :
    generatedAxisGlobalOddSpinOutputBlock ⟨k.val / 256, by have hk := k.isLt; omega⟩
      ⟨k.val % 256, Nat.mod_lt _ (by decide)⟩ = k := by
  apply Fin.ext
  dsimp only [generatedAxisGlobalOddSpinOutputBlock]
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
