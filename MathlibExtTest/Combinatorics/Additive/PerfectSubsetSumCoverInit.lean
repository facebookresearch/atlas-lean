/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCoverInit

namespace MetaMathlibExt

open PerfectSubsetSumCover

/-- Removing the sole entry of a perfect cover of `ZMod 2` leaves an empty prefix. -/
example :
    let s : Fin 1 → ZMod 2 := fun _ => 1
    coverCount (s ∘ Fin.castSucc) 0 = 1 ∧ coverCount (s ∘ Fin.castSucc) 1 = 0 := by
  intro s
  have hs : IsPerfectMCover (2 ^ 0) s := by decide +revert
  have hzero : coverCount (s ∘ Fin.castSucc) 0 = 1 := by decide +revert
  refine ⟨hzero, ?_⟩
  have h := coverCount_init_add_last hs 0
  rw [hzero] at h
  exact h

/-- Two equal entries at different indices contribute separately to the prefix count. -/
example :
    let s : Fin 4 → ZMod 4 := ![0, 0, 2, 1]
    coverCount (s ∘ Fin.castSucc) 1 = 0 ∧ coverCount (s ∘ Fin.castSucc) 2 = 4 := by
  intro s
  have hs : IsPerfectMCover (2 ^ 2) s := by decide +revert
  have hone : coverCount (s ∘ Fin.castSucc) 1 = 0 := by decide +revert
  refine ⟨hone, ?_⟩
  have h := coverCount_init_add_last hs 1
  rw [hone] at h
  exact h

-- Negative shifts use the same parity rule. The last entry has order four, not two.
example :
    let s : Fin 4 → ZMod 4 := ![0, 0, 2, 1]
    coverCount (s ∘ Fin.castSucc) 2 = 4 ∧ coverCount (s ∘ Fin.castSucc) 3 = 0 := by
  intro s
  have hs : IsPerfectMCover (2 ^ 2) s := by decide +revert
  have hzero : coverCount (s ∘ Fin.castSucc) 0 = 4 := by decide +revert
  have h := coverCount_init_add_zsmul_last hs 0 (-1)
  rw [hzero] at h
  exact h

end MetaMathlibExt
