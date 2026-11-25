/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCover

namespace MetaMathlibExt

open PerfectSubsetSumCover

/-- Repeating the first generator gives a double cover with different projection counts. -/
example :
    let s : Fin 4 → ZMod 2 × ZMod 4 := ![(1, 0), (0, 1), (0, 2), (1, 0)]
    IsPerfectMCover 8 (fun i => (s i).1) ∧ IsPerfectMCover 4 (fun i => (s i).2) := by
  intro s
  have hs : IsPerfectMCover 2 s := by decide +revert
  exact isPerfectMCover_fst_snd (m := 1) (n := 2) (by decide) (by decide) hs

/-- A nonzero adjoiner can repeat the value of an existing index. -/
example : IsPerfectMCover 2 (Fin.cons (1 : ZMod 4) (![1, 2] : Fin 2 → ZMod 4)) := by
  have hs : IsPerfectMCover 1 (![1, 2] : Fin 2 → ZMod 4) := by decide
  exact isPerfectMCover_cons hs 1

/-- A zero adjoiner doubles the multiplicity of a cover with repeated entries. -/
example : IsPerfectMCover 4 (Fin.cons (0 : ZMod 2) (![1, 1] : Fin 2 → ZMod 2)) := by
  have hs : IsPerfectMCover 2 (![1, 1] : Fin 2 → ZMod 2) := by decide
  exact isPerfectMCover_cons hs 0

/-- The empty family covers zero exactly once, through the empty subset. -/
example : coverCount (Fin.elim0 : Fin 0 → ZMod 2) 0 = 1 ∧
    coverCount (Fin.elim0 : Fin 0 → ZMod 2) 1 = 0 := by decide

/-- The trivial group has one perfect cover, the empty set. -/
example : count (ZMod 1) = 1 := by
  rw [count_eq_card_filter]
  decide

/-- A nonzero even integer cannot be an odd combination of the singleton generator. -/
example : (2 : ℤ) ∉ oddCombinations {1} := by
  rintro ⟨c, hc, heq⟩
  have h := hc 1 (by simp)
  simp at heq
  rcases h with hz | ⟨k, hk⟩ <;> omega

/-- The two coordinate generators of `ZMod 2 × ZMod 2` satisfy the odd-combination condition. -/
example : IsPerfectMCover 1 (![(1, 0), (0, 1)] : Fin 2 → ZMod 2 × ZMod 2) := by
  let s : Fin 2 → ZMod 2 × ZMod 2 := ![(1, 0), (0, 1)]
  have hs (i : Fin 2) : s i ∉ oddCombinations ((Finset.Iio i).image s) := by
    have hIio0 : Finset.Iio (0 : Fin 2) = ∅ := by decide
    have hIio1 : Finset.Iio (1 : Fin 2) = {0} := by decide
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [hIio0, Finset.image_empty, oddCombinations_empty]
      decide
    · rw [hIio1, Finset.image_singleton]
      rintro ⟨c, -, h⟩
      have hcoord := congrArg Prod.snd h
      simp [s] at hcoord
  exact (coverCount_le_one_of_not_mem_oddCombinations hs).2 (by
    rw [Nat.card_eq_fintype_card]
    decide)

-- An odd multiple may be negative, and an unused generator keeps coefficient zero.
example : (-3 : ℤ) ∈ oddCombinations {1, 2} := by
  have h : (1 : ℤ) ∈ oddCombinations {1, 2} := mem_oddCombinations_of_mem (by simp)
  simpa using zsmul_mem_oddCombinations {1, 2} h (-2)

-- Closure includes the zero combination on the empty set.
example (j : ℤ) : (2 * j + 1) • (0 : ℤ) ∈ oddCombinations ∅ :=
  zsmul_mem_oddCombinations ∅ (zero_mem_oddCombinations ∅) j

end MetaMathlibExt
