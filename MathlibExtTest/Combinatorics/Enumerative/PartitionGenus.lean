/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PartitionGenus

namespace MathlibExtTest.Combinatorics.Enumerative.PartitionGenus

open Equiv Finset MetaMathlibExt

-- Two singleton blocks give one nontrivial face and genus zero.
example : (finRotate 2).cycleType.card = 1 ∧ setPartitionGenus (1 : Perm (Fin 2)) = 0 := by
  have h := twoBlock_oneFace_and_genus 1 (isIncreasingCyclePerm_one 2)
    (by simp [Perm.parts_partition]) 0
  exact ⟨by simpa using h.1, setPartitionGenus_one 2⟩

-- The blocks {0, 2} and {1, 3, 4} alternate except at the consecutive pair 3, 4.
private def mixed : Perm (Fin 5) := swap 0 2 * (swap 3 1 * swap 3 4)

example : setPartitionGenus mixed = 1 := by
  have h2 : mixed.partition.parts.card = 2 := by
    let a : Perm (Fin 5) := swap 0 2
    let b : Perm (Fin 5) := swap 3 1 * swap 3 4
    have hd : a.Disjoint b := by
      rw [Perm.disjoint_iff_eq_or_eq]
      decide
    have ha : a.IsCycle := Perm.isCycle_swap (by decide)
    have hb : b.IsThreeCycle := Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide)
      (by decide)
    have hs : #mixed.support = 5 := by decide
    rw [Perm.parts_partition, hs, show mixed = a * b from rfl, hd.cycleType_mul,
      ha.cycleType, hb.cycleType]
    decide
  have h := (twoBlock_oneFace_and_genus mixed (by decide) h2 1).2
  have hfixed : #{x | mixed.SameCycle 1 x ∧ (finRotate 5 * mixed⁻¹) x = x} = 1 := by decide
  have hsize : #{x | mixed.SameCycle 1 x} = 3 := by decide
  omega

end MathlibExtTest.Combinatorics.Enumerative.PartitionGenus
