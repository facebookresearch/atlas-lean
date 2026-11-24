/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AbsolutelyDensePartition
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.ZMod

/-! # Tests for absolutely dense partitions -/

namespace MathlibExtTest.AbsolutelyDensePartition

open MathlibExt.GroupTheory.AbsolutelyDensePartitionKourovka13Problem47Wanted Set

private abbrev G := Multiplicative (ℚ × ZMod 2)

-- The two rational lines have a nontrivial involution and a non-discrete Hausdorff topology.
example : ∃ A B : Set G, A ∪ B = univ ∧ Disjoint A B ∧ Dense A ∧ Dense B := by
  have hfin : {g : G | g ≠ 1 ∧ g ^ 2 = 1}.Finite := by
    apply (finite_range (fun k : ZMod 2 ↦ Multiplicative.ofAdd ((0 : ℚ), k))).subset
    intro g hg
    have h := congrArg (fun z : G ↦ z.toAdd.1) hg.2
    change (2 • g.toAdd).1 = 0 at h
    simp only [two_nsmul, Prod.fst_add] at h
    refine ⟨g.toAdd.2, congrArg Multiplicative.ofAdd (Prod.ext ?_ rfl)⟩
    change 0 = g.toAdd.1
    linarith
  obtain ⟨A, B, hcover, hdisj, hd⟩ :=
    countableAbsolutelyDensePartition_holds G (inferInstanceAs (Countable (ℚ × ZMod 2))) hfin
  let τ : GroupTopology G := ⟨inferInstance, inferInstance⟩
  have hnd : τ.toTopologicalSpace ≠ ⊥ := by
    intro h
    have hopen : IsOpen ({((0 : ℚ), (0 : ZMod 2))} : Set (ℚ × ZMod 2)) := by
      change τ.IsOpen _
      exact h ▸ trivial
    apply not_isOpen_singleton (0 : ℚ)
    have hpre : (fun x : ℚ ↦ (x, (0 : ZMod 2))) ⁻¹' {(0, 0)} = {(0 : ℚ)} := by
      ext x
      simp
    rw [← hpre]
    exact hopen.preimage (continuous_id.prodMk continuous_const)
  exact ⟨A, B, hcover, hdisj, hd τ (inferInstanceAs (T2Space (ℚ × ZMod 2))) hnd⟩

end MathlibExtTest.AbsolutelyDensePartition
