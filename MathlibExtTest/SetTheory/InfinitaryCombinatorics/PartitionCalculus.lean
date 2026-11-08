/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.InfinitaryCombinatorics.PartitionCalculus
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MathlibExtTest.SetTheory.InfinitaryCombinatorics.PartitionCalculus

open MetaMathlibExt

-- Logic 31: Homogeneous set

/-- Check A (negative, discriminating): a colouring that genuinely splits the
1-element subsets is homogeneous for no colour on `univ`. -/

theorem not_isHomogeneousFor_mem_zero :
    ¬ ∃ k : Bool, IsHomogeneousFor 1 (fun s : Finset ℕ => decide (0 ∈ s)) Set.univ k := by
  rintro ⟨k, hk⟩
  have h0 := hk {0} (by simp) (by simp)
  have h1 := hk {1} (by simp) (by simp)
  rw [← h0] at h1
  simp at h1

end MathlibExtTest.SetTheory.InfinitaryCombinatorics.PartitionCalculus

end
