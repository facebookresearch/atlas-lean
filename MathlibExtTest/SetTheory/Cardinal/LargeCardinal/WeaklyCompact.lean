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

public import MathlibExt.SetTheory.Cardinal.LargeCardinal.WeaklyCompact
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

open Set Cardinal

namespace MathlibExtTest.SetTheory.Cardinal.LargeCardinal.WeaklyCompact

open MetaMathlibExt

-- Logic 33: Weakly compact cardinal

/-- Sanity check: the homogeneous set the definition produces is not vacuously
homogeneous — it really contains 2-element subsets, so `k` is pinned down. -/

theorem isWeaklyCompact_homogeneous_nonvacuous (κ : Cardinal) (h : IsWeaklyCompact κ)
    (F : Finset κ.out → Bool) :
    ∃ (H : Set κ.out) (k : Bool), #H = κ ∧ IsHomogeneousFor 2 F H k ∧
      ∃ s : Finset κ.out, s.card = 2 ∧ (s : Set κ.out) ⊆ H := by
  obtain ⟨hκ, hpart⟩ := h
  obtain ⟨H, hH, k, hhom⟩ := hpart κ.out (mk_out κ) F
  have hinf : H.Infinite := by
    rw [← Set.infinite_coe_iff, Cardinal.infinite_iff, hH]
    exact hκ.le
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq 2
  exact ⟨H, k, hH, hhom, s, hcard, hs⟩

end MathlibExtTest.SetTheory.Cardinal.LargeCardinal.WeaklyCompact

end
