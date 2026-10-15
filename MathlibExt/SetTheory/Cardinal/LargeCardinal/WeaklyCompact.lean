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

public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.InfinitaryCombinatorics.PartitionCalculus
public import MathlibExt.SetTheory.Ultrafilter.Ramsey
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 33
-- Proposed path (advisory metadata only, not a review instruction).

open Set Cardinal

-- Logic 33: Weakly compact cardinal
def IsWeaklyCompact (κ : Cardinal) : Prop :=
  ℵ₀ < κ ∧
  ∀ (I : Type) (_ : #I = κ) (F : Finset I → Bool),
    ∃ (H : Set I) (_ : #H = κ) (k : Bool), IsHomogeneousFor 2 F H k

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

end
