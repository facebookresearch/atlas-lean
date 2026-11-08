/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import MathlibExt.SetTheory.Cardinal.Characteristics
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

open Cardinal Ordinal Set Order

namespace MathlibExtTest.SetTheory.Cardinal.Characteristics

open MetaMathlibExt

-- Logic 361: Unbounded family

/-- **Degenerate case**: `∅` is bounded. -/

theorem not_isUnboundedFamily_empty : ¬ IsUnboundedFamily (∅ : Set (ℕ → ℕ)) := by
  intro h
  exact h ⟨fun _ => 0, fun f hf => absurd hf (by simp)⟩

/-- Unboundedness is **upward closed**, so all the content of `𝔟` is in minimising the size. -/

theorem _root_.MetaMathlibExt.IsUnboundedFamily.mono {F G : Set (ℕ → ℕ)} (hsub : F ⊆ G)
    (h : IsUnboundedFamily F) : IsUnboundedFamily G := by
  intro ⟨g, hg⟩
  exact h ⟨g, fun f hf => hg f (hsub hf)⟩

-- Logic 362: Bounding number

/-- Any single unbounded family bounds `𝔟` from above. -/

theorem boundingNumber_le {F : Set (ℕ → ℕ)} (h : IsUnboundedFamily F) :
    boundingNumber ≤ #F :=
  csInf_le' ⟨F, h, rfl⟩

end MathlibExtTest.SetTheory.Cardinal.Characteristics

end
