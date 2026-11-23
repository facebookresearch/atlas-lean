/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.Dataflow
import Mathlib.Data.Fintype.Order

@[expose] public section

/-- Boundary check: Kildall iteration on `Bool` stabilizes for a
monotone transfer function. -/
example : ∃ k, (fun b : Bool => b || true)^[k] (⊥ : Bool)
    = (fun b : Bool => b || true) ((fun b : Bool => b || true)^[k] (⊥ : Bool)) :=
  kildall_stabilizes (fun b : Bool => b || true) (fun a b h => by
    cases a <;> cases b <;> simp_all)

/-- On a finite lattice the two theorems compose: iteration from `⊥`
reaches the least fixpoint of every monotone transfer function. -/
example (F : Bool → Bool) (hF : Monotone F) :
    ∃ k, F^[k] (⊥ : Bool) = OrderHom.lfp ⟨F, hF⟩ := by
  obtain ⟨k, hk⟩ := kildall_stabilizes F hF
  exact ⟨k, kildall_eq_lfp F hF k hk⟩

/-- A monotone transfer function on the infinite complete lattice
`Set ℕ`: add `0` and the successors of current elements that lie
below `3`. -/
private def countStep (s : Set ℕ) : Set ℕ :=
  insert 0 ((· + 1) '' s ∩ Set.Iio 3)

private theorem countStep_mono : Monotone countStep :=
  fun _ _ h => Set.insert_subset_insert
    (Set.inter_subset_inter_left _ (Set.image_mono h))

/-- Infinite-lattice check: the iterate from `⊥` on `Set ℕ` stabilizes
after three steps, and `kildall_eq_lfp` identifies it with the least
fixpoint. -/
example : OrderHom.lfp ⟨countStep, countStep_mono⟩ = Set.Iio 3 := by
  have h3 : countStep^[3] ⊥ = Set.Iio 3 := by
    ext n
    simp [countStep, Function.iterate_succ_apply']
    omega
  have h4 : countStep (Set.Iio 3) = Set.Iio 3 := by
    ext n
    simp only [countStep, Set.mem_insert_iff, Set.mem_inter_iff,
      Set.mem_image, Set.mem_Iio]
    constructor
    · rintro (rfl | ⟨-, h⟩)
      · omega
      · exact h
    · intro h
      rcases n with _ | m
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨m, by omega, rfl⟩, h⟩
  rw [← kildall_eq_lfp countStep countStep_mono 3 (by rw [h3, h4]), h3]
