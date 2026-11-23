/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.AbstractInterpretation
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Set.Lattice.Image

/-! # Abstract interpretation regression probes -/

open Cslib.AbstractInterpretation

/-- Concrete transformer that adds `0` and closes under `+ 2`. -/
private def evenStep (s : Set ℕ) : Set ℕ := insert 0 ((· + 2) '' s)

private theorem evenStep_mono : Monotone evenStep :=
  fun _ _ h => Set.insert_subset_insert (Set.image_mono h)

/-- Abstract parity transformer on `Set Bool`, where `true` means odd. -/
private def parityStep (t : Set Bool) : Set Bool := insert false t

private theorem parityStep_mono : Monotone parityStep :=
  fun _ _ h => Set.insert_subset_insert h

-- Parity abstraction through the non-identity Galois connection
-- `Set.image Nat.bodd ⊣ Set.preimage Nat.bodd` between `Set ℕ` and
-- `Set Bool`: every element of the concrete least fixpoint is even.
example :
    ∀ n ∈ OrderHom.lfp ⟨evenStep, evenStep_mono⟩, Nat.bodd n = false := by
  have hsound :
      ∀ t, Nat.bodd '' evenStep (Nat.bodd ⁻¹' t) ⊆ parityStep t := by
    rintro t _ ⟨n, hn, rfl⟩
    rcases hn with rfl | ⟨m, hm, rfl⟩
    · exact Or.inl Nat.bodd_zero
    · exact Or.inr (by simpa [Nat.bodd_add] using hm)
  have h := abs_lfp_sound (Set.image Nat.bodd) (Set.preimage Nat.bodd)
    Set.image_preimage evenStep evenStep_mono parityStep parityStep_mono
    hsound
  have hfalse : OrderHom.lfp ⟨parityStep, parityStep_mono⟩ ⊆ {false} :=
    OrderHom.lfp_le _ (by simp [parityStep])
  intro n hn
  exact hfalse (h ⟨n, hn, rfl⟩)

-- The concrete least fixpoint is nonempty, so the parity bound above is
-- not vacuous.
example : 0 ∈ OrderHom.lfp ⟨evenStep, evenStep_mono⟩ := by
  rw [← OrderHom.map_lfp]
  exact Set.mem_insert 0 _

-- The one-point domain composes with `abs_lfp_sound` for every monotone
-- concrete transformer.
example (F : Set ℕ → Set ℕ) (hF : Monotone F) :
    (fun _ => (PUnit.unit : PUnit.{1})) (OrderHom.lfp ⟨F, hF⟩) ≤
      OrderHom.lfp ⟨id, monotone_id⟩ :=
  abs_lfp_sound (A := PUnit.{1}) _ _ top_domain_gc F hF id monotone_id
    (top_domain_sound F)
