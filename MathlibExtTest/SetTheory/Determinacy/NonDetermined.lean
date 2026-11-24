/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.SetTheory.Determinacy.NonDetermined

@[expose] public section

open Set Cardinal MathlibExt.SetTheory.Determinacy

namespace MathlibExtTest.SetTheory.Determinacy.NonDetermined

/-- A non-determined game on three moves. -/
example : ∃ S : Set (ℕ → Fin 3), ¬ Determined S := exists_not_determined

/-- The axiom of determinacy fails. -/
example : ¬ ∀ S : Set (ℕ → ℕ), Determined S := not_forall_determined

/-- The two-element hypothesis cannot be dropped: with one move every set is determined. -/
example : ∀ S : Set (ℕ → Unit), Determined S := determined_of_subsingleton

/-- The diagonalisation in a small case: a countable family of copies of `ℕ` inside `ℕ × ℕ`
(the rows) is split by a single set. -/
example : ∃ B : Set (ℕ × ℕ), ∀ i : ℕ, (B ∩ {p | p.1 = i}).Nonempty ∧
    (Bᶜ ∩ {p | p.1 = i}).Nonempty := by
  refine exists_meets_and_compl_meets ℵ₀ le_rfl _ (by simp) fun i => ?_
  have : Function.Injective (fun n : ℕ => (⟨(i, n), rfl⟩ : {p : ℕ × ℕ | p.1 = i})) := by
    intro a b h
    simpa using congrArg (fun q => q.1.2) h
  have h := mk_le_of_injective this
  rwa [mk_nat] at h

end MathlibExtTest.SetTheory.Determinacy.NonDetermined
