/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Resolution

@[expose] public section

/-- Boundary check: a one-step resolution proof derives the empty
clause from the two unit clauses, so the formula is
unsatisfiable. -/
example (σ : ℕ → Bool) :
    ¬ (∀ c ∈ ([{(0, true)}, {(0, false)}] : List (Finset Lit)),
      clauseSat σ c) := by
  intro h
  have hproof : ResProof [{(0, true)}, {(0, false)}] ∅ :=
    ResProof.resolve 0 ∅ ∅
      (ResProof.input ⟨0, by decide⟩)
      (ResProof.input ⟨1, by decide⟩) (by decide) (by decide)
  exact resolution_sound hproof σ h

/-- A model of a single unit clause satisfies it. -/
example : clauseSat (fun _ => true) {(0, true)} :=
  ⟨(0, true), by decide, rfl⟩
