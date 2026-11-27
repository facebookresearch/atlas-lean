/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ProvabilityLogic.Basic

/-!
# Frame correspondence for Löb's axiom

`frame_valid_axiomLob_iff` characterizes the frames validating Löb's axiom as the transitive,
conversely well-founded frames.
-/

public section

namespace Cslib.Modal

universe u

variable {Atom : Type u}

/-- **Frame correspondence for Löb's axiom.** On a nonempty set of worlds `W`, with at least one
atom, Löb's axiom `□(□φ → φ) → □φ` is valid for every formula `φ` and every valuation on the frame
`(W, R)` iff `R` is transitive and conversely well-founded, i.e. has no infinite chain
`w₀ R w₁ R w₂ R ⋯` (Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*,
current edition, §3.1). The direction from right to left is the proved
`KripkeModel.valid_axiomLob`. -/
theorem frame_valid_axiomLob_iff {W : Type u} [Nonempty W] [Nonempty Atom]
    (R : W → W → Prop) :
    (∀ (V : W → Atom → Prop) (phi : Formula Atom),
        (KripkeModel.mk inferInstance R V).Valid (Formula.axiomLob phi)) ↔
      (∀ {a b c}, R a b → R b c → R a c) ∧ WellFounded (flip R) := by
  constructor
  · intro hLob
    obtain ⟨p⟩ := ‹Nonempty Atom›
    constructor
    · intro a b c hab hbc
      -- Make the atom true exactly at the successors of a, then apply axiom 4 at a.
      let M : KripkeModel W Atom := ⟨inferInstance, R, fun v _ ↦ R a v⟩
      have hFour := (Derivable.axiomFour_GL (.atom p)).valid (M := M) (by
        rintro _ ⟨phi, rfl⟩
        exact hLob M.valuation phi)
      exact hFour a (fun _ h ↦ h) b hab c hbc
    · -- An atom interpreted as accessibility satisfies □p → p at every world.
      refine ⟨fun w ↦ Acc.intro w ?_⟩
      exact hLob (fun v _ ↦ Acc (flip R) v) (.atom p) w (fun v _ ih ↦ Acc.intro v ih)
  · rintro ⟨htrans, hwf⟩ V phi
    exact (KripkeModel.mk inferInstance R V).valid_axiomLob htrans hwf phi

end Cslib.Modal
