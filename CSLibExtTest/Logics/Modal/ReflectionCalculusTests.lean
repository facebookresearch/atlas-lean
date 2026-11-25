/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ReflectionCalculus

@[expose] public section

/-! # Tests for the Reflection Calculus -/

namespace Cslib.Modal.RC.ReflectionCalculusTests

inductive Atom where
  | p
  | q
  deriving DecidableEq

open Formula

/-- The source's example `ω(p ∧ q) ⊢ ωp ∧ ωq`, here for the modality `2`. -/
example : Derives (.dia 2 (.and (.atom Atom.p) (.atom Atom.q)))
    (.and (.dia 2 (.atom Atom.p)) (.dia 2 (.atom Atom.q))) :=
  .and_intro (.dia_mono 2 (.and_left _ _)) (.dia_mono 2 (.and_right _ _))

/-- Positive replacement: from `p ∧ q ⊢ p` infer `⟨1⟩(p ∧ q) ∧ q ⊢ ⟨1⟩p ∧ q`, with
`C = ⟨1⟩p ∧ q`. -/
example : Derives (.and (.dia 1 (.and (.atom Atom.p) (.atom Atom.q))) (.atom Atom.q))
    (.and (.dia 1 (.atom Atom.p)) (.atom Atom.q)) := by
  simpa [Formula.subst] using
    (Derives.and_left (.atom Atom.p) (.atom Atom.q)).subst_left_right Atom.p
      (.and (.dia 1 (.atom Atom.p)) (.atom Atom.q))

/-- The worm `1` proves `⟨0⟩⟨0⟩⟨0⟩⊤`. -/
example : WormLt (Atom := Atom) [0, 0] [1] := WormLt.replicate_zero_one 2

/-- A nondegenerate RC-frame: the chain `0 < 1 < 2` with `R₀` the strict order and `R₁` empty. -/
def chainR : ℕ → Fin 3 → Fin 3 → Prop := fun n x y ↦ n = 0 ∧ x < y

theorem chainR_isFrame : IsFrame chainR :=
  ⟨fun ⟨hm, hxy⟩ ⟨hn, hyz⟩ ↦ ⟨by simp [hm, hn], Fin.lt_trans hxy hyz⟩,
    fun hnm ⟨hm, _⟩ _ ↦ absurd hm (Nat.ne_of_gt (Nat.zero_lt_of_lt hnm)),
    fun hnm ⟨hm, _⟩ ↦ absurd hm (Nat.ne_of_gt (Nat.zero_lt_of_lt hnm))⟩

/-- On the chain, `⟨0⟩⟨0⟩⊤` holds at the bottom, so soundness applies non-vacuously. -/
example : Satisfies chainR (fun _ (_ : Atom) ↦ True) 0 (.dia 0 (.dia 0 .top)) :=
  ⟨1, ⟨rfl, by decide⟩, 2, ⟨rfl, by decide⟩, trivial⟩

/-- Monotonicity fails in the converse direction: `⟨0⟩p ⊬ ⟨1⟩p`, by soundness on the chain. -/
example : ¬Derives (.dia 0 (.atom Atom.p)) (.dia 1 (.atom Atom.p)) := fun h ↦ by
  obtain ⟨_, ⟨h1, _⟩, _⟩ := Derives.sound chainR_isFrame (fun _ _ ↦ True) h 0
    ⟨1, ⟨rfl, by decide⟩, trivial⟩
  exact absurd h1 (by decide)

/-- The worm `0` is not below itself. -/
example : ¬WormLt (Atom := Atom) [0] [0] := not_wormLt_zero_zero

end Cslib.Modal.RC.ReflectionCalculusTests
