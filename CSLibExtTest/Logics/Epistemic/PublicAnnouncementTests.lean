/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Epistemic.PublicAnnouncement

namespace Cslib.Epistemic.PublicAnnouncementTests

open Cslib.Epistemic

/-- A false announcement is vacuously true, even of falsity. -/
example : Sat muddy (.announce (.atom ()) .bot) false := by
  intro h
  exact Bool.false_ne_true h

/-- Two worlds with universal accessibility; atom `0` holds only at
`true`, atom `1` nowhere. -/
def guardModel : Model Bool (Fin 2) (Fin 1) where
  rel := fun _ _ _ => True
  valuation := fun w a => a = 0 ∧ w = true
  nonempty_world := ⟨true⟩

/-- At the world where the announcement fails, announcing before knowledge
is vacuously true. -/
example : Sat guardModel (.announce (.atom 0) (.know 0 (.atom 1))) false := by
  intro h
  exact absurd h.2 (by decide)

/-- Together with the previous example, this refutes the unguarded
knowledge law at `false`: the announced form holds vacuously while
knowledge of the announcement fails. The law needs its guard exactly
here. -/
example : ¬ Sat guardModel (.know 0 (.announce (.atom 0) (.atom 1))) false := by
  intro h
  have h1 := h true trivial ⟨rfl, rfl⟩
  exact (by decide : ¬ ((1 : Fin 2) = 0)) h1.1

/-- The three-world chain: the atom holds at `0` and `1` only. -/
def chainModel : Model (Fin 3) Unit (Fin 1) where
  rel := fun _ a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)
  valuation := fun w _ => w = 0 ∨ w = 1
  nonempty_world := ⟨0⟩

/-- After announcing the atom on the chain model, common knowledge of the
atom holds at `0`: paths may only land in announced worlds (`0` and `1`). -/
example :
    Sat chainModel
      (.announce (.atom ()) (.common {0} (.atom ()))) 0 := by
  intro _h v hv
  induction hv with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
      obtain ⟨i, -, hP, hrel⟩ := hstep
      rcases hrel with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr rfl
      · exact False.elim ((by decide : ¬ ((2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1)) hP)

/-- Learning by announcement: once agent `1` hears that the coin is
heads, agent `1` knows it. This would fail if knowledge steps ignored the
announced worlds. -/
example :
    Sat muddy (.announce (.atom ()) (.know 1 (.atom ()))) true := by
  intro _h v hv _hr
  exact hv

/-- A nested announcement still requires its inner guard: announcing
that agent `1` does not know the coin, then announcing that agent `1`
knows it, is contradictory, so falsity follows. This fails if the inner
announcement drops its guard. -/
example :
    Sat muddy
      (.announce (.not (.know 1 (.atom ())))
        (.announce (.know 1 (.atom ())) .bot)) true := by
  intro _ h
  exact Bool.false_ne_true
    (h false (by intro hk; exact Bool.false_ne_true (hk false trivial)) trivial)

/-- Nested announcements still restrict the worlds: after a vacuous outer
announcement and announcing the coin, agent `1` knows the coin. This
fails if the inner announcement drops the world restriction. -/
example :
    Sat muddy
      (.announce (.imp .bot .bot)
        (.announce (.atom ()) (.know 1 (.atom ())))) true := by
  intro _ _ v hv _
  exact hv.2

end Cslib.Epistemic.PublicAnnouncementTests
