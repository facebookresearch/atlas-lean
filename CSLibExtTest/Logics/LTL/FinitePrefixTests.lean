/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.LTL.FinitePrefix
import Cslib.Foundations.Data.OmegaSequence.Init

/-! # Regressions for three-valued LTL on finite prefixes -/

set_option autoImplicit false

namespace CSLibExtTest.Logics.LTL.FinitePrefix

open Cslib Cslib.LTL Cslib.LTL.Word

private def val : Bool → Unit → Prop := fun b _ => b = true

private def p : Formula Unit := .atom ()

private theorem atom_satisfied : prefixVerdict val [true] p = .satisfied := by
  apply prefixVerdict_eq_satisfied_iff.mpr
  intro w
  rw [show p = .atom () from rfl, Satisfies.atom_iff]
  rfl

private theorem atom_violated : prefixVerdict val [false] p = .violated := by
  apply prefixVerdict_eq_violated_iff.mpr
  intro w
  rw [show p = .atom () from rfl, Satisfies.atom_iff]
  change ¬ false = true
  decide

example : prefixVerdict val [] p = .inconclusive := by
  apply prefixVerdict_eq_inconclusive_iff.mpr
  refine ⟨⟨ωSequence.const true, ?_⟩, ⟨ωSequence.const false, ?_⟩⟩
  · rfl
  · change ¬ false = true
    decide

-- Further observations cannot undo either definite verdict.
example : prefixVerdict val [true, false] p = .satisfied :=
  (prefixVerdict_append_of_definite (v := [false]) (by rw [atom_satisfied]; decide)).trans
    atom_satisfied

example : prefixVerdict val [false, true] p = .violated :=
  (prefixVerdict_append_of_definite (v := [true]) (by rw [atom_violated]; decide)).trans
    atom_violated

-- Every prefix has a definite extension for F p; observing p suffices.
example : Monitorable val p.eventually := by
  intro u
  refine ⟨[true], ?_⟩
  have h : prefixVerdict val (u ++ [true]) p.eventually = .satisfied := by
    apply prefixVerdict_eq_satisfied_iff.mpr
    intro w
    apply Satisfies.eventually_iff.mpr
    refine ⟨u.length, ?_⟩
    rw [show p = .atom () from rfl, satisfiesAt_atom]
    change ((u ++ [true]) ++ω w) u.length = true
    rw [ωSequence.append_append_ωSequence, ωSequence.get_append_length]
    rfl
  rw [h]
  decide

-- GF p remains inconclusive: true and false constant tails witness the two outcomes.
private theorem recurrent_inconclusive (u : List Bool) :
    prefixVerdict val u p.eventually.always = .inconclusive := by
  apply prefixVerdict_eq_inconclusive_iff.mpr
  refine ⟨⟨ωSequence.const true, ?_⟩, ⟨ωSequence.const false, ?_⟩⟩
  · rw [Satisfies.always_eventually_iff, Filter.frequently_atTop]
    intro n
    refine ⟨u.length + n, by omega, ?_⟩
    rw [show p = .atom () from rfl, satisfiesAt_atom]
    change (u ++ω ωSequence.const true) (u.length + n) = true
    rw [ωSequence.get_append_right]
    rfl
  · rw [Satisfies.always_eventually_iff, Filter.frequently_atTop]
    intro h
    obtain ⟨n, hn, hp⟩ := h u.length
    rw [show p = .atom () from rfl, satisfiesAt_atom] at hp
    change (u ++ω ωSequence.const false) n = true at hp
    rw [ωSequence.get_append_right' hn] at hp
    change false = true at hp
    cases hp

example : ¬ Monitorable val p.eventually.always := by
  intro h
  obtain ⟨v, hv⟩ := h []
  exact hv (recurrent_inconclusive ([] ++ v))

end CSLibExtTest.Logics.LTL.FinitePrefix
