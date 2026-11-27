/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Testing.MealyConformance

/-! # Regressions for Mealy-machine conformance testing -/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Testing.MealyConformance

open Cslib.Automata MealyMachine

private def spec : MealyMachine Unit Unit Bool where
  start := ()
  step _ _ := ((), false)

private def suite : Finset (List Unit) := {[()]}

-- Every one-state implementation agreeing on the single input letter
-- produces the same output on every finite word, including the empty word.
private theorem complete_one : spec.MComplete 1 suite := by
  intro n hn impl hpass
  have hstate (s : Fin n) : s = impl.start := by
    apply Fin.ext
    have h₁ := s.isLt
    have h₂ := impl.start.isLt
    omega
  have hw : impl.runOut impl.start [()] = spec.runOut spec.start [()] :=
    hpass [()] (by simp [suite])
  rw [runOut_cons, runOut_cons] at hw
  change [(impl.step impl.start ()).2] = [false] at hw
  have hout := (List.cons.inj hw).1
  intro xs
  change impl.runOut impl.start xs = spec.runOut spec.start xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x
      rw [runOut_cons, runOut_cons, hout, hstate (impl.step impl.start ()).1]
      exact congrArg (List.cons false) ih

-- The completeness guarantee applies to a carrier other than `Fin 1`.
example : spec.Conforms spec :=
  complete_one.conforms_of_passes spec ⟨inferInstance, (Nat.card_of_subsingleton ()).le⟩
    (fun _ _ => rfl)

private def delayed : MealyMachine (Fin 2) Unit Bool where
  start := 0
  step s _ := (1, decide (s = 1))

private theorem delayed_passes : delayed.PassesSuite spec suite := by
  intro xs hx
  have hxs : xs = [()] := Finset.mem_singleton.mp hx
  subst xs
  rfl

-- The same suite is not complete for the two-state fault domain: it misses
-- the second output letter of this implementation.
example : ¬ spec.MComplete 2 suite := by
  intro hc
  have he := hc 2 (by decide) delayed delayed_passes [(), ()]
  change [false, true] = [false, false] at he
  exact (by decide : [false, true] ≠ [false, false]) he

private def infinite : MealyMachine ℕ Unit Bool where
  start := 0
  step n _ := (n + 1, false)

-- A zero `Nat.card` must not let an infinite machine into the fault domain.
example : ¬ infinite.InFaultDomain 1 := by
  intro h
  have hpos : 0 < Nat.card ℕ := Nat.card_pos_iff.mpr ⟨⟨0⟩, h.1⟩
  have hzero : Nat.card ℕ = 0 := Nat.card_eq_zero_of_infinite
  omega

end CSLibExtTest.Logics.Testing.MealyConformance
