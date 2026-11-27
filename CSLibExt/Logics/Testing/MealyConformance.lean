/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.Transducers.Sequential
public import CSLibExt.Logics.Testing.TestAdequacy
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Mealy-machine conformance and bounded fault domains

For the classical bounded-state setup, see Peleska, *Complete property-oriented testing with
symbolic methods*, §1, p. 1. For completeness relative to a fault domain and the state bound,
see Kocsis and Rot, *Complete test suites for automata in monoidal closed categories*,
arXiv:2411.13412v2, Definition 2.2 and the following paragraph. We use the traditional Mealy
semantics discussed in §5.1: compare entire output words from the machines' start states.
The bound limits implementation states, not input word lengths or the specification's state
count. These definitions do not construct a suite or prove the W-method.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Automata.MealyMachine

variable {S T I O : Type*}

/-- A total deterministic Mealy machine produces one output letter per input letter. -/
theorem length_runOut (M : MealyMachine S I O) (s : S) (xs : List I) :
    (M.runOut s xs).length = xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [runOut_cons, List.length_cons, ih]

/-- An implementation conforms to a specification when their start-state output words agree
on every input word, regardless of the machines' state representations. -/
def Conforms (impl : MealyMachine T I O) (spec : MealyMachine S I O) : Prop :=
  ∀ xs, impl.transduce xs = spec.transduce xs

/-- An implementation passes a finite suite if its output word agrees with the specification's
on each input word in the suite. Each test starts both machines in their initial states. -/
def PassesSuite (impl : MealyMachine T I O) (spec : MealyMachine S I O)
    (suite : Finset (List I)) : Prop :=
  Cslib.Testing.Passes impl.transduce (fun xs ys => ys = spec.transduce xs) suite

/-- The fault domain at state bound `m` contains precisely the machines with finite state
space and at most `m` states. The explicit finiteness condition excludes infinite state spaces,
for which `Nat.card` is zero. Count all states, not just reachable ones. -/
def InFaultDomain (m : ℕ) (_ : MealyMachine T I O) : Prop :=
  Finite T ∧ Nat.card T ≤ m

/-- A suite is `m`-complete if every implementation with at most `m` states that passes it
conforms to the specification. The definition uses canonical carriers `Fin n`;
`MComplete.conforms_of_passes` transfers the guarantee to any finite state carrier. -/
def MComplete (spec : MealyMachine S I O) (m : ℕ) (suite : Finset (List I)) : Prop :=
  ∀ n ≤ m, ∀ impl : MealyMachine (Fin n) I O, impl.PassesSuite spec suite → impl.Conforms spec

private def reindex (M : MealyMachine T I O) (e : T ≃ S) : MealyMachine S I O where
  start := e M.start
  step s x := (e (M.step (e.symm s) x).1, (M.step (e.symm s) x).2)

private theorem runOut_reindex (M : MealyMachine T I O) (e : T ≃ S) (s : T) (xs : List I) :
    (reindex M e).runOut (e s) xs = M.runOut s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      have hstep : (reindex M e).step (e s) x = (e (M.step s x).1, (M.step s x).2) := by
        simp only [reindex, Equiv.symm_apply_apply]
      rw [runOut_cons, runOut_cons, hstep]
      exact congrArg (List.cons (M.step s x).2) (ih (M.step s x).1)

private theorem transduce_reindex (M : MealyMachine T I O) (e : T ≃ S) (xs : List I) :
    (reindex M e).transduce xs = M.transduce xs :=
  runOut_reindex M e M.start xs

/-- Completeness transfers to every implementation in the bounded fault domain, even if its
state type lies in a different universe from the specification's state type. -/
theorem MComplete.conforms_of_passes {spec : MealyMachine S I O} {m : ℕ}
    {suite : Finset (List I)} (h : spec.MComplete m suite) (impl : MealyMachine T I O)
    (hdom : impl.InFaultDomain m) (hpass : impl.PassesSuite spec suite) : impl.Conforms spec := by
  have hpos : 0 < Nat.card T := Nat.card_pos_iff.mpr ⟨⟨impl.start⟩, hdom.1⟩
  let e := Nat.equivFinOfCardPos (Nat.ne_of_gt hpos)
  have hout (xs : List I) : (reindex impl e).transduce xs = impl.transduce xs :=
    transduce_reindex impl e xs
  have hpass' : (reindex impl e).PassesSuite spec suite :=
    fun xs hx => (hout xs).trans (hpass xs hx)
  have hconf := h (Nat.card T) hdom.2 (reindex impl e) hpass'
  exact fun xs => (hout xs).symm.trans (hconf xs)

/-- Completeness is equivalent to quantification over all implementations in the fault domain
whose state type is in `Type 0`. Use `MComplete.conforms_of_passes` for the forward implication
with a state type in any universe. -/
theorem mComplete_iff_forall_inFaultDomain (spec : MealyMachine S I O) (m : ℕ)
    (suite : Finset (List I)) : spec.MComplete m suite ↔
      ∀ (Q : Type) (impl : MealyMachine Q I O),
        impl.InFaultDomain m → impl.PassesSuite spec suite → impl.Conforms spec := by
  constructor
  · intro h _ impl
    exact h.conforms_of_passes impl
  · intro h n hn impl hpass
    exact h (Fin n) impl ⟨inferInstance, by simpa only [Nat.card_fin] using hn⟩ hpass

end Cslib.Automata.MealyMachine
