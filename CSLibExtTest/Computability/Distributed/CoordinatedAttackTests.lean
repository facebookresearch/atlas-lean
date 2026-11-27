/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.CoordinatedAttack
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Tests for the impossibility of coordinated attack

* Executions: under `andAll`, where each process keeps the conjunction of its value and the
  values it receives, a lost message changes only what its receiver computes.
* Each requirement alone is satisfiable: `andAll` satisfies validity in one round but not
  agreement, and a protocol that always decides `false` satisfies agreement but not validity.
* Both hypotheses are needed: with one process, deciding one's own input solves coordinated
  attack, and with one value every protocol does.
* `not_solvesCoordinatedAttack` applies to two processes with binary values, to any `n + 2`
  processes, and to infinitely many processes.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.CoordinatedAttack.Tests

open LossyProtocol

/-- Each process sends its value to every process in every round and replaces it by the
conjunction of its value and the values it receives, a missing message counting as `false`. -/
def andAll : LossyProtocol (Fin 2) Bool Bool Bool where
  init _ x := x
  send _ _ s _ := some s
  recv _ _ s msg := s && (msg 0).getD false && (msg 1).getD false
  output _ s := s

/-- No message is lost. -/
def allDelivered : ℕ → Fin 2 → Fin 2 → Bool := fun _ _ _ => true

/-- Only the message from process `1` to process `0` in round `0` is lost. -/
def lose10 : ℕ → Fin 2 → Fin 2 → Bool := fun r j i => !(r == 0 && j == 1 && i == 0)

example : andAll.stateAfter (fun _ => true) allDelivered 1 0 = true := by decide
example : andAll.stateAfter (fun _ => true) allDelivered 3 1 = true := by decide
example : andAll.stateAfter (fun i => i == 0) allDelivered 1 0 = false := by decide

/-- A lost message changes what its receiver computes, and nothing else in its round. -/
example : andAll.stateAfter (fun _ => true) lose10 1 0 = false := by decide
example : andAll.stateAfter (fun _ => true) lose10 1 1 = true := by decide

/-- `andAll` satisfies validity in one round. -/
theorem andAll_valid :
    ∀ (v : Bool) (i : Fin 2),
      andAll.output i (andAll.stateAfter (fun _ => v) allDelivered 1 i) = v := by
  decide

/-- `andAll` does not satisfy agreement in one round: after losing the message from `1` to `0`,
the two processes decide differently. -/
theorem andAll_not_solves : ¬ andAll.SolvesCoordinatedAttack 1 := by
  rintro ⟨hagree, -⟩
  exact absurd (hagree (fun _ => true) lose10 0 1) (by decide)

/-- A protocol for two processes that decides `false` whatever happens. -/
def alwaysFalse : LossyProtocol (Fin 2) Bool Unit Unit where
  init _ _ := ()
  send _ _ _ _ := none
  recv _ _ _ _ := ()
  output _ _ := false

/-- `alwaysFalse` satisfies agreement but not validity. -/
example (T : ℕ) :
    (∀ (x : Fin 2 → Bool) (Δ : ℕ → Fin 2 → Fin 2 → Bool) (i j : Fin 2),
      alwaysFalse.output i (alwaysFalse.stateAfter x Δ T i) =
        alwaysFalse.output j (alwaysFalse.stateAfter x Δ T j)) ∧
      alwaysFalse.output 0 (alwaysFalse.stateAfter (fun _ => true) allDelivered T 0) ≠ true := by
  simp [alwaysFalse]

/-- A single process deciding its own input. -/
def selfDecide (V : Type*) : LossyProtocol Unit V V Unit where
  init _ x := x
  send _ _ _ _ := none
  recv _ _ s _ := s
  output _ s := s

theorem selfDecide_stateAfter {V : Type*} (x : Unit → V) (Δ : ℕ → Unit → Unit → Bool) (T : ℕ) :
    (selfDecide V).stateAfter x Δ T () = x () := by
  induction T with
  | zero => rfl
  | succ T ih => simpa [stateAfter, selfDecide] using ih

/-- With one process, coordinated attack is solvable in any number of rounds, so the hypothesis
of at least two processes is needed. -/
theorem selfDecide_solves (V : Type*) (T : ℕ) : (selfDecide V).SolvesCoordinatedAttack T :=
  ⟨fun _ _ _ _ => rfl, fun v () => selfDecide_stateAfter (fun _ => v) _ T⟩

/-- With one value, every protocol solves coordinated attack, so the hypothesis of at least two
values is needed. -/
theorem solves_of_unit {G σ M : Type*} (Q : LossyProtocol G Unit σ M) (T : ℕ) :
    Q.SolvesCoordinatedAttack T :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩

/-- Two generals with binary decisions. -/
example {σ M : Type*} (Q : LossyProtocol (Fin 2) Bool σ M) (T : ℕ) :
    ¬ Q.SolvesCoordinatedAttack T :=
  Q.not_solvesCoordinatedAttack T

example : ¬ andAll.SolvesCoordinatedAttack 5 := andAll.not_solvesCoordinatedAttack 5

/-- Any `n + 2` processes. -/
example (n : ℕ) {V σ M : Type*} [Nontrivial V] (Q : LossyProtocol (Fin (n + 2)) V σ M)
    (T : ℕ) : ¬ Q.SolvesCoordinatedAttack T :=
  Q.not_solvesCoordinatedAttack T

/-- Infinitely many processes. -/
example {σ M : Type*} (Q : LossyProtocol ℕ Bool σ M) (T : ℕ) : ¬ Q.SolvesCoordinatedAttack T :=
  Q.not_solvesCoordinatedAttack T

end Cslib.Distributed.CoordinatedAttack.Tests
