/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.CDCL.Basic

@[expose] public section

/-!
# Tests for the CDCL transition system

Reachability boundary checks, a decide step, learning with explicit resolution certificates,
unsatisfiability of `x₀ ∧ ¬x₀` reached through the step relation, and a run with a decision,
conflict analysis, and a backjump on the four clauses over two variables.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.SAT.CDCL

open Cslib.Logic.PL Cslib.Algorithms.SAT.CDCL

/-- Boundary check: reachability is reflexive at the initial state of the empty formula. -/
example : Relation.ReflTransGen (Step []) State.initial State.initial :=
  Relation.ReflTransGen.refl

/-! ### `x₀ ∧ ¬x₀` -/

/-- The contradictory formula `x₀ ∧ ¬x₀`. -/
abbrev F₀ : CNF := [[(0, true)], [(0, false)]]

/-- A decide step extends the trail. -/
example : Step F₀ State.initial ⟨[.decided (0, true)], [], none⟩ :=
  .decide (by decide) (by decide)

/-- A variable that the trail assigns cannot be decided again. -/
example : ¬Step F₀ ⟨[.decided (0, true)], [], none⟩
    ⟨[.decided (0, false), .decided (0, true)], [], none⟩ := by
  generalize hs : (⟨[.decided (0, true)], [], none⟩ : State) = s
  generalize ht : (⟨[.decided (0, false), .decided (0, true)], [], none⟩ : State) = t
  intro h
  cases h with
  | decide _ hfree =>
    cases hs
    cases ht
    exact hfree (by decide)
  | _ => simp_all

/-- Only variables of the input can be decided. -/
example : ¬Step F₀ State.initial ⟨[.decided (1, true)], [], none⟩ := by
  generalize hs : State.initial = s
  generalize ht : (⟨[.decided (1, true)], [], none⟩ : State) = t
  intro h
  cases h with
  | decide hvar _ =>
    cases ht
    exact absurd hvar (by decide)
  | _ => simp_all [State.initial]

/-- Propagate `x₀` from the unit clause `x₀`. -/
theorem step_propagate :
    Step F₀ State.initial ⟨[.propagated (0, true) [(0, true)]], [], none⟩ :=
  .propagate (by decide) (by decide) (by decide) (by decide)

/-- The clause `¬x₀` is false on the trail and becomes the conflict clause. -/
theorem step_conflict :
    Step F₀ ⟨[.propagated (0, true) [(0, true)]], [], none⟩
      ⟨[.propagated (0, true) [(0, true)]], [], some [(0, false)]⟩ :=
  .conflict (by decide) (by decide)

/-- Resolving the conflict clause `¬x₀` with the reason `x₀` gives the empty clause. -/
theorem step_resolve :
    Step F₀ ⟨[.propagated (0, true) [(0, true)]], [], some [(0, false)]⟩ ⟨[], [], some []⟩ :=
  .resolve (by decide)

/-- `x₀ ∧ ¬x₀` reaches a conflict without decisions on the trail. -/
theorem reach_conflict :
    Relation.ReflTransGen (Step F₀) State.initial
      ⟨[.propagated (0, true) [(0, true)]], [], some [(0, false)]⟩ :=
  (Relation.ReflTransGen.single step_propagate).tail step_conflict

/-- The conflict without decisions refutes `x₀ ∧ ¬x₀`. -/
example : ¬CNFSat F₀ := not_cnfSat_of_reachable_conflict reach_conflict rfl (by simp)

/-- Conflict analysis then derives the empty clause, which also refutes `x₀ ∧ ¬x₀`. -/
example : ¬CNFSat F₀ := not_cnfSat_of_reachable_conflict_nil (reach_conflict.tail step_resolve) rfl

/-! ### Learning with explicit certificates -/

/-- Learn `x₀`, certified by the axiom rule; decide `¬x₀`; restart. The trail is cleared and
the learned clause is kept. -/
theorem reach_restart :
    Relation.ReflTransGen (Step F₀) State.initial ⟨[], [[(0, true)]], none⟩ :=
  ((Relation.ReflTransGen.single (Step.learn (.ax (by decide)))).tail
    (Step.decide (trail := []) (literal := (0, false)) (by decide) (by decide))).tail
    Step.restart

/-- The invariant recovers that the learned clause `x₀` is derivable from `x₀ ∧ ¬x₀`. -/
example : CNF.ResolutionDerivable F₀ [(0, true)] :=
  resolutionDerivable_of_reachable reach_restart (by decide)

/-- After the restart, learn the empty clause, certified by resolving the learned clause `x₀`
with the input clause `¬x₀`. -/
theorem reach_learn_nil :
    Relation.ReflTransGen (Step F₀) State.initial ⟨[], [[], [(0, true)]], none⟩ :=
  reach_restart.tail (Step.learn
    (.resolve (C := [(0, true)]) (D := [(0, false)]) 0 (.ax (by decide)) (.ax (by decide))
      (by decide) (by decide)))

/-- Learning the empty clause refutes `x₀ ∧ ¬x₀`. -/
example : ¬CNFSat F₀ := not_cnfSat_of_reachable_nil_mem reach_learn_nil (by decide)

/-- The learned empty clause is false on every trail, so it is also a conflict. -/
example : ¬CNFSat F₀ :=
  not_cnfSat_of_reachable_conflict_nil (reach_learn_nil.tail (.conflict (by decide) (by decide)))
    rfl

/-! ### One learn step with an explicit certificate -/

/-- The formula `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂)`. -/
abbrev F₁ : CNF := [[(0, true), (1, true)], [(0, false), (2, true)]]

/-- Learn the resolvent `x₁ ∨ x₂`; the certificate resolves the two input clauses on `x₀`. -/
theorem step_learn : Step F₁ State.initial ⟨[], [[(1, true), (2, true)]], none⟩ :=
  .learn (.resolve (C := [(0, true), (1, true)]) (D := [(0, false), (2, true)]) 0
    (.ax (by decide)) (.ax (by decide)) (by decide) (by decide))

/-- Through the invariant, every model of `F₁` satisfies the learned clause `x₁ ∨ x₂`. -/
example (σ : Nat → Bool) (hσ : F₁.Satisfies σ) : σ 1 = true ∨ σ 2 = true := by
  have h := resolutionDerivable_of_reachable (Relation.ReflTransGen.single step_learn)
    (C := [(1, true), (2, true)]) (by decide)
  simpa using h.satisfies hσ

/-! ### Decision, conflict analysis, and backjump -/

/-- The four clauses over two variables: `x₀ ∨ x₁`, `¬x₀ ∨ x₁`, `x₀ ∨ ¬x₁`, `¬x₀ ∨ ¬x₁`. -/
abbrev F₂ : CNF :=
  [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)],
    [(0, false), (1, false)]]

/-- Decide `x₀`, propagate `x₁` from `¬x₀ ∨ x₁`, hit the conflict `¬x₀ ∨ ¬x₁`, and resolve it
with the reason of `x₁` into `¬x₀ ∨ ¬x₀`. -/
theorem reach_analyzed :
    Relation.ReflTransGen (Step F₂) State.initial
      ⟨[.decided (0, true)], [], some [(0, false), (0, false)]⟩ :=
  (((Relation.ReflTransGen.single (Step.decide (trail := []) (literal := (0, true))
      (by decide) (by decide))).tail
    (Step.propagate (clause := [(0, false), (1, true)]) (literal := (1, true)) (by decide)
      (by decide) (by decide) (by decide))).tail
    (Step.conflict (clause := [(0, false), (1, false)]) (by decide) (by decide))).tail
    (Step.resolve (by decide))

/-- Backjump over the decision: learn `¬x₀ ∨ ¬x₀` and propagate `¬x₀` with it as reason. -/
theorem reach_backjump :
    Relation.ReflTransGen (Step F₂) State.initial
      ⟨[.propagated (0, false) [(0, false), (0, false)]], [[(0, false), (0, false)]], none⟩ :=
  reach_analyzed.tail
    (Step.backjump (dropped := [.decided (0, true)]) (kept := []) (by decide) (by decide)
      (by decide))

/-- Propagate `x₁` from `x₀ ∨ x₁` and hit the conflict `x₀ ∨ ¬x₁` with no decision left. -/
theorem reach_final_conflict :
    Relation.ReflTransGen (Step F₂) State.initial
      ⟨[.propagated (1, true) [(0, true), (1, true)],
          .propagated (0, false) [(0, false), (0, false)]],
        [[(0, false), (0, false)]], some [(0, true), (1, false)]⟩ :=
  (reach_backjump.tail
    (Step.propagate (clause := [(0, true), (1, true)]) (by decide) (by decide) (by decide)
      (by decide))).tail
    (Step.conflict (clause := [(0, true), (1, false)]) (by decide) (by decide))

/-- The decision-free conflict refutes the four clauses. -/
example : ¬CNFSat F₂ := not_cnfSat_of_reachable_conflict reach_final_conflict rfl (by simp)

/-- The clause learned at the backjump is derivable from the input. -/
example : CNF.ResolutionDerivable F₂ [(0, false), (0, false)] :=
  resolutionDerivable_of_reachable reach_backjump (by decide)

end CSLibExtTest.Algorithms.SAT.CDCL
