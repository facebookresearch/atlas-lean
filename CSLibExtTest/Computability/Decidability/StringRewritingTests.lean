/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.StringRewriting

@[expose] public section

/-!
# Tests for string rewriting and its reduction to MPCP
-/

set_option autoImplicit false

open Cslib.Decidability Cslib.Decidability.Post Cslib.Decidability.Rewriting

namespace CSLibExtTest.Computability.Decidability.StringRewriting

/-- The rule `0 → 1` rewrites `00` to `11` in two steps. -/
theorem derives_00_11 : Derives [([0], [1])] [0, 0] [1, 1] := by
  have h₁ : Step [([0], [1])] [0, 0] [1, 0] := by
    simpa using Step.mk (R := [([0], [1])]) [] [0] (List.mem_singleton_self _)
  have h₂ : Step [([0], [1])] [1, 0] [1, 1] := by
    simpa using Step.mk (R := [([0], [1])]) [1] [] (List.mem_singleton_self _)
  exact (Derives.single h₁).trans (Derives.single h₂)

/-- Hence the MPCP instance of `(0 → 1, 00, 11)` is solvable. -/
example : MPCP (toMPCP (([([0], [1])], [0, 0], [1, 1]) : List (Rule ℕ) × List ℕ × List ℕ)) :=
  sr_iff_mpcp_toMPCP.mp derives_00_11

/-- Without rules, a word rewrites only to itself. -/
theorem eq_of_derives_nil {x y : List ℕ} (h : Derives [] x y) : x = y := by
  induction h with
  | refl => rfl
  | tail _ hs _ => obtain ⟨_, _, hr⟩ := hs; simp at hr

/-- So `(∅, 0, 1)` has no MPCP solution. -/
example : ¬MPCP (toMPCP (([], [0], [1]) : List (Rule ℕ) × List ℕ × List ℕ)) := fun h ↦
  absurd (eq_of_derives_nil (sr_iff_mpcp_toMPCP.mpr h)) (by simp)

/-- The first domino of the instance is `($, $x#)`. -/
example : (toMPCP (([([0], [1])], [0, 0], [1, 1]) : List (Rule ℕ) × List ℕ × List ℕ)).head? =
    some ([endMark], [endMark, letter 0, letter 0, star]) := rfl

/-- The composed reduction to PCP, over `ℕ`. -/
example : ManyOneReducible (fun I : List (Rule ℕ) × List ℕ × List ℕ ↦ NonemptyRules I.1 ∧ SR I)
    (PCP (α := Sym (Sym ℕ))) :=
  manyOneReducible_sr_pcp

/-- With the rule `a → b`, `b` and `a` are equivalent in the Thue system although `b` does not
rewrite to `a`. -/
example : ThueWP ([([0], [1])], [1], [0]) ∧ ¬SR ([([0], [1])], [1], [0]) := by
  have hstep : Step [([0], [1])] [0] [1] := Step.of_mem (List.mem_singleton_self _)
  refine ⟨Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hstep), fun h ↦ ?_⟩
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hs, -⟩
  · cases h
  · generalize hw : ([1] : List ℕ) = w at hs
    rcases hs with @⟨l, r, u, v, hr⟩
    simp only [List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have : (0 : ℕ) ∈ ([1] : List ℕ) := by rw [hw]; simp
    simp at this

end CSLibExtTest.Computability.Decidability.StringRewriting
