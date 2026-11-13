/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Insert
public import Mathlib.Logic.Relation

/-!
# Termination of CDCL without restarts or clause deletion

The abstract CDCL system over the canonical CNF representation `Cslib.Logic.PL.CNF`, in which a
literal is a pair `(variable, polarity)` and a clause is a list of literals. A state is a trail
of assigned literals, newest first, together with the finite set of learned clauses
(`Finset CNFClause`). `CDCLStep F` has two rules:

* `decide`: push a literal whose variable is not on the trail yet (neither polarity present);
* `learn`: add a new clause implied by the input formula `F` (`ImpliedBy`) and backjump, i.e.
  replace the trail by any suffix of it, popping its newest literals. Keeping the whole trail is
  the special case of learning without backjumping.

`cdcl_step_potential_decreases`: within a finite universe (trail variables in `vars` and
distinct, learned clauses in `clauses`), the potential
`(clauses.card - L.card) * (vars.card + 1) + (vars.card - t.length)` strictly decreases along
every step. A decide lengthens the trail by one; a learn step adds a clause, worth
`vars.card + 1`, which exceeds the at most `vars.card` that backjumping can add to the second
summand.

Scope: unit propagation and conflict analysis are not separate rules. A learn step only needs the
clause to be new and implied by `F`, and the literal that CDCL asserts after a backjump can be
pushed by a later `decide`. Restarts and clause deletion are excluded.
-/

@[expose] public section

namespace Cslib.Algorithms.SAT.CDCL

open Cslib.Logic.PL

/-- The clause `C` is a semantic consequence of the formula `F`: every assignment satisfying `F`
satisfies `C`. -/
def ImpliedBy (F : CNF) (C : CNFClause) : Prop :=
  ∀ σ, F.Satisfies σ → C.Satisfies σ

/-- A CDCL state: the trail (newest literal first) and the learned clauses. -/
abbrev CDCLState := List (Nat × Bool) × Finset CNFClause

/-- CDCL steps without restart or clause deletion: decide a
literal whose variable is not yet decided (neither polarity
present), or learn a new clause implied by `F` and backjump to a
suffix of the trail. -/
inductive CDCLStep (F : CNF) :
    CDCLState → CDCLState → Prop
  | decide (t : List (Nat × Bool)) (L : Finset CNFClause) (l : Nat × Bool)
      (h : l ∉ t) (hneg : (l.1, !l.2) ∉ t) :
      CDCLStep F (t, L) (l :: t, L)
  | learn (t t' : List (Nat × Bool)) (L : Finset CNFClause) (C : CNFClause)
      (h : ImpliedBy F C) (hnew : C ∉ L) (hback : t' <:+ t) :
      CDCLStep F (t, L) (t', insert C L)

/-- Reachability: the reflexive-transitive closure of `CDCLStep F`. -/
def CDCLReach (F : CNF) : CDCLState → CDCLState → Prop :=
  Relation.ReflTransGen (CDCLStep F)

/-- Termination of the no-restart, no-deletion system over a
finite universe: fix finite sets `vars` of variables and
`clauses` of learnable clauses. The potential
`(clauses.card - L.card) * (vars.card + 1) + (vars.card -
t.length)` strictly decreases along every step taken from a
state whose trail variables lie in `vars`, whose trail decides
distinct variables, and whose learned clauses lie in `clauses`
(and likewise for the successor state), including learn steps
that backjump. Hence no infinite decide/learn sequence exists
within the universe: well-founded induction on the potential
bounds every run. -/
theorem cdcl_step_potential_decreases {F : CNF}
    (vars : Finset ℕ) (clauses : Finset CNFClause)
    {s₁ s₂ : CDCLState} (hstep : CDCLStep F s₁ s₂)
    (hvars : ∀ l ∈ s₁.1, l.1 ∈ vars)
    (hnodup : (s₁.1.map Prod.fst).Nodup)
    (hclauses : ∀ C ∈ s₁.2, C ∈ clauses)
    (hvars₂ : ∀ l ∈ s₂.1, l.1 ∈ vars)
    (hclauses₂ : ∀ C ∈ s₂.2, C ∈ clauses) :
    (clauses.card - s₂.2.card) * (vars.card + 1) +
        (vars.card - s₂.1.length) <
      (clauses.card - s₁.2.card) * (vars.card + 1) +
        (vars.card - s₁.1.length) := by
  cases hstep with
  | decide t L l h hneg =>
      dsimp only [] at hvars hnodup hclauses hvars₂ hclauses₂ ⊢
      have hsub : (t.map Prod.fst).toFinset ⊆ vars := by
        intro x hx
        rw [List.mem_toFinset, List.mem_map] at hx
        obtain ⟨l', hl', rfl⟩ := hx
        exact hvars l' hl'
      have hcard : (t.map Prod.fst).toFinset.card = t.length := by
        rw [List.toFinset_card_of_nodup hnodup, List.length_map]
      have hlvars : l.1 ∈ vars := hvars₂ l List.mem_cons_self
      have hnotmem : l.1 ∉ (t.map Prod.fst).toFinset := by
        rw [List.mem_toFinset, List.mem_map]
        rintro ⟨l', hl', heq⟩
        by_cases h2 : l'.2 = l.2
        · apply h
          have hEq : l' = l := Prod.ext heq h2
          rw [hEq] at hl'
          exact hl'
        · apply hneg
          have h3 : l'.2 = !l.2 := by
            revert h2
            cases l'.2 <;> cases l.2 <;> simp
          have hEq : l' = (l.1, !l.2) := Prod.ext heq h3
          rw [hEq] at hl'
          exact hl'
      have hne : (t.map Prod.fst).toFinset ≠ vars := by
        intro heqV
        apply hnotmem
        rw [heqV]
        exact hlvars
      have hlt : t.length < vars.card := by
        have hss := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
        have hc := Finset.card_lt_card hss
        rw [hcard] at hc
        exact hc
      rw [List.length_cons]
      exact Nat.add_lt_add_left (by omega) _
  | learn t t' L C h hnew hback =>
      dsimp only [] at hvars hnodup hclauses hvars₂ hclauses₂ ⊢
      have hC : C ∈ clauses := hclauses₂ C (Finset.mem_insert_self C L)
      have hsub : L ⊆ clauses := Finset.subset_iff.mpr hclauses
      have hne : L ≠ clauses := by
        intro heqC
        apply hnew
        rw [heqC]
        exact hC
      have hcardlt : L.card < clauses.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      have hins : (insert C L).card = L.card + 1 :=
        Finset.card_insert_of_notMem hnew
      have hsucc : clauses.card - L.card = (clauses.card - (L.card + 1)) + 1 := by
        omega
      -- the new clause is worth `vars.card + 1`; backjumping costs at most `vars.card`
      rw [hins, hsucc, Nat.add_mul, Nat.one_mul]
      omega

end Cslib.Algorithms.SAT.CDCL
