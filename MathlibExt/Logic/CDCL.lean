/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Basic

@[expose] public section


/-- A literal is a (possibly negated) variable; a clause is a
finset of literals; a formula is a finset of clauses. -/
abbrev Lit := ℕ × Bool

/-- The negation of a literal. -/
def Lit.neg (l : Lit) : Lit := (l.1, !l.2)

def litSat (σ : ℕ → Bool) (l : Lit) : Prop := σ l.1 = l.2

def clauseSat (σ : ℕ → Bool) (c : Finset Lit) : Prop :=
  ∃ l ∈ c, litSat σ l

def formulaSat (σ : ℕ → Bool) (φ : Finset (Finset Lit)) : Prop :=
  ∀ c ∈ φ, clauseSat σ c

/-- A clause is implied by a formula if every model of the
formula satisfies it. -/
def ImpliedBy (φ : Finset (Finset Lit)) (C : Finset Lit) : Prop :=
  ∀ σ, formulaSat σ φ → clauseSat σ C

/-- A CDCL state: a trail (decided/propagated literals, head is
most recent) and a set of learned clauses. -/
abbrev CDCLState := List Lit × Finset (Finset Lit)

/-- Abstract CDCL steps over a fixed original formula `F`:
decide a fresh literal, learn a clause implied by `F`, or
restart (clear the trail, keep learned clauses). Propagation and
conflict analysis are folded into `learn`: a learned clause is
exactly one the original formula implies, which is what conflict
analysis produces. -/
inductive CDCLStep (F : Finset (Finset Lit)) :
    CDCLState → CDCLState → Prop
  | decide (t : List Lit) (L : Finset (Finset Lit)) (l : Lit)
      (h : l ∉ t) (hneg : l.neg ∉ t) :
      CDCLStep F (t, L) (l :: t, L)
  | learn (t : List Lit) (L : Finset (Finset Lit)) (C : Finset Lit)
      (h : ImpliedBy F C) :
      CDCLStep F (t, L) (t, insert C L)
  | restart (t : List Lit) (L : Finset (Finset Lit)) :
      CDCLStep F (t, L) ([], L)

/-- Reachability in the abstract CDCL system. -/
inductive CDCLReach (F : Finset (Finset Lit)) :
    CDCLState → CDCLState → Prop
  | refl (s : CDCLState) : CDCLReach F s s
  | tail {s₁ s₂ s₃ : CDCLState} (h : CDCLReach F s₁ s₂)
      (hstep : CDCLStep F s₂ s₃) : CDCLReach F s₁ s₃

/-- Generalized invariant: from any start state with no learned
clauses, every learned clause of any reachable end state is
implied. `induction` needs the end state to stay generalized,
so this helper quantifies over both states. -/
private theorem cdcl_learned_implied_aux {F : Finset (Finset Lit)}
    {s₁ s₂ : CDCLState} (h : CDCLReach F s₁ s₂) :
    s₁.2 = ∅ → ∀ C ∈ s₂.2, ImpliedBy F C := by
  induction h with
  | refl =>
      intro hstart C hC
      rw [hstart] at hC
      exact absurd hC (Finset.notMem_empty C)
  | tail hreach hstep ih =>
      intro hstart
      cases hstep with
      | decide t' L' l _ _ =>
          exact ih hstart
      | learn t' L' C' hC' =>
          intro C hC
          rw [Finset.mem_insert] at hC
          rcases hC with rfl | hCold
          · exact hC'
          · exact ih hstart C hCold
      | restart t' L' =>
          exact ih hstart

/-- Soundness invariant of abstract CDCL: every learned clause
in any reachable state is implied by the original formula. -/
theorem cdcl_learned_implied {F : Finset (Finset Lit)}
    {t₀ : List Lit} {t : List Lit} {L : Finset (Finset Lit)}
    (h : CDCLReach F (t₀, ∅) (t, L)) :
    ∀ C ∈ L, ImpliedBy F C := by
  exact cdcl_learned_implied_aux h rfl

/-- CDCL soundness: if a reachable state has learned the empty
clause, the original formula is unsatisfiable. -/
theorem cdcl_unsat {F : Finset (Finset Lit)}
    {t₀ : List Lit} {t : List Lit} {L : Finset (Finset Lit)}
    (h : CDCLReach F (t₀, ∅) (t, L)) (hempty : ∅ ∈ L) :
    ¬ ∃ σ, formulaSat σ F := by
  rintro ⟨σ, hσ⟩
  obtain ⟨l, hl, -⟩ := cdcl_learned_implied h ∅ hempty σ hσ
  exact Finset.notMem_empty l hl
