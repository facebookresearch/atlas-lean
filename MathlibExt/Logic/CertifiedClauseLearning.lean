/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Resolution

/-!
# Certified clause learning

An abstract transition system over a fixed formula `F`: decide a fresh literal, learn a clause
`C` together with a certificate `ImpliedBy F C` that every model of `F` satisfies `C`, or
restart (clear the trail, keep the learned clauses). `certifiedClause_learned_implied` shows
that every learned clause of a reachable state is implied by `F`, and `certifiedClause_unsat`
that learning the empty clause makes `F` unsatisfiable.

This is the decide/learn/restart skeleton of CDCL with the learning certificate taken as a
premise of the `learn` step. Unit propagation and conflict analysis are not modeled, so these
results are not a soundness proof for CDCL; such a proof would still have to show that conflict
analysis learns only implied clauses.

Literals and clause satisfaction (`Lit`, `clauseSat`) are those of
`MathlibExt.Logic.Resolution`.
-/

@[expose] public section


/-- The negation of a literal. -/
def Lit.neg (l : Lit) : Lit := (l.1, !l.2)

/-- An assignment satisfies a formula, a finset of clauses, if it satisfies every clause. -/
def formulaSat (σ : ℕ → Bool) (φ : Finset (Finset Lit)) : Prop :=
  ∀ c ∈ φ, clauseSat σ c

/-- A clause is implied by a formula if every model of the
formula satisfies it. -/
def ImpliedBy (φ : Finset (Finset Lit)) (C : Finset Lit) : Prop :=
  ∀ σ, formulaSat σ φ → clauseSat σ C

/-- A state of the certified clause-learning system: a trail of
decided literals (head is most recent) and a set of learned clauses. -/
abbrev CertifiedClauseState := List Lit × Finset (Finset Lit)

/-- Certified clause-learning steps over a fixed formula `F`:
decide a fresh literal, learn a clause `C` given a certificate
`ImpliedBy F C`, or restart (clear the trail, keep learned clauses).
The certificate is a premise of `learn`; no propagation or
conflict-analysis rule produces it. -/
inductive CertifiedClauseStep (F : Finset (Finset Lit)) :
    CertifiedClauseState → CertifiedClauseState → Prop
  | decide (t : List Lit) (L : Finset (Finset Lit)) (l : Lit)
      (h : l ∉ t) (hneg : l.neg ∉ t) :
      CertifiedClauseStep F (t, L) (l :: t, L)
  | learn (t : List Lit) (L : Finset (Finset Lit)) (C : Finset Lit)
      (h : ImpliedBy F C) :
      CertifiedClauseStep F (t, L) (t, insert C L)
  | restart (t : List Lit) (L : Finset (Finset Lit)) :
      CertifiedClauseStep F (t, L) ([], L)

/-- Reachability in the certified clause-learning system. -/
inductive CertifiedClauseReach (F : Finset (Finset Lit)) :
    CertifiedClauseState → CertifiedClauseState → Prop
  | refl (s : CertifiedClauseState) : CertifiedClauseReach F s s
  | tail {s₁ s₂ s₃ : CertifiedClauseState} (h : CertifiedClauseReach F s₁ s₂)
      (hstep : CertifiedClauseStep F s₂ s₃) : CertifiedClauseReach F s₁ s₃

/-- Generalized invariant: from any start state with no learned
clauses, every learned clause of any reachable end state is
implied. `induction` needs the end state to stay generalized,
so this helper quantifies over both states. -/
private theorem certifiedClause_learned_implied_aux {F : Finset (Finset Lit)}
    {s₁ s₂ : CertifiedClauseState} (h : CertifiedClauseReach F s₁ s₂) :
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

/-- Every learned clause of a state reachable from a state with no
learned clauses is implied by the formula: each one entered through
a certified `learn` step. -/
theorem certifiedClause_learned_implied {F : Finset (Finset Lit)}
    {t₀ : List Lit} {t : List Lit} {L : Finset (Finset Lit)}
    (h : CertifiedClauseReach F (t₀, ∅) (t, L)) :
    ∀ C ∈ L, ImpliedBy F C := by
  exact certifiedClause_learned_implied_aux h rfl

/-- If a state reachable from a state with no learned clauses has
learned the empty clause, the formula is unsatisfiable. -/
theorem certifiedClause_unsat {F : Finset (Finset Lit)}
    {t₀ : List Lit} {t : List Lit} {L : Finset (Finset Lit)}
    (h : CertifiedClauseReach F (t₀, ∅) (t, L)) (hempty : ∅ ∈ L) :
    ¬ ∃ σ, formulaSat σ F := by
  rintro ⟨σ, hσ⟩
  obtain ⟨l, hl, -⟩ := certifiedClause_learned_implied h ∅ hempty σ hσ
  exact Finset.notMem_empty l hl
