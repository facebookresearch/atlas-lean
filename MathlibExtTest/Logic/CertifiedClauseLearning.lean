/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.CertifiedClauseLearning

@[expose] public section

namespace MathlibExtTest.CertifiedClauseLearning

/-- Boundary check: the empty formula admits the empty learned
set in the initial state, and reachability is reflexive. -/
example : CertifiedClauseReach (∅ : Finset (Finset Lit)) ([], ∅) ([], ∅) :=
  CertifiedClauseReach.refl _

/-- A decide step extends the trail. -/
example : CertifiedClauseStep (∅ : Finset (Finset Lit)) ([], ∅)
    ([(0, true)], ∅) :=
  CertifiedClauseStep.decide [] ∅ (0, true) (by decide) (by decide)

/-- The contradictory formula `x₀ ∧ ¬x₀`. -/
abbrev F₀ : Finset (Finset Lit) := {{(0, true)}, {(0, false)}}

/-- `F₀` implies its unit clause `x₀`. -/
theorem impliedBy_x₀ : ImpliedBy F₀ {(0, true)} :=
  fun _ hσ => hσ {(0, true)} (by simp [F₀])

/-- `F₀` implies the empty clause: no assignment satisfies both
`x₀` and `¬x₀`. -/
theorem impliedBy_empty : ImpliedBy F₀ ∅ := by
  intro σ hσ
  obtain ⟨l, hl, h₁⟩ := hσ {(0, true)} (by simp [F₀])
  obtain ⟨l', hl', h₂⟩ := hσ {(0, false)} (by simp [F₀])
  rw [Finset.mem_singleton] at hl hl'
  subst hl hl'
  simp only at h₁ h₂
  rw [h₁] at h₂
  exact absurd h₂ (by decide)

/-- Learn `x₀`, decide `x₁`, then restart: the trail is cleared
and the learned clause `x₀` is kept. -/
theorem reach_restart :
    CertifiedClauseReach F₀ ([], ∅) ([], insert {(0, true)} ∅) :=
  (((CertifiedClauseReach.refl _).tail
    (CertifiedClauseStep.learn [] ∅ {(0, true)} impliedBy_x₀)).tail
    (CertifiedClauseStep.decide [] _ (1, true) (by simp) (by simp))).tail
    (CertifiedClauseStep.restart [(1, true)] _)

/-- The clause learned before the restart is still learned after
it, and the invariant recovers that `F₀` implies it. -/
example : ImpliedBy F₀ {(0, true)} :=
  certifiedClause_learned_implied reach_restart {(0, true)} (Finset.mem_insert_self _ _)

/-- After the restart, learn the empty clause. -/
theorem reach_empty :
    CertifiedClauseReach F₀ ([], ∅) ([], insert ∅ (insert {(0, true)} ∅)) :=
  reach_restart.tail (CertifiedClauseStep.learn [] _ ∅ impliedBy_empty)

/-- Learning the empty clause shows that `F₀` is unsatisfiable. -/
example : ¬ ∃ σ, formulaSat σ F₀ :=
  certifiedClause_unsat reach_empty (Finset.mem_insert_self _ _)

end MathlibExtTest.CertifiedClauseLearning
