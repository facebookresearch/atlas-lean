/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Insert

@[expose] public section


/-- A literal is a (possibly negated) variable; a clause is a
finset of literals; a formula is a finset of clauses. This file
is the termination core for the abstract CDCL system without
restart or clause deletion, restated self-containedly. -/
abbrev Lit := ℕ × Bool

def Lit.neg (l : Lit) : Lit := (l.1, !l.2)

def litSat (σ : ℕ → Bool) (l : Lit) : Prop := σ l.1 = l.2

def clauseSat (σ : ℕ → Bool) (c : Finset Lit) : Prop :=
  ∃ l ∈ c, litSat σ l

def formulaSat (σ : ℕ → Bool) (φ : Finset (Finset Lit)) : Prop :=
  ∀ c ∈ φ, clauseSat σ c

def ImpliedBy (φ : Finset (Finset Lit)) (C : Finset Lit) : Prop :=
  ∀ σ, formulaSat σ φ → clauseSat σ C

abbrev CDCLState := List Lit × Finset (Finset Lit)

/-- CDCL steps without restart or clause deletion: decide a
literal whose variable is not yet decided (neither polarity
present), or learn a new clause implied by `F`. -/
inductive CDCLStep (F : Finset (Finset Lit)) :
    CDCLState → CDCLState → Prop
  | decide (t : List Lit) (L : Finset (Finset Lit)) (l : Lit)
      (h : l ∉ t) (hneg : l.neg ∉ t) :
      CDCLStep F (t, L) (l :: t, L)
  | learn (t : List Lit) (L : Finset (Finset Lit)) (C : Finset Lit)
      (h : ImpliedBy F C) (hnew : C ∉ L) :
      CDCLStep F (t, L) (t, insert C L)

inductive CDCLReach (F : Finset (Finset Lit)) :
    CDCLState → CDCLState → Prop
  | refl (s : CDCLState) : CDCLReach F s s
  | tail {s₁ s₂ s₃ : CDCLState} (h : CDCLReach F s₁ s₂)
      (hstep : CDCLStep F s₂ s₃) : CDCLReach F s₁ s₃

/-- Termination of the no-restart, no-deletion system over a
finite universe: fix finite sets `vars` of variables and
`clauses` of learnable clauses. The potential
`(clauses.card - L.card) * (vars.card + 1) + (vars.card -
t.length)` strictly decreases along every step taken from a
state whose trail variables lie in `vars`, whose trail decides
distinct variables, and whose learned clauses lie in `clauses`
(and likewise for the successor state). Hence no infinite
decide/learn sequence exists within the universe: well-founded
induction on the potential bounds every run. -/
theorem cdcl_step_potential_decreases {F : Finset (Finset Lit)}
    (vars : Finset ℕ) (clauses : Finset (Finset Lit))
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
          have hEq : l' = l.neg := Prod.ext heq h3
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
  | learn t L C h hnew =>
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
      rw [hins, hsucc, Nat.add_mul, Nat.one_mul]
      omega
