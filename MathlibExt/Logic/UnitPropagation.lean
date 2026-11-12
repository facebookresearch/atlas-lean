/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Basic

@[expose] public section


/-- A literal is a (possibly negated) variable; a clause is a
finset of literals; a formula is a finset of clauses. -/
abbrev Lit := ℕ × Bool

/-- The negation of a literal. -/
def Lit.neg (l : Lit) : Lit := (l.1, !l.2)

/-- An assignment satisfies a literal `(v, p)` if `σ v = p`, a
clause if it satisfies some literal in it, a formula if it
satisfies every clause. -/
def litSat (σ : ℕ → Bool) (l : Lit) : Prop := σ l.1 = l.2

def clauseSat (σ : ℕ → Bool) (c : Finset Lit) : Prop :=
  ∃ l ∈ c, litSat σ l

def formulaSat (σ : ℕ → Bool) (φ : Finset (Finset Lit)) : Prop :=
  ∀ c ∈ φ, clauseSat σ c

/-- Simplification under an assumed-true literal `l` (one unit
propagation step on the formula): drop clauses containing `l`,
delete `l.neg` from the rest. -/
noncomputable def simplify (φ : Finset (Finset Lit)) (l : Lit) :
    Finset (Finset Lit) :=
  (φ.filter (fun c => l ∉ c)).image (fun c => c.erase l.neg)

/-- Unit propagation conflict derivation: an inductive predicate
stating that iterated unit propagation from `φ` reaches the
empty clause: either `φ` already contains `∅`, or `φ` has a unit
clause `{l}` and the simplified formula derives a conflict. -/
inductive UPConflict : Finset (Finset Lit) → Prop
  | empty (φ : Finset (Finset Lit)) (h : ∅ ∈ φ) : UPConflict φ
  | step (φ : Finset (Finset Lit)) (l : Lit)
      (hunit : {l} ∈ φ) (h : UPConflict (simplify φ l)) :
      UPConflict φ

private theorem upConflict_no_model : ∀ {φ : Finset (Finset Lit)},
    UPConflict φ → ∀ σ : ℕ → Bool, formulaSat σ φ → False := by
  intro φ h
  induction h with
  | empty φ hmem =>
      intro σ hσ
      simp only [formulaSat, clauseSat] at hσ
      obtain ⟨l, hmem2, _⟩ := hσ ∅ hmem
      exact Finset.notMem_empty l hmem2
  | step φ l hunit _ ih =>
      intro σ hσ
      simp only [formulaSat, clauseSat] at hσ
      obtain ⟨l', hmem', hsat'⟩ := hσ {l} hunit
      have heq : l' = l := Finset.mem_singleton.mp hmem'
      rw [heq] at hsat'
      have hunit_sat : σ l.1 = l.2 := hsat'
      have hsat_simp : ∀ c ∈ simplify φ l, ∃ l₀ ∈ c, litSat σ l₀ := by
        intro c hc
        simp only [simplify, Finset.mem_image, Finset.mem_filter] at hc
        obtain ⟨c', ⟨hc'mem, _⟩, rfl⟩ := hc
        obtain ⟨l', hl'mem, hsat⟩ := hσ c' hc'mem
        by_cases hne : l' = l.neg
        · subst hne
          have hcon : σ l.1 = !l.2 := hsat
          rw [← hunit_sat] at hcon
          cases hbl : l.2 <;> simp at hcon
        · exact ⟨l', Finset.mem_erase.mpr ⟨hne, hl'mem⟩, hsat⟩
      exact ih σ hsat_simp

/-- Soundness of unit propagation: if unit propagation derives a
conflict from `φ`, then `φ` is unsatisfiable. -/
theorem upConflict_unsat {φ : Finset (Finset Lit)}
    (h : UPConflict φ) : ¬ ∃ σ, formulaSat σ φ := by
  rintro ⟨σ, hσ⟩
  exact upConflict_no_model h σ hσ
