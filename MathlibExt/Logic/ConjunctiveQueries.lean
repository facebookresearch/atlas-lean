/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Basic

@[expose] public section


/-- A conjunctive query over variables `ℕ`: a head tuple and a
body of atoms `(relation, argument tuple)`. -/
structure CQ where
  head : List ℕ
  body : List (ℕ × List ℕ)

/-- A finite database: for each relation name, a finite set of
tuples. Domains are `ℕ` throughout. -/
abbrev DB := ℕ → Finset (List ℕ)

/-- An assignment of variables extends to terms (variables
only, no constants in this fragment). -/
abbrev Assign := ℕ → ℕ

/-- An assignment satisfies the body in the database. -/
def Satisfies (D : DB) (q : CQ) (σ : Assign) : Prop :=
  ∀ a ∈ q.body, (a.2.map σ) ∈ D a.1

/-- Query containment in assignment form: on every database,
every satisfying assignment of `Q` can be matched by a
satisfying assignment of `Q'` producing the same head tuple.
This is the assignment-level reading of `Ans Q D ⊆ Ans Q' D`
for the answer-set semantics. -/
def Contained (Q Q' : CQ) : Prop :=
  ∀ (D : DB) (σ : Assign), Satisfies D Q σ →
    ∃ τ : Assign, Satisfies D Q' τ ∧ Q'.head.map τ = Q.head.map σ

/-- A homomorphism from `Q'` to `Q`: maps variables so that
the head is preserved and every body atom of `Q'` maps to a
body atom of `Q`. -/
def Hom (Q' Q : CQ) (h : ℕ → ℕ) : Prop :=
  Q'.head.map h = Q.head ∧
    ∀ a ∈ Q'.body, (a.1, a.2.map h) ∈ Q.body

/-- The canonical database of `Q`: each body atom becomes a
fact, with variables as domain elements. -/
def canonDB (Q : CQ) : DB :=
  fun r => ((Q.body.filter (fun a => a.1 = r)).map
    (fun a => a.2)).toFinset

/-- Chandra-Merlin: containment iff there is a homomorphism
from `Q'` to `Q` mapping head to head. -/
theorem contained_iff_hom (Q Q' : CQ) :
    Contained Q Q' ↔ ∃ h, Hom Q' Q h := by
  constructor
  · -- (=>): containment yields a homomorphism, via the canonical database.
    intro hC
    have hid : Satisfies (canonDB Q) Q id := by
      intro a ha
      show (a.2.map id) ∈ canonDB Q a.1
      rw [List.map_id]
      unfold canonDB
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨a, by simp [ha], rfl⟩
    obtain ⟨τ, hτ, hhead⟩ := hC (canonDB Q) id hid
    refine ⟨τ, ?_, ?_⟩
    · rw [List.map_id] at hhead
      exact hhead
    · intro a ha
      have hmem := hτ a ha
      unfold canonDB at hmem
      rw [List.mem_toFinset, List.mem_map] at hmem
      obtain ⟨b, hbmem, hb2⟩ := hmem
      simp only [List.mem_filter] at hbmem
      obtain ⟨hbQ, hbeq⟩ := hbmem
      have hbeq' : b.1 = a.1 := of_decide_eq_true hbeq
      have heq : (a.1, a.2.map τ) = b := Prod.ext_iff.mpr ⟨hbeq'.symm, hb2.symm⟩
      rw [heq]
      exact hbQ
  · -- (<=): a homomorphism yields containment, via `τ = σ ∘ h`.
    rintro ⟨h, hhead, hbody⟩ D σ hσ
    refine ⟨σ ∘ h, ?_, ?_⟩
    · intro a ha
      have hmem : ((a.2.map h).map σ) ∈ D a.1 := hσ _ (hbody a ha)
      rwa [List.map_map] at hmem
    · rw [← List.map_map, hhead]
