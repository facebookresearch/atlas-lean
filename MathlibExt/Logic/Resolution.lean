/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.GetD

@[expose] public section


/-- A literal is a (possibly negated) variable. A clause is a
finset of literals. -/
abbrev Lit := ℕ × Bool

/-- A resolution proof of the clause `Γ` from the formula `φ`
(a list of clauses): leaves are input clauses; a `resolve` node
combines proofs of `insert (v, true) C` and `insert (v, false) D`
(where the pivot literals do not occur in the opposite side
clauses) into a proof of `C ∪ D`. -/
inductive ResProof (φ : List (Finset Lit)) : Finset Lit → Type
  | input (i : Fin φ.length) : ResProof φ φ[i.val]
  | resolve (v : ℕ) (C D : Finset Lit)
      (hC : ResProof φ (insert (v, true) C))
      (hD : ResProof φ (insert (v, false) D))
      (h₃ : (v, true) ∉ D) (h₄ : (v, false) ∉ C) :
      ResProof φ (C ∪ D)

/-- An assignment satisfies a clause if it satisfies some literal
in it. -/
def clauseSat (σ : ℕ → Bool) (c : Finset Lit) : Prop :=
  ∃ l ∈ c, σ l.1 = l.2

private theorem resProof_sat {φ : List (Finset Lit)} {Γ : Finset Lit}
    (h : ResProof φ Γ) (σ : ℕ → Bool) (hσ : ∀ c ∈ φ, clauseSat σ c) :
    clauseSat σ Γ := by
  refine ResProof.rec
    (motive := fun Γ _ => ∀ (σ : ℕ → Bool), (∀ c ∈ φ, clauseSat σ c) → clauseSat σ Γ)
    ?_ ?_ h σ hσ
  · intro i σ hσ
    exact hσ _ (List.getElem_mem i.isLt)
  · intro v C D _ _ _ _ ihC ihD σ hσ
    cases hv : σ v
    case false =>
      obtain ⟨l, hl, hsat⟩ := ihC σ hσ
      rw [Finset.mem_insert] at hl
      rcases hl with rfl | hlC
      · simp [hv] at hsat
      · exact ⟨l, Finset.mem_union_left _ hlC, hsat⟩
    case true =>
      obtain ⟨l, hl, hsat⟩ := ihD σ hσ
      rw [Finset.mem_insert] at hl
      rcases hl with rfl | hlD
      · simp [hv] at hsat
      · exact ⟨l, Finset.mem_union_right _ hlD, hsat⟩

/-- Soundness of resolution: if there is a resolution proof of
the empty clause from `φ`, then `φ` is unsatisfiable. -/
theorem resolution_sound {φ : List (Finset Lit)} (h : ResProof φ ∅)
    (σ : ℕ → Bool) (hσ : ∀ c ∈ φ, clauseSat σ c) : False := by
  obtain ⟨l, hl, _⟩ := resProof_sat h σ hσ
  exact Finset.notMem_empty l hl
