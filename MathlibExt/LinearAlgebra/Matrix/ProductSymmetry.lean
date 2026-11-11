/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
state the grid symmetry criterion for canonical matrices on product types,
remove finiteness and entry-type assumptions from the public theorem, and retain a private bridge
to the source's finite ordered-pair formulation.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Symmetry of matrices indexed by a product

A matrix indexed by rows and columns is symmetric exactly when its restrictions within each row
and column are symmetric and both diagonals of every ordered rectangle agree in opposite
directions.

Adapted from `Groundwork.Grid.symm_iff` in
[`eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5),
where the matrix is represented by the definitionally equal `Half` function type.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Matrix

variable {ρ γ α : Type*} [LinearOrder ρ] [LinearOrder γ]

/-- A matrix on a product is symmetric exactly when its restrictions to each row and column are
symmetric and both diagonals of every ordered rectangle agree in opposite directions. -/
theorem isSymm_prod_iff {A : Matrix (ρ × γ) (ρ × γ) α} :
    A.IsSymm ↔
      (∀ a, (A.submatrix (a, ·) (a, ·)).IsSymm) ∧
      (∀ i, (A.submatrix (·, i) (·, i)).IsSymm) ∧
      ∀ a b i j, a < b → i < j →
        A (a, i) (b, j) = A (b, j) (a, i) ∧
          A (a, j) (b, i) = A (b, i) (a, j) := by
  constructor
  · intro h
    refine ⟨fun a => h.submatrix (a, ·), fun i => h.submatrix (·, i), ?_⟩
    intro a b i j _ _
    exact ⟨h.apply (b, j) (a, i), h.apply (b, i) (a, j)⟩
  · rintro ⟨hr, hc, hd⟩
    rw [IsSymm.ext_iff]
    rintro ⟨a, i⟩ ⟨b, j⟩
    rcases lt_trichotomy a b with hab | rfl | hba <;>
      rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hd a b i j hab hij).1.symm
    · exact (hc i).apply a b
    · exact (hd a b j i hab hji).2.symm
    · exact (hr a).apply i j
    · rfl
    · exact (hr a).apply i j
    · exact (hd b a i j hba hij).2
    · exact (hc i).apply a b
    · exact (hd b a j i hba hji).1

private def sourcePairs (ι : Type*) [Fintype ι] [LinearOrder ι] : Finset (ι × ι) :=
  Finset.univ.filter fun p => p.1 < p.2

private def sourceRectangles (ρ γ : Type*) [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] : Finset ((ρ × ρ) × (γ × γ)) :=
  sourcePairs ρ ×ˢ sourcePairs γ

private theorem source_symm_iff [Fintype ρ] [Fintype γ] (A : Matrix (ρ × γ) (ρ × γ) α) :
    A.IsSymm ↔
      ((∀ a, ∀ q ∈ sourcePairs γ,
          A (a, q.1) (a, q.2) = A (a, q.2) (a, q.1)) ∧
        (∀ i, ∀ p ∈ sourcePairs ρ,
          A (p.1, i) (p.2, i) = A (p.2, i) (p.1, i))) ∧
      ∀ ω ∈ sourceRectangles ρ γ,
        A (ω.1.1, ω.2.1) (ω.1.2, ω.2.2) =
            A (ω.1.2, ω.2.2) (ω.1.1, ω.2.1) ∧
          A (ω.1.1, ω.2.2) (ω.1.2, ω.2.1) =
            A (ω.1.2, ω.2.1) (ω.1.1, ω.2.2) := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro a q _
      exact h.apply (a, q.2) (a, q.1)
    · intro i p _
      exact h.apply (p.2, i) (p.1, i)
    · intro ω _
      exact ⟨h.apply (ω.1.2, ω.2.2) (ω.1.1, ω.2.1),
        h.apply (ω.1.2, ω.2.1) (ω.1.1, ω.2.2)⟩
  · rintro ⟨⟨hr, hc⟩, hd⟩
    rw [isSymm_prod_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [IsSymm.ext_iff]
      intro i j
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (hr a (i, j) (by simp [sourcePairs, hij])).symm
      · rfl
      · exact hr a (j, i) (by simp [sourcePairs, hji])
    · intro i
      rw [IsSymm.ext_iff]
      intro a b
      rcases lt_trichotomy a b with hab | rfl | hba
      · exact (hc i (a, b) (by simp [sourcePairs, hab])).symm
      · rfl
      · exact hc i (b, a) (by simp [sourcePairs, hba])
    · intro a b i j hab hij
      exact hd ((a, b), (i, j)) (by simp [sourceRectangles, sourcePairs, hab, hij])

end Matrix
