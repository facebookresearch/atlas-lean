/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.FaceSplit

/-!
# Reindexing the bisimplicial Alexander--Whitney ordinary faces

For each target cut `p + q = n`, the horizontal ordinary faces are indexed by
`Fin (p + 1)` and the vertical ordinary faces by `Fin (q + 1)`.  Their sum type
is canonically equivalent to `Fin (n + 2)`, the index of the diagonal faces.
This file proves the resulting double-sum identity after identifying each
ordinary face with its factored diagonal face.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitney

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasFiniteCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

/-- An ordinary horizontal face of the Alexander--Whitney summand at a fixed
target cut. -/
noncomputable def horizontalOrdinaryTerm
    (n : ℕ) (p : Fin (n + 1)) (j : Fin (p.val + 1)) :
    (diagonalAlternatingComplex B).X (n + 1) ⟶
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n :=
  let q := cutComplement n p
  ((-1 : ℤ) ^ j.val) •
    (faceToBidegreeOfEq B (p.val + 1) q (n + 1) (by
        have := cut_add n p
        omega) ≫
      (B.δ (Fin.castSucc j)).app (Opposite.op ⦋q⦌) ≫
      totalιOfEq B p.val q n (cut_add n p))

/-- An ordinary vertical face of the Alexander--Whitney summand at a fixed
target cut, including the total-complex column sign. -/
noncomputable def verticalOrdinaryTerm
    (n : ℕ) (p : Fin (n + 1))
    (k : Fin (cutComplement n p + 1)) :
    (diagonalAlternatingComplex B).X (n + 1) ⟶
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n :=
  let q := cutComplement n p
  ((-1 : ℤ) ^ (p.val + 1 + k.val)) •
    (faceToBidegreeOfEq B p.val (q + 1) (n + 1) (by
        have := cut_add n p
        omega) ≫
      (B.obj (Opposite.op ⦋p.val⦌)).δ (Fin.succ k) ≫
      totalιOfEq B p.val q n (cut_add n p))

/-- A signed diagonal face followed by the Alexander--Whitney summand at a
fixed target cut. -/
noncomputable def diagonalOrdinaryTerm
    (n : ℕ) (p : Fin (n + 1)) (i : Fin (n + 2)) :
    (diagonalAlternatingComplex B).X (n + 1) ⟶
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n :=
  ((-1 : ℤ) ^ i.val) •
    (((SimplicialObject.diagonalFunctor A).obj B).δ i ≫ summand B n p)

/-- A horizontal ordinary term is the corresponding diagonal term. -/
theorem horizontalOrdinaryTerm_eq_diagonal
    (n : ℕ) (p : Fin (n + 1)) (j : Fin (p.val + 1)) :
    horizontalOrdinaryTerm B n p j =
      diagonalOrdinaryTerm B n p
        (⟨j.val, by omega⟩ : Fin (n + 2)) := by
  unfold horizontalOrdinaryTerm diagonalOrdinaryTerm
  dsimp only
  congr 1
  have h := horizontal_ordinary_face_eq B p.val
    (cutComplement n p) n (cut_add n p) j
  have h' := h =≫ totalιOfEq B p.val (cutComplement n p) n (cut_add n p)
  rw [← Category.assoc, h']
  unfold summand
  rw [← Category.assoc, diagonal_δ]
  rfl

/-- A vertical ordinary term is the corresponding diagonal term. -/
theorem verticalOrdinaryTerm_eq_diagonal
    (n : ℕ) (p : Fin (n + 1))
    (k : Fin (cutComplement n p + 1)) :
    verticalOrdinaryTerm B n p k =
      diagonalOrdinaryTerm B n p
        (⟨p.val + 1 + k.val, by
          have := cut_add n p
          omega⟩ : Fin (n + 2)) := by
  unfold verticalOrdinaryTerm diagonalOrdinaryTerm
  dsimp only
  congr 1
  have h := vertical_ordinary_face_eq B p.val
    (cutComplement n p) n (cut_add n p) k
  have h' := h =≫ totalιOfEq B p.val (cutComplement n p) n (cut_add n p)
  rw [← Category.assoc, h']
  unfold summand
  rw [← Category.assoc, diagonal_δ]
  rfl

private def faceSplitEquiv (n : ℕ) (p : Fin (n + 1)) :
    Fin (p.val + 1) ⊕ Fin (cutComplement n p + 1) ≃ Fin (n + 2) :=
  finSumFinEquiv.trans (finCongr (by
    have := cut_add n p
    omega))

/-- After summing over all target cuts, the horizontal and vertical ordinary
faces reindex to the double sum of all diagonal faces and all target cuts. -/
theorem ordinaryTerms_eq_diagonalDoubleSum (n : ℕ) :
    (∑ p : Fin (n + 1), ∑ j : Fin (p.val + 1),
        horizontalOrdinaryTerm B n p j) +
      (∑ p : Fin (n + 1), ∑ k : Fin (cutComplement n p + 1),
        verticalOrdinaryTerm B n p k) =
    ∑ i : Fin (n + 2), ∑ p : Fin (n + 1),
      diagonalOrdinaryTerm B n p i := by
  rw [← Finset.sum_add_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  let e := faceSplitEquiv n p
  rw [← Fintype.sum_equiv e
      (fun x => diagonalOrdinaryTerm B n p (e x))
      (diagonalOrdinaryTerm B n p) (fun _ => rfl),
    Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact horizontalOrdinaryTerm_eq_diagonal B n p j
  · apply Finset.sum_congr rfl
    intro k _
    exact verticalOrdinaryTerm_eq_diagonal B n p k

end AlgebraicTopology.BisimplicialAlexanderWhitney
