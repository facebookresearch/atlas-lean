/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryMixedCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryPositiveReindex
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryActiveReindex

/-!
# Active positive-face reindexing for the bisimplicial Shih boundary

The existing global finite equivalence partitions active upper faces into the
exceptional left edge and ordinary left/right insertion families.  Mixed
faces cancel under their partner involution.  This file evaluates that
combinatorial reindexing with the bisimplicial boundary terms.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

open AlgebraicTopology.EilenbergZilber

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

/-- The bisimplicial upper boundary term represented by active data. -/
noncomputable def shihUpperActiveDataTerm {n : ℕ}
    (z : ShihUpperActiveData n) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) :=
  let w := (shihUpperPositiveActiveEquiv n).symm z
  shihUpperBoundaryTerm B (n + 1) w.val.val.1 w.val.val.2.succ

/-- Express an active-data term through its intrinsic Shih index and face. -/
theorem shihUpperActiveDataTerm_eq
    {n : ℕ} (z : ShihUpperActiveData n) :
    shihUpperActiveDataTerm B z =
      shihUpperBoundaryTerm B (n + 1) z.1
        (z.1.activeBoundaryFace z.2) := by
  rcases z with ⟨i, r⟩
  dsimp only [shihUpperActiveDataTerm, shihUpperPositiveActiveEquiv]
  congr 1
  apply Fin.ext
  change (i.gap + r.val - 1) + 1 = i.gap + r.val
  have hgap := i.gap_pos
  omega

@[simp]
theorem shihUpperActiveDataTerm_leftInsertion
    {n : ℕ} (z : ShihLeftInsertionData n) :
    shihUpperActiveDataTerm B (leftInsertionToActive z).val =
      shihUpperBoundaryTerm B (n + 1) (z.1.leftUpperOf z.2)
        (z.1.leftUpperFaceOf z.2) := by
  rw [shihUpperActiveDataTerm_eq]
  congr 1
  apply Fin.ext
  simp [leftInsertionToActive, ShihIndex.leftUpperLocalFaceOf,
    ShihIndex.leftUpperFaceOf, ShihIndex.activeBoundaryFace]

@[simp]
theorem shihUpperActiveDataTerm_rightInsertion
    {n : ℕ} (z : ShihRightInsertionData n) :
    shihUpperActiveDataTerm B (rightInsertionToActive z).val =
      shihUpperBoundaryTerm B (n + 1) (z.1.rightUpperOf z.2)
        (z.1.rightUpperFaceOf z.2) := by
  rw [shihUpperActiveDataTerm_eq]
  congr 1
  apply Fin.ext
  simp [rightInsertionToActive, ShihIndex.rightUpperLocalFaceOf,
    ShihIndex.rightUpperFaceOf, ShihIndex.activeBoundaryFace]

@[simp]
theorem shihUpperActiveDataTerm_leftEdge
    {n : ℕ} (z : ShihLeftEdgeData n) :
    shihUpperActiveDataTerm B (leftEdgeToActive z).val =
      shihUpperBoundaryTerm B (n + 1)
        (ShihIndex.leftEdgeIndex (n + 1) z.1 z.2)
        (ShihIndex.leftEdgeFace (n + 1) z.1 z.2) := by
  rw [shihUpperActiveDataTerm_eq]
  congr 1

/-- Expand the exceptional left-edge data sum. -/
theorem sum_shihLeftEdgeData_term (n : ℕ) :
    (∑ z : ShihLeftEdgeData n,
      shihUpperActiveDataTerm B (leftEdgeToActive z).val) =
    ∑ q : Fin (n + 1),
      (shihUpperBoundaryTerm B (n + 1)
          (ShihIndex.leftEdgeIndex (n + 1) q 0)
          (ShihIndex.leftEdgeFace (n + 1) q 0) +
        shihUpperBoundaryTerm B (n + 1)
          (ShihIndex.leftEdgeIndex (n + 1) q (Fin.last 1))
          (ShihIndex.leftEdgeFace (n + 1) q (Fin.last 1))) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fin.sum_univ_two]
  rw [shihUpperActiveDataTerm_leftEdge,
    shihUpperActiveDataTerm_leftEdge]
  rw [show (1 : Fin 2) = Fin.last 1 by rfl]

/-- Split the inserted-left data into zero, interior, and last positions. -/
theorem sum_shihLeftInsertionData_term (n : ℕ) :
    (∑ z : ShihLeftInsertionData n,
      shihUpperActiveDataTerm B (leftInsertionToActive z).val) =
    ((∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1) (i.leftUpperOf 0)
          (i.leftUpperFaceOf 0)) +
      (∑ z : ShihLowerLeftData n,
        shihUpperBoundaryTerm B (n + 1) (z.1.leftUpperOf z.2)
          (z.1.leftUpperFaceOf z.2)) +
      ∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1)
          (i.leftUpperOf (Fin.last (i.p + 2)))
          (i.leftUpperFaceOf (Fin.last (i.p + 2)))) := by
  rw [sum_shihLeftInsertionData_split]
  apply congrArg₂ (fun a b => a + b)
  · apply congrArg₂ (fun a b => a + b)
    · apply Finset.sum_congr rfl
      intro i _
      exact shihUpperActiveDataTerm_leftInsertion B ⟨i, 0⟩
    · apply Finset.sum_congr rfl
      rintro ⟨i, a⟩ _
      exact shihUpperActiveDataTerm_leftInsertion B ⟨i, a.val⟩
  · apply Finset.sum_congr rfl
    intro i _
    exact shihUpperActiveDataTerm_leftInsertion B
      ⟨i, Fin.last (i.p + 2)⟩

/-- Split the inserted-right data into zero and positive positions. -/
theorem sum_shihRightInsertionData_term (n : ℕ) :
    (∑ z : ShihRightInsertionData n,
      shihUpperActiveDataTerm B (rightInsertionToActive z).val) =
    ((∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1) (i.rightUpperOf 0)
          (i.rightUpperFaceOf 0)) +
      ∑ z : ShihLowerRightData n,
        shihUpperBoundaryTerm B (n + 1) (z.1.rightUpperOf z.2)
          (z.1.rightUpperFaceOf z.2)) := by
  rw [sum_shihRightInsertionData_split]
  apply congrArg₂ (fun a b => a + b)
  · apply Finset.sum_congr rfl
    intro i _
    exact shihUpperActiveDataTerm_rightInsertion B ⟨i, 0⟩
  · apply Finset.sum_congr rfl
    rintro ⟨i, b⟩ _
    exact shihUpperActiveDataTerm_rightInsertion B ⟨i, b.val⟩

/-- The global mixed active family cancels. -/
theorem shihUpperMixedData_sum_eq_zero_global (n : ℕ) :
    ∑ z : ShihUpperMixedData n, shihUpperActiveDataTerm B z.val = 0 := by
  apply Finset.sum_involution (fun z _ => z.partner)
  · intro z _
    rw [shihUpperActiveDataTerm_eq, shihUpperActiveDataTerm_eq]
    simpa only [ShihUpperMixedData.partner,
      ShihUpperMixedData.mixedFace_faceIndex,
      ShihIndex.activeBoundaryFace, ShihIndex.replaceShuffle,
      ShihIndex.gap] using
      shihMixedActiveBoundaryTerm_add_partner_eq_zero
        B z.val.1 z.mixedFace rfl
  · intro z _ _
    exact z.partner_ne
  · intro z _
    exact z.partner_partner
  · intro z _
    simp

/-- The active upper reindexing identity for bisimplicial boundary terms. -/
def ShihActiveUpperReindexIdentity (n : ℕ) : Prop :=
  (∑ z : ShihUpperActiveData n, shihUpperActiveDataTerm B z) =
    (∑ q : Fin (n + 1),
      (shihUpperBoundaryTerm B (n + 1)
          (ShihIndex.leftEdgeIndex (n + 1) q 0)
          (ShihIndex.leftEdgeFace (n + 1) q 0) +
        shihUpperBoundaryTerm B (n + 1)
          (ShihIndex.leftEdgeIndex (n + 1) q (Fin.last 1))
          (ShihIndex.leftEdgeFace (n + 1) q (Fin.last 1)))) +
    ((∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1) (i.leftUpperOf 0)
          (i.leftUpperFaceOf 0)) +
      (∑ z : ShihLowerLeftData n,
        shihUpperBoundaryTerm B (n + 1) (z.1.leftUpperOf z.2)
          (z.1.leftUpperFaceOf z.2)) +
      (∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1)
          (i.leftUpperOf (Fin.last (i.p + 2)))
          (i.leftUpperFaceOf (Fin.last (i.p + 2))))) +
    ((∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1) (i.rightUpperOf 0)
          (i.rightUpperFaceOf 0)) +
      ∑ z : ShihLowerRightData n,
        shihUpperBoundaryTerm B (n + 1) (z.1.rightUpperOf z.2)
          (z.1.rightUpperFaceOf z.2))

/-- The canonical active upper reindexing identity. -/
theorem shihActiveUpperReindexIdentity (n : ℕ) :
    ShihActiveUpperReindexIdentity B n := by
  rw [ShihActiveUpperReindexIdentity]
  rw [sum_shihUpperActiveData_eq_mixed_add_nonmixed n
      (shihUpperActiveDataTerm B),
    shihUpperMixedData_sum_eq_zero_global, zero_add,
    sum_shihUpperNonmixedData_eq_activeBoundaryData n
      (shihUpperActiveDataTerm B)]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  change
    (∑ z : ShihLeftEdgeData n,
      shihUpperActiveDataTerm B (leftEdgeToActive z).val) +
      ((∑ z : ShihLeftInsertionData n,
          shihUpperActiveDataTerm B (leftInsertionToActive z).val) +
        ∑ z : ShihRightInsertionData n,
          shihUpperActiveDataTerm B (rightInsertionToActive z).val) = _
  rw [sum_shihLeftEdgeData_term,
    sum_shihLeftInsertionData_term,
    sum_shihRightInsertionData_term]
  abel

end AlgebraicTopology.BisimplicialEilenbergZilber
