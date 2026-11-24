/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNondegenerateFaceSupport
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank

/-!
# The complete original two-bead support

The two beads are the full standard-simplex faces on either side of the
same original pivot. The pairing inserts that pivot in each crossing
nondegenerate simplex that omits it.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalTwoBead

/-- The union of the two complete original faces at the given pivot. -/
def union {n : ℕ} (k : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex :=
  stdSimplex.face (Finset.univ.filter (fun j => j ≤ k)) ⊔
    stdSimplex.face (Finset.univ.filter (fun j => k ≤ j))

/-- Membership retains every ordinal vertex in one complete bead. -/
theorem mem_union_iff {n d : ℕ} (k : Fin (n + 1))
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (union k).obj (op ⦋d⦌) ↔
      (∀ j, x j ≤ k) ∨ (∀ j, k ≤ x j) := by
  simp [union, stdSimplex.mem_face_iff]

/-- A simplex outside the full bead union crosses the original pivot. -/
theorem not_mem_union_iff {n d : ℕ} (k : Fin (n + 1))
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∉ (union k).obj (op ⦋d⦌) ↔
      (∃ j, x j < k) ∧ (∃ j, k < x j) := by
  classical
  rw [mem_union_iff]
  simp only [not_or, not_forall, not_le]
  exact and_comm

/-- The original missing-pivot nondegenerate simplex indexes its pair. -/
structure Index {n : ℕ} (k : Fin (n + 1)) where
  /-- Dimension of the original face. -/
  dim : ℕ
  /-- The whole original nondegenerate face. -/
  original : (Δ[n] : SSet.{u}).nonDegenerate dim
  /-- The pivot is absent from this original support. -/
  missing : k ∉ (stdSimplex.nonDegenerateEquiv' original).val
  /-- An original vertex occurs below the pivot. -/
  below : ∃ j, original.val j < k
  /-- An original vertex occurs above the pivot. -/
  above : ∃ j, k < original.val j

namespace Index

variable {n : ℕ} {k : Fin (n + 1)} (s : Index.{u} k)

/-- The same original support after inserting the original pivot. -/
noncomputable def paired : (Δ[n] : SSet.{u}).nonDegenerate (s.dim + 1) :=
  stdSimplex.nonDegenerateEquiv'.symm
    ⟨insert k (stdSimplex.nonDegenerateEquiv' s.original).val, by
      change (insert k (stdSimplex.nonDegenerateEquiv' s.original).val).card =
        s.dim + 1 + 1
      rw [Finset.card_insert_of_notMem s.missing]
      exact congrArg Nat.succ (stdSimplex.nonDegenerateEquiv' s.original).property⟩

/-- Every original support vertex remains in the paired simplex. -/
theorem support_paired :
    (stdSimplex.nonDegenerateEquiv' s.paired).val =
      insert k (stdSimplex.nonDegenerateEquiv' s.original).val := by
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The original pivot has a genuine ordinal preimage in the paired simplex. -/
theorem exists_pivot : ∃ j, s.paired.val j = k := by
  rw [← stdSimplex.nonDegenerateEquiv'_iff, support_paired]
  exact Finset.mem_insert_self _ _

/-- The distinguished original ordinal vertex of the inserted pivot. -/
noncomputable def pivotIndex : Fin (s.dim + 2) :=
  s.exists_pivot.choose

/-- Literal evaluation of the inserted original pivot. -/
theorem paired_pivotIndex : s.paired.val s.pivotIndex = k :=
  s.exists_pivot.choose_spec

/-- The distinguished original face has exactly the old full support. -/
theorem support_distinguished :
    (stdSimplex.nonDegenerateEquiv'
      (stdSimplex.OriginalFaceSupport.face s.paired s.pivotIndex)).val =
        (stdSimplex.nonDegenerateEquiv' s.original).val := by
  rw [stdSimplex.OriginalFaceSupport.support_face, s.paired_pivotIndex,
    s.support_paired, Finset.erase_insert s.missing]

/-- Deleting the distinguished original vertex gives the same original face. -/
theorem distinguished_face :
    (Δ[n] : SSet.{u}).δ s.pivotIndex s.paired.val = s.original.val := by
  have h := Subtype.ext s.support_distinguished
  exact congrArg Subtype.val (stdSimplex.nonDegenerateEquiv'.injective h)

/-- The original missing-pivot face lies outside the full bead union. -/
theorem original_not_mem : s.original.val ∉ (union k).obj (op ⦋s.dim⦌) :=
  (not_mem_union_iff k s.original.val).2 ⟨s.below, s.above⟩

/-- The full paired simplex remains outside the original bead union. -/
theorem paired_not_mem : s.paired.val ∉ (union k).obj (op ⦋s.dim + 1⦌) := by
  apply (not_mem_union_iff k s.paired.val).2
  constructor
  · obtain ⟨j, hj⟩ := s.below
    have hm : s.original.val j ∈ (stdSimplex.nonDegenerateEquiv' s.paired).val := by
      rw [s.support_paired]
      exact Finset.mem_insert_of_mem ((stdSimplex.nonDegenerateEquiv'_iff _ _).2 ⟨j, rfl⟩)
    obtain ⟨i, hi⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).1 hm
    exact ⟨i, hi.trans_lt hj⟩
  · obtain ⟨j, hj⟩ := s.above
    have hm : s.original.val j ∈ (stdSimplex.nonDegenerateEquiv' s.paired).val := by
      rw [s.support_paired]
      exact Finset.mem_insert_of_mem ((stdSimplex.nonDegenerateEquiv'_iff _ _).2 ⟨j, rfl⟩)
    obtain ⟨i, hi⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).1 hm
    exact ⟨i, hj.trans_eq hi.symm⟩

/-- The distinguished face is genuinely inner at its first endpoint. -/
theorem pivotIndex_ne_zero : s.pivotIndex ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := s.below
  have hm : s.original.val j ∈ (stdSimplex.nonDegenerateEquiv' s.paired).val := by
    rw [s.support_paired]
    exact Finset.mem_insert_of_mem ((stdSimplex.nonDegenerateEquiv'_iff _ _).2 ⟨j, rfl⟩)
  obtain ⟨i, hi⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).1 hm
  have hle := stdSimplex.monotone_apply s.paired.val (Fin.zero_le i)
  change s.paired.val 0 ≤ s.paired.val i at hle
  rw [← h, s.paired_pivotIndex, hi] at hle
  exact (not_le_of_gt hj) hle

/-- The distinguished face is genuinely inner at its last endpoint. -/
theorem pivotIndex_ne_last : s.pivotIndex ≠ Fin.last (s.dim + 1) := by
  intro h
  obtain ⟨j, hj⟩ := s.above
  have hm : s.original.val j ∈ (stdSimplex.nonDegenerateEquiv' s.paired).val := by
    rw [s.support_paired]
    exact Finset.mem_insert_of_mem ((stdSimplex.nonDegenerateEquiv'_iff _ _).2 ⟨j, rfl⟩)
  obtain ⟨i, hi⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).1 hm
  have hle := stdSimplex.monotone_apply s.paired.val (Fin.le_last i)
  change s.paired.val i ≤ s.paired.val (Fin.last (s.dim + 1)) at hle
  rw [← h, s.paired_pivotIndex, hi] at hle
  exact (not_le_of_gt hj) hle

end Index

end SSet.OriginalTwoBead
