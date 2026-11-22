/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceComplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadOrdinalCharts

/-!
# Actual original native necklace concatenation

Both original joint sets are mapped by the same original full prefix
and suffix operators. The complete joint union retains both original
endpoints and their same common pivot, including zero-dimensional
original necklaces.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open OriginalTwoBead.OrdinalCharts

/-- The actual native concatenation of both complete original necklaces. -/
abbrev Data.concat (T U : Data) : Data where
  dimension := T.dimension + U.dimension
  joints := T.joints.map (prefixEmbedding T.dimension U.dimension).toEmbedding ∪
    U.joints.map (suffix T.dimension U.dimension).toEmbedding
  source_joint := Finset.mem_union.mpr (Or.inl
    (Finset.mem_map.mpr ⟨0, T.source_joint, prefix_zero T.dimension U.dimension⟩))
  target_joint := Finset.mem_union.mpr (Or.inr
    (Finset.mem_map.mpr ⟨Fin.last U.dimension, U.target_joint, suffix_last T.dimension U.dimension⟩))

/-- The actual common original pivot is a joint of the entire concatenation. -/
theorem concat_pivot_joint (T U : Data) :
    pivot T.dimension U.dimension ∈ (T.concat U).joints :=
  Finset.mem_union.mpr (Or.inl
    (Finset.mem_map.mpr ⟨Fin.last T.dimension, T.target_joint, prefix_last T.dimension U.dimension⟩))

/-- Every complete original prefix simplex has precisely its original source-necklace membership. -/
theorem prefix_mem_concat_iff (T U : Data) {d : ℕ}
    (s : (Δ[T.dimension] : SSet.{u}) _⦋d⦌) :
    (SSet.stdSimplex.map (prefixOperator T.dimension U.dimension)).app (op ⦋d⦌) s ∈
      (complex (T.concat U).joints).obj (op ⦋d⦌) ↔
        s ∈ (complex T.joints).obj (op ⦋d⦌) := by
  constructor
  · intro hs
    apply (mem_complex_iff _ _).mpr
    intro j hj
    have h := (mem_complex_iff _ _).mp hs
      (prefixEmbedding T.dimension U.dimension j)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨j, hj, rfl⟩)))
    rcases h with h | h
    · exact Or.inl (fun i => (prefixEmbedding T.dimension U.dimension).le_iff_le.mp (h i))
    · exact Or.inr (fun i => (prefixEmbedding T.dimension U.dimension).le_iff_le.mp (h i))
  · intro hs
    apply (mem_complex_iff _ _).mpr
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨j, hjT, rfl⟩ := Finset.mem_map.mp hj
      rcases (mem_complex_iff _ _).mp hs j hjT with h | h
      · exact Or.inl (fun i => (prefixEmbedding T.dimension U.dimension).monotone (h i))
      · exact Or.inr (fun i => (prefixEmbedding T.dimension U.dimension).monotone (h i))
    · obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hj
      apply Or.inl
      intro i
      have hi := (s i).isLt
      change (s i).val ≤ T.dimension + j.val
      omega

/-- Every complete original suffix simplex has precisely its original second-necklace membership. -/
theorem suffix_mem_concat_iff (T U : Data) {d : ℕ}
    (s : (Δ[U.dimension] : SSet.{u}) _⦋d⦌) :
    (SSet.stdSimplex.map (suffixOperator T.dimension U.dimension)).app (op ⦋d⦌) s ∈
      (complex (T.concat U).joints).obj (op ⦋d⦌) ↔
        s ∈ (complex U.joints).obj (op ⦋d⦌) := by
  constructor
  · intro hs
    apply (mem_complex_iff _ _).mpr
    intro j hj
    have h := (mem_complex_iff _ _).mp hs
      (suffix T.dimension U.dimension j)
      (Finset.mem_union.mpr (Or.inr (Finset.mem_map.mpr ⟨j, hj, rfl⟩)))
    rcases h with h | h
    · exact Or.inl (fun i => (suffix T.dimension U.dimension).le_iff_le.mp (h i))
    · exact Or.inr (fun i => (suffix T.dimension U.dimension).le_iff_le.mp (h i))
  · intro hs
    apply (mem_complex_iff _ _).mpr
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hj
      apply Or.inr
      intro i
      have hj := j.isLt
      change j.val ≤ T.dimension + (s i).val
      omega
    · obtain ⟨j, hjU, rfl⟩ := Finset.mem_map.mp hj
      rcases (mem_complex_iff _ _).mp hs j hjU with h | h
      · exact Or.inl (fun i => (suffix T.dimension U.dimension).monotone (h i))
      · exact Or.inr (fun i => (suffix T.dimension U.dimension).monotone (h i))

/-- The whole actual native prefix pullback is precisely the original first necklace. -/
theorem concat_preimage_prefix (T U : Data) :
    (complex.{u} (T.concat U).joints).preimage
      (SSet.stdSimplex.map (prefixOperator T.dimension U.dimension)) =
        complex.{u} T.joints := by
  ext q s
  exact prefix_mem_concat_iff T U (s : (Δ[T.dimension] : SSet.{u}) _⦋q.unop.len⦌)

/-- The whole actual native suffix pullback is precisely the original second necklace. -/
theorem concat_preimage_suffix (T U : Data) :
    (complex.{u} (T.concat U).joints).preimage
      (SSet.stdSimplex.map (suffixOperator T.dimension U.dimension)) =
        complex.{u} U.joints := by
  ext q s
  exact suffix_mem_concat_iff T U (s : (Δ[U.dimension] : SSet.{u}) _⦋q.unop.len⦌)

end SSet.OriginalNecklace
