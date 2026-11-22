/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceFirstCrossingPairing

/-!
# The full original necklace pairing core

Every missing simplex chooses its actual first crossed original joint.
The canonical two-bead coverage gives both possible full simplex types.
All remaining supplied joints and the native distinguished face are
retained by the original pairing core.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.CrossedJoints

/-- Every full original missing simplex has its same first-crossed-joint index. -/
theorem exists_index {n : ℕ} (J : Finset (Fin (n + 1))) (x : (complex.{u} J).N) :
    ∃ s : Index.{u} J,
      x.toS = SSet.S.mk s.bead.paired.val ∨ x.toS = SSet.S.mk s.bead.original.val := by
  classical
  obtain ⟨d, y, hy, hnm, rfl⟩ := x.mk_surjective
  let yND : (Δ[n] : SSet.{u}).nonDegenerate d := ⟨y, hy⟩
  let L := crossed J (stdSimplex.nonDegenerateEquiv' yND).val
  have hL : L.Nonempty := crossed_nonempty J yND hnm
  let k := L.min' hL
  have hk : k ∈ L := L.min'_mem hL
  have hj : k ∈ J := ((mem_crossed _ _ _).mp hk).1
  have hnmK : y ∉ (OriginalTwoBead.union k).obj (op ⦋d⦌) :=
    (OriginalTwoBead.not_mem_union_iff k y).mpr ((mem_crossed_support_iff J yND k).mp hk).2
  let z : (OriginalTwoBead.union.{u} k).N := SSet.Subcomplex.N.mk y hy hnmK
  obtain ⟨b, hb | hb⟩ := OriginalTwoBead.exists_index k z
  · have hc : crossed J (stdSimplex.nonDegenerateEquiv' b.paired).val = L := by
      have hd : d = b.dim + 1 := SSet.S.dim_eq_of_mk_eq hb
      cases b with
      | mk bd bx bm bl br =>
        change d = bd + 1 at hd
        subst d
        have he : yND = (OriginalTwoBead.Index.paired ⟨bd, bx, bm, bl, br⟩) :=
          Subtype.ext ((SSet.S.ext_iff _ _).mp hb)
        exact (congrArg (fun x => crossed J (stdSimplex.nonDegenerateEquiv' x).val) he).symm
    have ho : crossed J (stdSimplex.nonDegenerateEquiv' b.original).val = L := by
      rw [b.support_paired] at hc
      have hs := crossed_insert J (stdSimplex.nonDegenerateEquiv' b.original).val k
        (by
          refine ⟨?_, ?_⟩
          · obtain ⟨i, hi⟩ := b.below
            exact ⟨b.original.val i, (stdSimplex.nonDegenerateEquiv'_iff _ _).mpr ⟨i, rfl⟩, hi⟩
          · obtain ⟨i, hi⟩ := b.above
            exact ⟨b.original.val i, (stdSimplex.nonDegenerateEquiv'_iff _ _).mpr ⟨i, rfl⟩, hi⟩)
      exact hs.symm.trans hc
    refine ⟨⟨k, b, hj, fun j hj => L.min'_le j (ho ▸ hj)⟩, Or.inl hb⟩
  · have ho : crossed J (stdSimplex.nonDegenerateEquiv' b.original).val = L := by
      have hd : d = b.dim := SSet.S.dim_eq_of_mk_eq hb
      cases b with
      | mk bd bx bm bl br =>
        change d = bd at hd
        subst d
        have he : yND = bx := Subtype.ext ((SSet.S.ext_iff _ _).mp hb)
        exact (congrArg (fun x => crossed J (stdSimplex.nonDegenerateEquiv' x).val) he).symm
    refine ⟨⟨k, b, hj, fun j hj => L.min'_le j (ho ▸ hj)⟩, Or.inr hb⟩

/-- The canonical full original necklace pairing inserts its same first crossed joint. -/
def pairingCore {n : ℕ} (J : Finset (Fin (n + 1))) : (complex.{u} J).PairingCore where
  ι := Index.{u} J
  dim s := s.bead.dim
  simplex s := s.bead.paired.val
  index s := s.bead.pivotIndex
  nonDegenerate₁ s := s.bead.paired.property
  nonDegenerate₂ s := stdSimplex.OriginalFaceSupport.nonDegenerate_face _ _
  notMem₁ s := s.paired_not_mem
  notMem₂ s := by
    rw [s.bead.distinguished_face]
    exact s.original_not_mem
  injective_type₁' h := Index.injective_paired h
  injective_type₂' h := by
    simp only [OriginalTwoBead.Index.distinguished_face] at h
    exact Index.ext_original h
  type₁_ne_type₂' s t := by
    rw [t.bead.distinguished_face]
    exact s.paired_ne_original t
  surjective' x := by
    obtain ⟨s, hs | hs⟩ := exists_index J x
    · exact ⟨s, Or.inl hs⟩
    · exact ⟨s, Or.inr (by rwa [s.bead.distinguished_face])⟩

/-- Every native pairing face deletes a genuinely inner original vertex. -/
instance {n : ℕ} (J : Finset (Fin (n + 1))) : (pairingCore.{u} J).IsInner where
  ne_zero s := s.bead.pivotIndex_ne_zero
  ne_last s := s.bead.pivotIndex_ne_last

end SSet.OriginalNecklace.CrossedJoints
