/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadSupport

/-!
# The original two-bead pairing

The native pairing retains the whole original simplex and deletes only its
distinguished pivot. No simplex, flag, or coefficient map is chosen anew.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalTwoBead.Index

variable {n : ℕ} {k : Fin (n + 1)}

/-- Original simplices determine their full pairing index. -/
theorem ext_original {s t : Index.{u} k}
    (h : SSet.S.mk s.original.val = SSet.S.mk t.original.val) : s = t := by
  cases s with
  | mk sd sx sm sb sa =>
    cases t with
    | mk td tx tm tb ta =>
      have hd : sd = td := SSet.S.dim_eq_of_mk_eq h
      subst td
      have hx : sx = tx := Subtype.ext ((SSet.S.ext_iff _ _).1 h)
      subst tx
      rfl

/-- The paired original simplex also determines its complete index. -/
theorem injective_paired {s t : Index.{u} k}
    (h : SSet.S.mk s.paired.val = SSet.S.mk t.paired.val) : s = t := by
  cases s with
  | mk sd sx sm sb sa =>
    cases t with
    | mk td tx tm tb ta =>
      have hd : sd = td := Nat.succ.inj (SSet.S.dim_eq_of_mk_eq h)
      subst td
      let s : Index.{u} k := ⟨sd, sx, sm, sb, sa⟩
      let t : Index.{u} k := ⟨sd, tx, tm, tb, ta⟩
      have hp : s.paired = t.paired := Subtype.ext ((SSet.S.ext_iff _ _).1 h)
      have hs := congrArg (fun x : (Δ[n] : SSet.{u}).nonDegenerate (sd + 1) =>
        (stdSimplex.nonDegenerateEquiv' x).val.erase k) hp
      rw [s.support_paired, t.support_paired, Finset.erase_insert s.missing,
        Finset.erase_insert t.missing] at hs
      have hx : sx = tx := stdSimplex.nonDegenerateEquiv'.injective (Subtype.ext hs)
      subst tx
      rfl

/-- An original missing-pivot face cannot be a paired simplex. -/
theorem paired_ne_original (s t : Index.{u} k) :
    SSet.S.mk s.paired.val ≠ SSet.S.mk t.original.val := by
  intro h
  cases s with
  | mk sd sx sm sb sa =>
    cases t with
    | mk td tx tm tb ta =>
      have hd : sd + 1 = td := SSet.S.dim_eq_of_mk_eq h
      subst td
      let s : Index.{u} k := ⟨sd, sx, sm, sb, sa⟩
      have hp : s.paired = tx := Subtype.ext ((SSet.S.ext_iff _ _).1 h)
      apply tm
      rw [← hp, s.support_paired]
      exact Finset.mem_insert_self _ _

end SSet.OriginalTwoBead.Index

namespace SSet.OriginalTwoBead

/-- Every original missing simplex is in the genuine pivot pairing. -/
theorem exists_index {n : ℕ} (k : Fin (n + 1)) (x : (union.{u} k).N) :
    ∃ s : Index.{u} k,
      x.toS = SSet.S.mk s.paired.val ∨ x.toS = SSet.S.mk s.original.val := by
  obtain ⟨d, y, hy, hnm, rfl⟩ := x.mk_surjective
  let yND : (Δ[n] : SSet.{u}).nonDegenerate d := ⟨y, hy⟩
  obtain ⟨hb, ha⟩ := (not_mem_union_iff k y).1 hnm
  by_cases hk : k ∈ (stdSimplex.nonDegenerateEquiv' yND).val
  · obtain ⟨i, hi⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).1 hk
    have hd : 0 < d := by
      by_contra h
      have hd0 : d = 0 := by omega
      subst d
      obtain ⟨j, hj⟩ := hb
      obtain ⟨l, hl⟩ := ha
      have he : j = l := Fin.ext (by omega)
      exact (not_lt_of_ge (le_of_lt hj)) (by simpa [he] using hl)
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    let face := stdSimplex.OriginalFaceSupport.face yND i
    have hf : (stdSimplex.nonDegenerateEquiv' face).val =
        (stdSimplex.nonDegenerateEquiv' yND).val.erase k := by
      rw [stdSimplex.OriginalFaceSupport.support_face, hi]
    have hmissing : k ∉ (stdSimplex.nonDegenerateEquiv' face).val := by
      rw [hf]
      exact Finset.notMem_erase _ _
    have hfb : ∃ j, face.val j < k := by
      obtain ⟨j, hj⟩ := hb
      have hm : y j ∈ (stdSimplex.nonDegenerateEquiv' face).val := by
        rw [hf, Finset.mem_erase]
        exact ⟨ne_of_lt hj, (stdSimplex.nonDegenerateEquiv'_iff _ _).2 ⟨j, rfl⟩⟩
      obtain ⟨l, hl⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).1 hm
      exact ⟨l, hl.trans_lt hj⟩
    have hfa : ∃ j, k < face.val j := by
      obtain ⟨j, hj⟩ := ha
      have hm : y j ∈ (stdSimplex.nonDegenerateEquiv' face).val := by
        rw [hf, Finset.mem_erase]
        exact ⟨ne_of_gt hj, (stdSimplex.nonDegenerateEquiv'_iff _ _).2 ⟨j, rfl⟩⟩
      obtain ⟨l, hl⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).1 hm
      exact ⟨l, hj.trans_eq hl.symm⟩
    let s : Index.{u} k := ⟨e, face, hmissing, hfb, hfa⟩
    have hp : s.paired = yND := by
      apply stdSimplex.nonDegenerateEquiv'.injective
      apply Subtype.ext
      rw [s.support_paired, hf, Finset.insert_erase hk]
    exact ⟨s, Or.inl ((SSet.S.ext_iff _ _).2 (congrArg Subtype.val hp.symm))⟩
  · let s : Index.{u} k := ⟨d, yND, hk, hb, ha⟩
    exact ⟨s, Or.inr rfl⟩

/-- The complete original native pairing for the two full beads. -/
noncomputable def pairingCore {n : ℕ} (k : Fin (n + 1)) :
    (union.{u} k).PairingCore where
  ι := Index.{u} k
  dim s := s.dim
  simplex s := s.paired.val
  index s := s.pivotIndex
  nonDegenerate₁ s := s.paired.property
  nonDegenerate₂ s := stdSimplex.OriginalFaceSupport.nonDegenerate_face _ _
  notMem₁ s := s.paired_not_mem
  notMem₂ s := by
    rw [s.distinguished_face]
    exact s.original_not_mem
  injective_type₁' h := Index.injective_paired h
  injective_type₂' h := by
    simp only [Index.distinguished_face] at h
    exact Index.ext_original h
  type₁_ne_type₂' s t := by
    rw [t.distinguished_face]
    exact s.paired_ne_original t
  surjective' x := by
    obtain ⟨s, hs | hs⟩ := exists_index k x
    · exact ⟨s, Or.inl hs⟩
    · exact ⟨s, Or.inr (by rwa [s.distinguished_face])⟩

/-- The pairing omits a genuine inner vertex in every dimension. -/
instance {n : ℕ} (k : Fin (n + 1)) : (pairingCore.{u} k).IsInner where
  ne_zero s := s.pivotIndex_ne_zero
  ne_last s := s.pivotIndex_ne_last

end SSet.OriginalTwoBead
