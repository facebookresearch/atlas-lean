/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexEndpointLocalGeometry
import Code.Universality.HexEndpointLocalPartitionClosure

namespace StatMech.Universality

open Complex HexWalk
open scoped BigOperators

noncomputable section


inductive HexEndpointCyclicLocalAtom (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  | triplet : HexEndpointCyclicTriplet region a h0 v du →
      HexEndpointCyclicLocalAtom region a h0 v du
  | pair : HexEndpointCyclicLoopPair region a h0 v du →
      HexEndpointCyclicLocalAtom region a h0 v du

def HexEndpointCyclicLocalAtom.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ} :
    HexEndpointCyclicLocalAtom region a h0 v du → Finset (List ℤ)
  | .triplet C => C.piece
  | .pair P => P.piece

theorem HexEndpointCyclicLocalAtom.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (A : HexEndpointCyclicLocalAtom region a h0 v du) :
    ∑ ts ∈ A.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  cases A with
  | triplet C => exact C.sum_piece_zero hdu
  | pair P => exact P.sum_piece_zero hdu


structure HexEndpointCyclicLocalPartition
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (v du : ℂ) where
  atoms : Finset (HexEndpointCyclicLocalAtom R.inRegion a h0 v du)
  cover : atoms.biUnion HexEndpointCyclicLocalAtom.piece =
    R.endpointCombinedSupportFinset a h0 v du
  disjoint :
    (↑atoms : Set (HexEndpointCyclicLocalAtom R.inRegion a h0 v du)).PairwiseDisjoint
      HexEndpointCyclicLocalAtom.piece



noncomputable def hexEndpointCyclicLocalPartitionOfCover
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (hcover : ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
      ∃ A : HexEndpointCyclicLocalAtom R.inRegion a h0 v du,
        ts ∈ A.piece ∧
          A.piece ⊆ R.endpointCombinedSupportFinset a h0 v du)
    (hoverlap : ∀ A B : HexEndpointCyclicLocalAtom R.inRegion a h0 v du,
      ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
        ts ∈ A.piece → ts ∈ B.piece → A.piece = B.piece) :
    HexEndpointCyclicLocalPartition R a h0 v du := by
  classical
  have hexists := finitePiecePartition_exists
    (R.endpointCombinedSupportFinset a h0 v du)
    HexEndpointCyclicLocalAtom.piece hcover hoverlap
  let atoms := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  exact ⟨atoms, hspec.1, hspec.2⟩





noncomputable def hexEndpointCyclicLocalPartitionOfGoodCover
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (Good : HexEndpointCyclicLocalAtom R.inRegion a h0 v du → Prop)
    (hcover : ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
      ∃ A : HexEndpointCyclicLocalAtom R.inRegion a h0 v du,
        Good A ∧ ts ∈ A.piece ∧
          A.piece ⊆ R.endpointCombinedSupportFinset a h0 v du)
    (hoverlap : ∀ A B : HexEndpointCyclicLocalAtom R.inRegion a h0 v du,
      Good A → Good B →
      ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
        ts ∈ A.piece → ts ∈ B.piece → A.piece = B.piece) :
    HexEndpointCyclicLocalPartition R a h0 v du := by
  classical
  let Certified :=
    {A : HexEndpointCyclicLocalAtom R.inRegion a h0 v du // Good A}
  have hcover' : ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
      ∃ A : Certified, ts ∈ A.1.piece ∧
        A.1.piece ⊆ R.endpointCombinedSupportFinset a h0 v du := by
    intro ts hts
    obtain ⟨A, hgood, hmem, hsub⟩ := hcover ts hts
    exact ⟨⟨A, hgood⟩, hmem, hsub⟩
  have hoverlap' : ∀ A B : Certified,
      ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
        ts ∈ A.1.piece → ts ∈ B.1.piece → A.1.piece = B.1.piece := by
    intro A B
    exact hoverlap A.1 B.1 A.2 B.2
  have hexists := finitePiecePartition_exists
    (R.endpointCombinedSupportFinset a h0 v du)
    (fun A : Certified => A.1.piece) hcover' hoverlap'
  let certifiedAtoms := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  let atoms := certifiedAtoms.image Subtype.val
  refine ⟨atoms, ?_, ?_⟩
  · rw [← hspec.1]
    ext ts
    simp only [Finset.mem_biUnion, atoms, Finset.mem_image]
    constructor
    · rintro ⟨A, ⟨B, hB, rfl⟩, hmem⟩
      exact ⟨B, hB, hmem⟩
    · rintro ⟨B, hB, hmem⟩
      exact ⟨B.1, ⟨B, hB, rfl⟩, hmem⟩
  · intro A hA B hB hne
    change A ∈ atoms at hA
    change B ∈ atoms at hB
    simp only [atoms, Finset.mem_image] at hA hB
    obtain ⟨A', hA', rfl⟩ := hA
    obtain ⟨B', hB', rfl⟩ := hB
    change Disjoint A'.1.piece B'.1.piece
    exact hspec.2 hA' hB' (fun h => hne (congrArg Subtype.val h))



theorem HexEndpointCyclicLocalPartition.vertex_relation
    {R : HexFiniteRegion} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (P : HexEndpointCyclicLocalPartition R a h0 v du) :
    ((v + du) - v) *
        endpointParafObservable R.inRegion a h0 (v + du)
          (5 / 8) hexChi +
      ((v + hexOmega * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi = 0 := by
  rw [endpointVertexSum_eq_tsum_combined]
  rw [tsum_eq_sum (s := R.endpointCombinedSupportFinset a h0 v du)]
  · rw [← P.cover, Finset.sum_biUnion P.disjoint]
    exact Finset.sum_eq_zero fun A _ => A.sum_piece_zero hdu
  · intro ts hts
    by_contra hne
    exact hts ((R.mem_endpointCombinedSupportFinset a h0 v du ts).2 hne)

end

end StatMech.Universality
