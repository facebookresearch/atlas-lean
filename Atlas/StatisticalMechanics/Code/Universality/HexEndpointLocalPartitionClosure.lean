/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Universality.HexEndpointVertex

namespace StatMech.Universality

open Complex HexWalk

noncomputable section





theorem finitePiecePartition_exists
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (support : Finset α) (piece : ι → Finset α)
    (hcover : ∀ x ∈ support,
      ∃ i : ι, x ∈ piece i ∧ piece i ⊆ support)
    (hoverlap : ∀ i j : ι, ∀ x ∈ support,
      x ∈ piece i → x ∈ piece j → piece i = piece j) :
    ∃ atoms : Finset ι,
      atoms.biUnion piece = support ∧
        (↑atoms : Set ι).PairwiseDisjoint piece := by
  classical
  let Supported := {x // x ∈ support}
  have hcover' : ∀ x : Supported,
      ∃ i : ι, x.1 ∈ piece i ∧ piece i ⊆ support := fun x =>
    hcover x.1 x.2
  choose atomOf hmem hsubset using hcover'
  let pieces : Finset (Finset α) :=
    support.attach.image fun x => piece (atomOf x)
  have hpiece (p : {p // p ∈ pieces}) :
      ∃ i : ι, piece i = p.1 ∧ piece i ⊆ support := by
    have hp : p.1 ∈ pieces := p.2
    simp only [pieces, Finset.mem_image] at hp
    obtain ⟨x, -, hx⟩ := hp
    exact ⟨atomOf x, hx, hsubset x⟩
  choose representative hrep_piece hrep_subset using hpiece
  let atoms : Finset ι := pieces.attach.image representative
  refine ⟨atoms, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      simp only [atoms, Finset.mem_image] at hi
      obtain ⟨p, -, rfl⟩ := hi
      exact hrep_subset p hxi
    · intro hx
      let sx : Supported := ⟨x, hx⟩
      have hp_mem : piece (atomOf sx) ∈ pieces := by
        simp only [pieces, Finset.mem_image]
        exact ⟨sx, Finset.mem_attach support sx, rfl⟩
      let p : {p // p ∈ pieces} := ⟨piece (atomOf sx), hp_mem⟩
      rw [Finset.mem_biUnion]
      refine ⟨representative p, ?_, ?_⟩
      · simp only [atoms, Finset.mem_image]
        exact ⟨p, Finset.mem_attach pieces p, rfl⟩
      · rw [hrep_piece p]
        exact hmem sx
  · intro i hi j hj hij
    change i ∈ atoms at hi
    change j ∈ atoms at hj
    simp only [atoms, Finset.mem_image] at hi hj
    obtain ⟨p, -, rfl⟩ := hi
    obtain ⟨q, -, rfl⟩ := hj
    change Disjoint (piece (representative p)) (piece (representative q))
    rw [Finset.disjoint_left]
    intro x hxp hxq
    have hx : x ∈ support := hrep_subset p hxp
    have hpq_piece : piece (representative p) =
        piece (representative q) :=
      hoverlap (representative p) (representative q) x hx hxp hxq
    have hpq_value : p.1 = q.1 := by
      rw [← hrep_piece p, ← hrep_piece q]
      exact hpq_piece
    have hpq : p = q := Subtype.ext hpq_value
    exact hij (congrArg representative hpq)




noncomputable def hexEndpointLocalPartitionOfCanonicalAtoms
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (atomOf : List ℤ → HexEndpointLocalAtom R.inRegion a h0 v du)
    (mem_atom : ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
      ts ∈ (atomOf ts).piece)
    (atom_subset : ∀ ts ∈ R.endpointCombinedSupportFinset a h0 v du,
      (atomOf ts).piece ⊆ R.endpointCombinedSupportFinset a h0 v du)
    (overlap_eq : ∀ x (_hx : x ∈ R.endpointCombinedSupportFinset a h0 v du)
      y (_hy : y ∈ R.endpointCombinedSupportFinset a h0 v du) z,
      z ∈ (atomOf x).piece → z ∈ (atomOf y).piece →
        atomOf x = atomOf y) :
    HexEndpointLocalPartition R a h0 v du := by
  classical
  let S := R.endpointCombinedSupportFinset a h0 v du
  let atoms := S.image atomOf
  refine {
    atoms := atoms
    cover := ?_
    disjoint := ?_ }
  · ext z
    constructor
    · intro hz
      rw [Finset.mem_biUnion] at hz
      obtain ⟨A, hA, hzA⟩ := hz
      simp only [atoms, Finset.mem_image] at hA
      obtain ⟨x, hx, rfl⟩ := hA
      exact atom_subset x hx hzA
    · intro hz
      rw [Finset.mem_biUnion]
      refine ⟨atomOf z, ?_, mem_atom z hz⟩
      simp only [atoms, Finset.mem_image]
      exact ⟨z, hz, rfl⟩
  · intro A hA B hB hAB
    change A ∈ atoms at hA
    change B ∈ atoms at hB
    simp only [atoms, Finset.mem_image] at hA hB
    obtain ⟨x, hx, rfl⟩ := hA
    obtain ⟨y, hy, rfl⟩ := hB
    change Disjoint (atomOf x).piece (atomOf y).piece
    rw [Finset.disjoint_left]
    intro z hzx hzy
    exact hAB (overlap_eq x hx y hy z hzx hzy)

end

end StatMech.Universality
