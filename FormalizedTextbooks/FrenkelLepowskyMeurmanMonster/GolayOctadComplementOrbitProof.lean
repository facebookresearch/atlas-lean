/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadComplementOrbitData

/-! Genuine original word transport of all physical supports orthogonal to octad three. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The four array certificates are these actual original strong-generator words. -/
def golayOctadComplementLetter : Fin 4 → golayAutomorphismSubgroup :=
  ![golayStrongLetter 9,
    golayStrongLetter 15 * golayStrongLetter 2 * golayStrongLetter 1,
    golayStrongLetter 15 * golayStrongLetter 7 * golayStrongLetter 1,
    golayStrongLetter 0 * golayStrongLetter 27 * golayStrongLetter 14]

private theorem triple_array_apply (a b c : golayAutomorphismSubgroup)
    (A B C : Fin 24 → Fin 24) (ha : ∀ i, a.val i = A i)
    (hb : ∀ i, b.val i = B i) (hc : ∀ i, c.val i = C i) (i : Fin 24) :
    (a * b * c).val i = A (B (C i)) := by
  change a.val (b.val (c.val i)) = _
  rw [ha, hb, hc]

/-- Each concrete word acts exactly as its checked original physical array. -/
theorem golayOctadComplement_letter_apply (k : Fin 4) (i : Fin 24) :
    (golayOctadComplementLetter k).val i = golayOctadComplementLetterArray k i := by
  fin_cases k
  · change (golayStrongLetter 9).val i = golayStrongLetterArray 9 i
    exact golayOutsidePairOctad_strong_letter_apply _ _
  · exact triple_array_apply (golayStrongLetter 15) (golayStrongLetter 2)
      (golayStrongLetter 1) (golayStrongLetterArray 15) (golayStrongLetterArray 2)
      (golayStrongLetterArray 1) (golayOutsidePairOctad_strong_letter_apply 15)
      (golayOutsidePairOctad_strong_letter_apply 2)
      (golayOutsidePairOctad_strong_letter_apply 1) i
  · exact triple_array_apply (golayStrongLetter 15) (golayStrongLetter 7)
      (golayStrongLetter 1) (golayStrongLetterArray 15) (golayStrongLetterArray 7)
      (golayStrongLetterArray 1) (golayOutsidePairOctad_strong_letter_apply 15)
      (golayOutsidePairOctad_strong_letter_apply 7)
      (golayOutsidePairOctad_strong_letter_apply 1) i
  · exact triple_array_apply (golayStrongLetter 0) (golayStrongLetter 27)
      (golayStrongLetter 14) (golayStrongLetterArray 0) (golayStrongLetterArray 27)
      (golayStrongLetterArray 14) (golayOutsidePairOctad_strong_letter_apply 0)
      (golayOutsidePairOctad_strong_letter_apply 27)
      (golayOutsidePairOctad_strong_letter_apply 14) i

/-- Every actual incoming word preserves the original section coordinates. -/
theorem golayOctadComplement_letter_preserves_coordinates (k : Fin 4) (i : Fin 24) :
    (8 ≤ ((golayOctadComplementLetter k).val i).val ∧
      ((golayOctadComplementLetter k).val i).val < 16) ↔
    (8 ≤ i.val ∧ i.val < 16) := by
  rw [golayOctadComplement_letter_apply]
  exact golayOctadComplement_letter_preserves k i

private theorem pair_node_transport (n : Fin 120) :
    ∃ p : golayAutomorphismSubgroup,
      (∀ i : Fin 24, (8 ≤ (p.val i).val ∧ (p.val i).val < 16) ↔
        (8 ≤ i.val ∧ i.val < 16)) ∧
      ((p.val 0 = (golayOctadComplementPairNode n).1 ∧
          p.val 1 = (golayOctadComplementPairNode n).2) ∨
        (p.val 0 = (golayOctadComplementPairNode n).2 ∧
          p.val 1 = (golayOctadComplementPairNode n).1)) := by
  have all : ∀ m : ℕ, ∀ n : Fin 120, n.val = m →
      ∃ p : golayAutomorphismSubgroup,
        (∀ i : Fin 24, (8 ≤ (p.val i).val ∧ (p.val i).val < 16) ↔
          (8 ≤ i.val ∧ i.val < 16)) ∧
        ((p.val 0 = (golayOctadComplementPairNode n).1 ∧
            p.val 1 = (golayOctadComplementPairNode n).2) ∨
          (p.val 0 = (golayOctadComplementPairNode n).2 ∧
            p.val 1 = (golayOctadComplementPairNode n).1)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n hm
      by_cases hn : n = 0
      · subst n
        exact ⟨1, fun _ => Iff.rfl, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨p, hpres, hp⟩ := ih _ (by
          rw [← hm]; exact golayOctadComplement_pair_parent_lt n hn)
          (golayOctadComplementPairParent n) rfl
        let q := golayOctadComplementLetter (golayOctadComplementPairLetter n)
        refine ⟨q * p, fun i => (golayOctadComplement_letter_preserves_coordinates _ _).trans
          (hpres i), ?_⟩
        have he := golayOctadComplement_pair_edge n hn
        rcases hp with ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩ <;>
          rcases he with ⟨he0, he1⟩ | ⟨he0, he1⟩
        · exact Or.inl ⟨(congrArg q.val hp0).trans
            ((golayOctadComplement_letter_apply _ _).trans he0),
            (congrArg q.val hp1).trans
              ((golayOctadComplement_letter_apply _ _).trans he1)⟩
        · exact Or.inr ⟨(congrArg q.val hp0).trans
            ((golayOctadComplement_letter_apply _ _).trans he0),
            (congrArg q.val hp1).trans
              ((golayOctadComplement_letter_apply _ _).trans he1)⟩
        · exact Or.inr ⟨(congrArg q.val hp0).trans
            ((golayOctadComplement_letter_apply _ _).trans he1),
            (congrArg q.val hp1).trans
              ((golayOctadComplement_letter_apply _ _).trans he0)⟩
        · exact Or.inl ⟨(congrArg q.val hp0).trans
            ((golayOctadComplement_letter_apply _ _).trans he1),
            (congrArg q.val hp1).trans
              ((golayOctadComplement_letter_apply _ _).trans he0)⟩
  exact all n.val n rfl

private theorem nodes_cover {α : Type*} {n : ℕ}
    (s : Finset α) (f : Fin n → α) (hf : Function.Injective f)
    (hm : ∀ i, f i ∈ s) (hc : s.card = n) (x : α) (hx : x ∈ s) :
    ∃ i, f i = x := by
  classical
  let t := Finset.univ.map ⟨f, hf⟩
  have hsub : t ⊆ s := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
    exact hm i
  have he : t = s := Finset.eq_of_subset_of_card_le hsub (by simp [t, hc])
  have ht : x ∈ t := by rw [he]; exact hx
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ht
  exact ⟨i, hi⟩

/-- Every original outside pair occurs at one of the120 certified node addresses. -/
theorem golayOctadComplement_pairs_cover (v : Fin 24 × Fin 24)
    (hv : v ∈ golayOctadComplementPairs) :
    ∃ n : Fin 120, golayOctadComplementPairNode n = v :=
  nodes_cover _ _ golayOctadComplement_pair_injective
    golayOctadComplement_pair_member golayOctadComplement_pairs_card v hv

/-- Every original disjoint octad occurs at one of the30 certified node addresses. -/
theorem golayOctadComplement_octads_cover (d : Fin 4096)
    (hd : d ∈ golayOctadComplementOctads) :
    ∃ n : Fin 30, golayOctadComplementOctadNode n = d :=
  nodes_cover _ _ golayOctadComplement_octad_injective
    golayOctadComplement_octad_member golayOctadComplement_octads_card d hd

/-- All actual outside unordered pairs have original words from the initial pair. -/
theorem golayOctadComplement_pair_from_initial (v : Fin 24 × Fin 24)
    (hv : v ∈ golayOctadComplementPairs) :
    ∃ p : golayAutomorphismSubgroup,
      (∀ i : Fin 24, (8 ≤ (p.val i).val ∧ (p.val i).val < 16) ↔
        (8 ≤ i.val ∧ i.val < 16)) ∧
      ((p.val 0 = v.1 ∧ p.val 1 = v.2) ∨ (p.val 0 = v.2 ∧ p.val 1 = v.1)) := by
  obtain ⟨n, hn⟩ := nodes_cover _ _ golayOctadComplement_pair_injective
    golayOctadComplement_pair_member golayOctadComplement_pairs_card v hv
  rw [← hn]
  exact pair_node_transport n

private theorem octad_edge_code (n : Fin 30) (hn : n ≠ 0) :
    golayPermute (golayOctadComplementLetter (golayOctadComplementOctadLetter n)).val
      (golayCodeLabelEquiv
        (golayOctadComplementOctadNode (golayOctadComplementOctadParent n))).val =
      (golayCodeLabelEquiv (golayOctadComplementOctadNode n)).val := by
  funext j
  let p := golayOctadComplementLetter (golayOctadComplementOctadLetter n)
  have hb := golayOctadComplement_octad_edge n hn (p.val.symm j)
  rw [← golayOctadComplement_letter_apply, Equiv.apply_symm_apply] at hb
  apply ZMod.val_injective 2
  change (golayEncoder (golayLabelCoefficients
    (golayOctadComplementOctadNode (golayOctadComplementOctadParent n)))
      (p.val.symm j)).val =
    (golayEncoder (golayLabelCoefficients (golayOctadComplementOctadNode n)) j).val
  rw [golayLabelEncoder_match, golayLabelEncoder_match, hb]

private theorem octad_node_transport (n : Fin 30) :
    ∃ p : golayAutomorphismSubgroup,
      (∀ i : Fin 24, (8 ≤ (p.val i).val ∧ (p.val i).val < 16) ↔
        (8 ≤ i.val ∧ i.val < 16)) ∧
      golayPermute p.val (golayCodeLabelEquiv 2063).val =
        (golayCodeLabelEquiv (golayOctadComplementOctadNode n)).val := by
  have all : ∀ m : ℕ, ∀ n : Fin 30, n.val = m →
      ∃ p : golayAutomorphismSubgroup,
        (∀ i : Fin 24, (8 ≤ (p.val i).val ∧ (p.val i).val < 16) ↔
          (8 ≤ i.val ∧ i.val < 16)) ∧
        golayPermute p.val (golayCodeLabelEquiv 2063).val =
          (golayCodeLabelEquiv (golayOctadComplementOctadNode n)).val := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n hm
      by_cases hn : n = 0
      · subst n
        exact ⟨1, fun _ => Iff.rfl, golayPermute_one _⟩
      · obtain ⟨p, hpres, hp⟩ := ih _ (by
          rw [← hm]; exact golayOctadComplement_octad_parent_lt n hn)
          (golayOctadComplementOctadParent n) rfl
        let q := golayOctadComplementLetter (golayOctadComplementOctadLetter n)
        refine ⟨q * p, fun i => (golayOctadComplement_letter_preserves_coordinates _ _).trans
          (hpres i), ?_⟩
        change golayPermute (q.val * p.val) (golayCodeLabelEquiv 2063).val = _
        rw [golayPermute_mul, hp]
        exact octad_edge_code n hn
  exact all n.val n rfl

/-- All actual disjoint octads have genuine section-preserving original word transport. -/
theorem golayOctadComplement_octad_from_initial (d : Fin 4096)
    (hd : d ∈ golayOctadComplementOctads) :
    ∃ p : golayAutomorphismSubgroup,
      (∀ i : Fin 24, (8 ≤ (p.val i).val ∧ (p.val i).val < 16) ↔
        (8 ≤ i.val ∧ i.val < 16)) ∧
      golayPermute p.val (golayCodeLabelEquiv 2063).val = (golayCodeLabelEquiv d).val := by
  obtain ⟨n, hn⟩ := nodes_cover _ _ golayOctadComplement_octad_injective
    golayOctadComplement_octad_member golayOctadComplement_octads_card d hd
  rw [← hn]
  exact octad_node_transport n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
