/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOutsidePairOctadOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence

/-! Genuine original Mathieu words carry every outside-pair octad to its actual prototype. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/- The following coordinate bindings adapt the private word-binding lemmas in
`GolayAutomorphismGeneration`, retaining the proved original-generator certificates. -/
private theorem generatingLetter_apply (t : Fin 4) (i : Fin 24) :
    (golayGeneratingLetter t).val i = golayGeneratingLetterArray t i := by
  fin_cases t <;> rfl

private theorem generatingWord_apply (w : List (Fin 4)) (i : Fin 24) :
    (golayGeneratingWord w).val i = golayGeneratingWordArray w i := by
  induction w generalizing i with
  | nil => rfl
  | cons t w ih =>
    change (golayGeneratingLetter t).val ((golayGeneratingWord w).val i) = _
    rw [generatingLetter_apply, ih]
    rfl

private theorem strong_apply (s : Fin 14) (i : Fin 24) :
    (golayStrongAutomorphism s).val i = golayStrongForward s i := by
  rw [golayStrongAutomorphism, generatingWord_apply, golayStrongWords_certificate]

private theorem strong_inverse_apply (s : Fin 14) (i : Fin 24) :
    (golayStrongAutomorphism s).val.symm i = golayStrongInverse s i := by
  apply (golayStrongAutomorphism s).val.injective
  rw [Equiv.apply_symm_apply, strong_apply, (golayStrong_inverse_certificate s i).1]

/-- Each array letter is the actual original-generator word on every physical coordinate. -/
theorem golayOutsidePairOctad_strong_letter_apply (t : Fin 28) (i : Fin 24) :
    (golayStrongLetter t).val i = golayStrongLetterArray t i := by
  unfold golayStrongLetter golayStrongLetterArray
  split_ifs
  · exact strong_apply _ i
  · exact strong_inverse_apply _ i

/-- The actual original codeword at each checked parent address. -/
def golayOutsidePairOctadNodeCode (n : Fin 330) : golayCode :=
  golayCodeLabelEquiv (golayOutsidePairOctadNodeLabel n)

/-- Every checked incoming edge is an equality under the genuine original Golay action. -/
theorem golayOutsidePairOctad_edge_code (n : Fin 330) (hn : n ≠ 0) :
    golayPermute (golayStrongLetter (golayOutsidePairOctadNodeLetter n)).val
      (golayOutsidePairOctadNodeCode (golayOutsidePairOctadNodeParent n)).val =
        (golayOutsidePairOctadNodeCode n).val := by
  funext j
  let p := golayStrongLetter (golayOutsidePairOctadNodeLetter n)
  have hb := golayOutsidePairOctad_edge_bits n hn (p.val.symm j)
  rw [← golayOutsidePairOctad_strong_letter_apply, Equiv.apply_symm_apply] at hb
  apply (ZMod.val_injective 2)
  change (golayEncoder (golayLabelCoefficients
    (golayOutsidePairOctadNodeLabel (golayOutsidePairOctadNodeParent n))) (p.val.symm j)).val =
      (golayEncoder (golayLabelCoefficients (golayOutsidePairOctadNodeLabel n)) j).val
  rw [golayLabelEncoder_match, golayLabelEncoder_match, hb]

/-- Earlier-parent recursion gives a genuine original automorphism carrying the initial
outside octad to each node while fixing both physical root coordinates pointwise. -/
theorem golayOutsidePairOctad_node_transport (n : Fin 330) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 0 ∧ p.val 1 = 1 ∧
      golayPermute p.val (golayOutsidePairOctadNodeCode 0).val =
        (golayOutsidePairOctadNodeCode n).val := by
  have all : ∀ m : ℕ, ∀ n : Fin 330, n.val = m →
      ∃ p : golayAutomorphismSubgroup, p.val 0 = 0 ∧ p.val 1 = 1 ∧
        golayPermute p.val (golayOutsidePairOctadNodeCode 0).val =
          (golayOutsidePairOctadNodeCode n).val := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n hm
      by_cases hn : n = 0
      · subst n
        exact ⟨1, rfl, rfl, golayPermute_one _⟩
      · have hlt : (golayOutsidePairOctadNodeParent n).val < m := by
          rw [← hm]
          exact golayOutsidePairOctad_parent_lt n hn
        obtain ⟨p, hp0, hp1, hp⟩ := ih _ hlt (golayOutsidePairOctadNodeParent n) rfl
        let q := golayStrongLetter (golayOutsidePairOctadNodeLetter n)
        have hq := golayOutsidePairOctad_letter_fix_pair n
        refine ⟨q * p, ?_, ?_, ?_⟩
        · change q.val (p.val 0) = 0
          rw [hp0, golayOutsidePairOctad_strong_letter_apply]
          exact hq.1
        · change q.val (p.val 1) = 1
          rw [hp1, golayOutsidePairOctad_strong_letter_apply]
          exact hq.2
        · change golayPermute (q.val * p.val) (golayOutsidePairOctadNodeCode 0).val = _
          rw [golayPermute_mul, hp]
          exact golayOutsidePairOctad_edge_code n hn
  exact all n.val n rfl

/-- All actual330 outside-pair original codewords occur among the checked parent nodes. -/
theorem golayOutsidePairOctad_nodes_cover (d : Fin 4096)
    (hd : d ∈ generatedFeasibleOctadsOutsideRootPair) :
    ∃ n : Fin 330, golayOutsidePairOctadNodeLabel n = d := by
  let e : Fin 330 ↪ Fin 4096 :=
    ⟨golayOutsidePairOctadNodeLabel, golayOutsidePairOctad_node_injective⟩
  let s := Finset.univ.map e
  have hs : s ⊆ generatedFeasibleOctadsOutsideRootPair := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := Finset.mem_map.mp hx
    exact golayOutsidePairOctad_node_member n
  have hc : generatedFeasibleOctadsOutsideRootPair.card ≤ s.card := by
    rw [generatedFeasibleOctadsOutsideRootPair_card]
    simp [s]
  have he := Finset.eq_of_subset_of_card_le hs hc
  have hx : d ∈ s := by rw [he]; exact hd
  obtain ⟨n, _, hn⟩ := Finset.mem_map.mp hx
  exact ⟨n, hn⟩

/-- Every actual outside-pair octad has a genuine original word transport to codeword3. -/
theorem golayOutsidePairOctad_to_prototype (d : Fin 4096)
    (hd : d ∈ generatedFeasibleOctadsOutsideRootPair) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 0 ∧ p.val 1 = 1 ∧
      golayPermute p.val (golayCodeLabelEquiv d).val =
        (golayOutsidePairOctadNodeCode 0).val := by
  obtain ⟨n, hn⟩ := golayOutsidePairOctad_nodes_cover d hd
  obtain ⟨p, hp0, hp1, hp⟩ := golayOutsidePairOctad_node_transport n
  refine ⟨p⁻¹, ?_, ?_, ?_⟩
  · exact p.val.symm_apply_eq.mpr hp0.symm
  · exact p.val.symm_apply_eq.mpr hp1.symm
  · have h := congrArg (golayPermute p.val⁻¹) hp
    rw [golayPermute_inv] at h
    rw [← hn]
    exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
