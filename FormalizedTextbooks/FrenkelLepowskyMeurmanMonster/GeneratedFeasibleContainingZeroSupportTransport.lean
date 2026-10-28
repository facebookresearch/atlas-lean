/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroSupportData

/-! Genuine source-preserving support transport retaining both physical first coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The two support arrays are evaluated as genuine original Mathieu words. -/
def generatedFeasibleContainingZeroSupportLetter : Fin 2 → golayAutomorphismSubgroup :=
  ![golayStrongWord [19, 20, 27, 25, 5, 9, 4], golayStrongLetter 11]

private theorem strong_word_apply (w : List (Fin 28)) (i : Fin 24) :
    (golayStrongWord w).val i = golayStrongWordArray w i := by
  induction w generalizing i with
  | nil => rfl
  | cons t w ih =>
    change (golayStrongLetter t).val ((golayStrongWord w).val i) = _
    rw [golayOutsidePairOctad_strong_letter_apply, ih]
    rfl

/-- Exact coordinate binding of each actual source-preserving word. -/
theorem generatedFeasibleContainingZeroSupportLetter_apply (k : Fin 2) (i : Fin 24) :
    (generatedFeasibleContainingZeroSupportLetter k).val i =
      generatedFeasibleContainingZeroSupportLetterArray k i := by
  fin_cases k
  · exact strong_word_apply [19, 20, 27, 25, 5, 9, 4] i
  · exact golayOutsidePairOctad_strong_letter_apply 11 i

/-- Every genuine support word retains the entire source and both first coordinates. -/
theorem generatedFeasibleContainingZeroSupportLetter_flags (k : Fin 2) :
    (generatedFeasibleContainingZeroSupportLetter k).val 0 = 0 ∧
    (generatedFeasibleContainingZeroSupportLetter k).val 1 = 1 ∧
    ∀ i : Fin 24, ((generatedFeasibleContainingZeroSupportLetter k).val i).val < 8 ↔
      i.val < 8 := by
  simpa only [generatedFeasibleContainingZeroSupportLetter_apply] using
    generatedFeasibleContainingZeroSupportLetterArray_flags k

private theorem pair_node_transport (n : Fin 120) :
    ∃ p : golayAutomorphismSubgroup,
      p.val 0 = 0 ∧ p.val 1 = 1 ∧
      (∀ i : Fin 24, (p.val i).val < 8 ↔ i.val < 8) ∧
      ((p.val 8 = (generatedFeasibleContainingZeroPairNode n).1 ∧
          p.val 9 = (generatedFeasibleContainingZeroPairNode n).2) ∨
        (p.val 8 = (generatedFeasibleContainingZeroPairNode n).2 ∧
          p.val 9 = (generatedFeasibleContainingZeroPairNode n).1)) := by
  have all : ∀ m : ℕ, ∀ n : Fin 120, n.val = m →
      ∃ p : golayAutomorphismSubgroup,
        p.val 0 = 0 ∧ p.val 1 = 1 ∧
      (∀ i : Fin 24, (p.val i).val < 8 ↔ i.val < 8) ∧
        ((p.val 8 = (generatedFeasibleContainingZeroPairNode n).1 ∧
            p.val 9 = (generatedFeasibleContainingZeroPairNode n).2) ∨
          (p.val 8 = (generatedFeasibleContainingZeroPairNode n).2 ∧
            p.val 9 = (generatedFeasibleContainingZeroPairNode n).1)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n hm
      by_cases hn : n = 0
      · subst n
        exact ⟨1, rfl, rfl, fun _ => Iff.rfl, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨p, hp0fix, hp1fix, hpres, hp⟩ := ih _ (by
          rw [← hm]; exact generatedFeasibleContainingZeroPairParent_lt n hn)
          (generatedFeasibleContainingZeroPairParent n) rfl
        let q := generatedFeasibleContainingZeroSupportLetter (generatedFeasibleContainingZeroPairLetter n)
        obtain ⟨hq0, hq1, hqS⟩ := generatedFeasibleContainingZeroSupportLetter_flags
          (generatedFeasibleContainingZeroPairLetter n)
        refine ⟨q * p, ?_, ?_, fun i => (hqS (p.val i)).trans (hpres i), ?_⟩
        · change q.val (p.val 0) = 0
          rw [hp0fix]; exact hq0
        · change q.val (p.val 1) = 1
          rw [hp1fix]; exact hq1
        · have he := generatedFeasibleContainingZeroPair_edge n hn
          rcases hp with ⟨hp0, hp1⟩ | ⟨hp0, hp1⟩ <;>
          rcases he with ⟨he0, he1⟩ | ⟨he0, he1⟩
          · exact Or.inl ⟨(congrArg q.val hp0).trans
                ((generatedFeasibleContainingZeroSupportLetter_apply _ _).trans he0),
              (congrArg q.val hp1).trans
                  ((generatedFeasibleContainingZeroSupportLetter_apply _ _).trans he1)⟩
          · exact Or.inr ⟨(congrArg q.val hp0).trans
                ((generatedFeasibleContainingZeroSupportLetter_apply _ _).trans he0),
              (congrArg q.val hp1).trans
                  ((generatedFeasibleContainingZeroSupportLetter_apply _ _).trans he1)⟩
          · exact Or.inr ⟨(congrArg q.val hp0).trans
                ((generatedFeasibleContainingZeroSupportLetter_apply _ _).trans he1),
              (congrArg q.val hp1).trans
                  ((generatedFeasibleContainingZeroSupportLetter_apply _ _).trans he0)⟩
          · exact Or.inl ⟨(congrArg q.val hp0).trans
                ((generatedFeasibleContainingZeroSupportLetter_apply _ _).trans he1),
              (congrArg q.val hp1).trans
                  ((generatedFeasibleContainingZeroSupportLetter_apply _ _).trans he0)⟩
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

private theorem generatedFeasibleContaining_zero_octads_card :
    (generatedFeasibleContainingSelectedOutsideCodes 0).card = 30 := by
  simpa using generatedFeasibleContainingSelectedOutsideCodes_card 0

/-- Every original outside pair occurs at one of the120 certified node addresses. -/
theorem generatedFeasibleContainingZero_pairs_cover (v : Fin 24 × Fin 24)
    (hv : v ∈ generatedFeasibleContainingZeroPairs) :
    ∃ n : Fin 120, generatedFeasibleContainingZeroPairNode n = v :=
  nodes_cover _ _ generatedFeasibleContainingZeroPairNode_injective
    generatedFeasibleContainingZeroPairNode_mem generatedFeasibleContainingZeroPairs_card v hv

/-- Every original disjoint octad occurs at one of the30 certified node addresses. -/
theorem generatedFeasibleContainingZero_octads_cover (d : Fin 4096)
    (hd : d ∈ (generatedFeasibleContainingSelectedOutsideCodes 0)) :
    ∃ n : Fin 30, generatedFeasibleContainingZeroOctadNode n = d :=
  nodes_cover _ _ generatedFeasibleContainingZeroOctadNode_injective
    generatedFeasibleContainingZeroOctadNode_mem generatedFeasibleContaining_zero_octads_card d hd

/-- All actual outside unordered pairs have original words from the initial pair. -/
theorem generatedFeasibleContainingZero_pair_from_initial (v : Fin 24 × Fin 24)
    (hv : v ∈ generatedFeasibleContainingZeroPairs) :
    ∃ p : golayAutomorphismSubgroup,
      p.val 0 = 0 ∧ p.val 1 = 1 ∧
      (∀ i : Fin 24, (p.val i).val < 8 ↔ i.val < 8) ∧
      ((p.val 8 = v.1 ∧ p.val 9 = v.2) ∨ (p.val 8 = v.2 ∧ p.val 9 = v.1)) := by
  obtain ⟨n, hn⟩ := nodes_cover _ _ generatedFeasibleContainingZeroPairNode_injective
    generatedFeasibleContainingZeroPairNode_mem generatedFeasibleContainingZeroPairs_card v hv
  rw [← hn]
  exact pair_node_transport n

private theorem octad_edge_code (n : Fin 30) (hn : n ≠ 0) :
    golayPermute (generatedFeasibleContainingZeroSupportLetter (generatedFeasibleContainingZeroOctadLetter n)).val
      (golayCodeLabelEquiv
        (generatedFeasibleContainingZeroOctadNode (generatedFeasibleContainingZeroOctadParent n))).val =
      (golayCodeLabelEquiv (generatedFeasibleContainingZeroOctadNode n)).val := by
  funext j
  let p := generatedFeasibleContainingZeroSupportLetter (generatedFeasibleContainingZeroOctadLetter n)
  have hb := generatedFeasibleContainingZeroOctad_edge n hn (p.val.symm j)
  rw [← generatedFeasibleContainingZeroSupportLetter_apply, Equiv.apply_symm_apply] at hb
  apply ZMod.val_injective 2
  change (golayEncoder (golayLabelCoefficients
    (generatedFeasibleContainingZeroOctadNode (generatedFeasibleContainingZeroOctadParent n)))
      (p.val.symm j)).val =
    (golayEncoder (golayLabelCoefficients (generatedFeasibleContainingZeroOctadNode n)) j).val
  rw [golayLabelEncoder_match, golayLabelEncoder_match, hb]

private theorem octad_node_transport (n : Fin 30) :
    ∃ p : golayAutomorphismSubgroup,
      p.val 0 = 0 ∧ p.val 1 = 1 ∧
      (∀ i : Fin 24, (p.val i).val < 8 ↔ i.val < 8) ∧
      golayPermute p.val (golayCodeLabelEquiv 3).val =
        (golayCodeLabelEquiv (generatedFeasibleContainingZeroOctadNode n)).val := by
  have all : ∀ m : ℕ, ∀ n : Fin 30, n.val = m →
      ∃ p : golayAutomorphismSubgroup,
        p.val 0 = 0 ∧ p.val 1 = 1 ∧
      (∀ i : Fin 24, (p.val i).val < 8 ↔ i.val < 8) ∧
        golayPermute p.val (golayCodeLabelEquiv 3).val =
          (golayCodeLabelEquiv (generatedFeasibleContainingZeroOctadNode n)).val := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n hm
      by_cases hn : n = 0
      · subst n
        exact ⟨1, rfl, rfl, fun _ => Iff.rfl, golayPermute_one _⟩
      · obtain ⟨p, hp0fix, hp1fix, hpres, hp⟩ := ih _ (by
          rw [← hm]; exact generatedFeasibleContainingZeroOctadParent_lt n hn)
          (generatedFeasibleContainingZeroOctadParent n) rfl
        let q := generatedFeasibleContainingZeroSupportLetter (generatedFeasibleContainingZeroOctadLetter n)
        obtain ⟨hq0, hq1, hqS⟩ := generatedFeasibleContainingZeroSupportLetter_flags
          (generatedFeasibleContainingZeroOctadLetter n)
        refine ⟨q * p, ?_, ?_, fun i => (hqS (p.val i)).trans (hpres i), ?_⟩
        · change q.val (p.val 0) = 0
          rw [hp0fix]; exact hq0
        · change q.val (p.val 1) = 1
          rw [hp1fix]; exact hq1
        · change golayPermute (q.val * p.val) (golayCodeLabelEquiv 3).val = _
          rw [golayPermute_mul, hp]
          exact octad_edge_code n hn
  exact all n.val n rfl

/-- All actual disjoint octads have genuine section-preserving original word transport. -/
theorem generatedFeasibleContainingZero_octad_from_initial (d : Fin 4096)
    (hd : d ∈ (generatedFeasibleContainingSelectedOutsideCodes 0)) :
    ∃ p : golayAutomorphismSubgroup,
      p.val 0 = 0 ∧ p.val 1 = 1 ∧
      (∀ i : Fin 24, (p.val i).val < 8 ↔ i.val < 8) ∧
      golayPermute p.val (golayCodeLabelEquiv 3).val = (golayCodeLabelEquiv d).val := by
  obtain ⟨n, hn⟩ := nodes_cover _ _ generatedFeasibleContainingZeroOctadNode_injective
    generatedFeasibleContainingZeroOctadNode_mem generatedFeasibleContaining_zero_octads_card d hd
  rw [← hn]
  exact octad_node_transport n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
