/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Mathlib
import Code.Universality.HexZConvClose
import Code.Universality.HexSurgerySeams
import Code.Universality.HexHalfEdgeClose

namespace StatMech.Universality

open HexWalk





noncomputable def hlc_sawCount (a : ℂ) (h0 : ℤ) (n : ℕ) : ℕ :=
  hzc_sawCount a h0 (n + 1)



noncomputable def hlc_sawCountR (a : ℂ) (h0 : ℤ) (n : ℕ) : ℝ :=
  (hlc_sawCount a h0 n : ℝ)




theorem hlc_sawCount_zero (a : ℂ) (h0 : ℤ) : hlc_sawCount a h0 0 = 1 := by
  classical
  unfold hlc_sawCount hzc_sawCount
  have hfiber :
      (hzc_truncFinset a h0 (0 + 1 + 1)).filter
          (fun ts => (ofTurns a h0 ts).numVertices = 0 + 1) = {[]} := by
    ext ts
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hlen⟩
      have hzero : ts.length = 0 := by
        simpa [numVertices] using hlen
      exact List.length_eq_zero_iff.mp hzero
    · rintro rfl
      refine ⟨hzc_nil_mem_truncFinset a h0 (by omega), ?_⟩
      rfl
  rw [hfiber, Finset.card_singleton]

@[simp]
theorem hlc_sawCountR_zero (a : ℂ) (h0 : ℤ) : hlc_sawCountR a h0 0 = 1 := by
  simp [hlc_sawCountR, hlc_sawCount_zero]





def hlc_zigzagTurnsAux : Bool → ℕ → List ℤ
  | _, 0 => []
  | false, n + 1 => -1 :: hlc_zigzagTurnsAux true n
  | true, n + 1 => 1 :: hlc_zigzagTurnsAux false n


def hlc_zigzagTurns (n : ℕ) : List ℤ := hlc_zigzagTurnsAux false n

@[simp]
theorem hlc_length_zigzagTurnsAux (phase : Bool) (n : ℕ) :
    (hlc_zigzagTurnsAux phase n).length = n := by
  induction n generalizing phase with
  | zero => cases phase <;> rfl
  | succ n ih => cases phase <;> simp [hlc_zigzagTurnsAux, ih]

@[simp]
theorem hlc_length_zigzagTurns (n : ℕ) : (hlc_zigzagTurns n).length = n := by
  simp [hlc_zigzagTurns]


theorem hlc_zigzagTurns_legal (phase : Bool) (n : ℕ) :
    ∀ t ∈ hlc_zigzagTurnsAux phase n, t = 1 ∨ t = -1 := by
  induction n generalizing phase with
  | zero => cases phase <;> simp [hlc_zigzagTurnsAux]
  | succ n ih =>
      cases phase with
      | false =>
          intro t ht
          simp only [hlc_zigzagTurnsAux, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact Or.inr rfl
          · exact ih true t ht
      | true =>
          intro t ht
          simp only [hlc_zigzagTurnsAux, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact Or.inl rfl
          · exact ih false t ht


theorem hlc_halfStep_zero_re_pos : 0 < (halfStep 0).re := by
  rw [hexWall3_halfStep_re]
  rw [show Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 by norm_num,
    Real.cos_pi_div_six]
  positivity

theorem hlc_halfStep_neg_one_re_pos : 0 < (halfStep (-1)).re := by
  rw [hexWall3_halfStep_re]
  rw [show Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) by
      push_cast; ring,
    Real.cos_neg, Real.cos_pi_div_six]
  positivity



private theorem hlc_isChain_cons_verticesAux (x m : ℂ) (h : ℤ) (ts : List ℤ)
    (hstep : x.re < (m + halfStep h).re)
    (htail : List.IsChain (fun z w : ℂ => z.re < w.re) (verticesAux m h ts)) :
    List.IsChain (fun z w : ℂ => z.re < w.re) (x :: verticesAux m h ts) := by
  cases ts with
  | nil => exact .cons_cons hstep htail
  | cons t ts => exact .cons_cons hstep htail



theorem hlc_zigzag_vertices_chain (n : ℕ) :
    (∀ m : ℂ, List.IsChain (fun z w : ℂ => z.re < w.re)
      (verticesAux m 0 (hlc_zigzagTurnsAux false n))) ∧
    (∀ m : ℂ, List.IsChain (fun z w : ℂ => z.re < w.re)
      (verticesAux m (-1) (hlc_zigzagTurnsAux true n))) := by
  induction n with
  | zero =>
      constructor <;> intro m <;> exact .singleton _
  | succ n ih =>
      constructor
      · intro m
        rw [show hlc_zigzagTurnsAux false (n + 1) =
            -1 :: hlc_zigzagTurnsAux true n by rfl, verticesAux_cons]
        apply hlc_isChain_cons_verticesAux
        · simp only [Complex.add_re]
          have hp := hlc_halfStep_neg_one_re_pos
          norm_num at hp ⊢
          linarith
        · simpa using ih.2 (m + halfStep 0 + halfStep (0 + (-1)))
      · intro m
        rw [show hlc_zigzagTurnsAux true (n + 1) =
            1 :: hlc_zigzagTurnsAux false n by rfl, verticesAux_cons]
        apply hlc_isChain_cons_verticesAux
        · simp only [Complex.add_re]
          have hp := hlc_halfStep_zero_re_pos
          norm_num at hp ⊢
          linarith
        · simpa using ih.1 (m + halfStep (-1) + halfStep (-1 + 1))



theorem hlc_zigzag_isLegalSAW_zero (a : ℂ) (n : ℕ) :
    (ofTurns a 0 (hlc_zigzagTurns n)).IsLegalSAW := by
  constructor
  · simpa [LegalTurns, hlc_zigzagTurns] using hlc_zigzagTurns_legal false n
  · unfold IsSAW vertices ofTurns
    have hchain := (hlc_zigzag_vertices_chain n).1 a
    exact hchain.pairwise.imp
      (fun hlt heq => (ne_of_lt hlt) (congrArg Complex.re heq))



theorem hlc_zigzag_isLegalSAW (a : ℂ) (h0 : ℤ) (n : ℕ) :
    (ofTurns a h0 (hlc_zigzagTurns n)).IsLegalSAW := by
  exact (hhe_isLegalSAW_rebase a a 0 h0 (hlc_zigzagTurns n)).mpr
    (hlc_zigzag_isLegalSAW_zero a n)


theorem hlc_one_le_sawCount (a : ℂ) (h0 : ℤ) (n : ℕ) :
    1 ≤ hlc_sawCount a h0 n := by
  classical
  unfold hlc_sawCount hzc_sawCount
  apply Finset.one_le_card.mpr
  refine ⟨hlc_zigzagTurns n, ?_⟩
  simp only [Finset.mem_filter]
  constructor
  · rw [hzc_mem_truncFinset]
    refine ⟨hlc_zigzag_isLegalSAW a h0 n, ?_⟩
    simp [numVertices]
  · simp [numVertices]

theorem hlc_one_le_sawCountR (a : ℂ) (h0 : ℤ) (n : ℕ) :
    1 ≤ hlc_sawCountR a h0 n := by
  unfold hlc_sawCountR
  exact_mod_cast hlc_one_le_sawCount a h0 n




noncomputable def hlc_sawFinset (a : ℂ) (h0 : ℤ) (n : ℕ) : Finset (List ℤ) :=
  (hzc_truncFinset a h0 (n + 2)).filter
    (fun ts => (ofTurns a h0 ts).numVertices = n + 1)

@[simp]
theorem hlc_card_sawFinset (a : ℂ) (h0 : ℤ) (n : ℕ) :
    (hlc_sawFinset a h0 n).card = hlc_sawCount a h0 n := by
  unfold hlc_sawFinset hlc_sawCount
  exact hzc_filterCard_eq a h0 (n + 2) (n + 1) (by omega)


theorem hlc_mem_sawFinset (a : ℂ) (h0 : ℤ) (n : ℕ) (ts : List ℤ) :
    ts ∈ hlc_sawFinset a h0 n ↔
      (ofTurns a h0 ts).IsLegalSAW ∧ ts.length = n := by
  simp only [hlc_sawFinset, Finset.mem_filter, hzc_mem_truncFinset]
  constructor
  · rintro ⟨⟨hleg, _⟩, hnum⟩
    refine ⟨hleg, ?_⟩
    simpa [numVertices] using hnum
  · rintro ⟨hleg, hlen⟩
    refine ⟨⟨hleg, ?_⟩, ?_⟩ <;> simp [numVertices, hlen]




theorem hlc_split_mem (a : ℂ) (h0 : ℤ) (m n : ℕ) {ts : List ℤ}
    (hts : ts ∈ hlc_sawFinset a h0 (m + n)) :
    (ts.take m, ts.drop m) ∈
      hlc_sawFinset a h0 m ×ˢ hlc_sawFinset a h0 n := by
  rw [Finset.mem_product]
  have hdata := (hlc_mem_sawFinset a h0 (m + n) ts).mp hts
  have hcp : m ≤ ts.length := by omega
  constructor
  · rw [hlc_mem_sawFinset]
    exact ⟨hexCut_legal_take a h0 ts m hdata.1, by simp [hdata.2]⟩
  · rw [hlc_mem_sawFinset]
    refine ⟨?_, by simp [List.length_drop, hdata.2]⟩
    have hdrop := hexCut_legal_drop a h0 ts m hcp hdata.1
    exact (hhe_isLegalSAW_rebase a (hexDropMid a h0 ts m) h0
      (h0 + (ts.take m).sum) (ts.drop m)).mp hdrop


theorem hlc_split_injective (m : ℕ) :
    Function.Injective (fun ts : List ℤ => (ts.take m, ts.drop m)) := by
  intro s t h
  have htake : s.take m = t.take m := congrArg Prod.fst h
  have hdrop : s.drop m = t.drop m := congrArg Prod.snd h
  calc
    s = s.take m ++ s.drop m := (List.take_append_drop m s).symm
    _ = t.take m ++ t.drop m := by rw [htake, hdrop]
    _ = t := List.take_append_drop m t


theorem hlc_sawCount_submult (a : ℂ) (h0 : ℤ) (m n : ℕ) :
    hlc_sawCount a h0 (m + n) ≤ hlc_sawCount a h0 m * hlc_sawCount a h0 n := by
  classical
  rw [← hlc_card_sawFinset a h0 (m + n), ← hlc_card_sawFinset a h0 m,
    ← hlc_card_sawFinset a h0 n, ← Finset.card_product]
  exact Finset.card_le_card_of_injOn
    (fun ts => (ts.take m, ts.drop m))
    (fun _ hts => hlc_split_mem a h0 m n hts)
    (fun _ _ _ _ h => hlc_split_injective m h)



theorem hlc_sawCountR_submultiplicative (a : ℂ) (h0 : ℤ) :
    Submultiplicative (hlc_sawCountR a h0) := by
  intro m n
  unfold hlc_sawCountR
  exact_mod_cast hlc_sawCount_submult a h0 m n





theorem hlc_sawFinset_rebase (a a' : ℂ) (h0 h0' : ℤ) (n : ℕ) :
    hlc_sawFinset a' h0' n = hlc_sawFinset a h0 n := by
  ext ts
  rw [hlc_mem_sawFinset, hlc_mem_sawFinset]
  exact and_congr (hhe_isLegalSAW_rebase a a' h0 h0' ts) Iff.rfl



theorem hlc_sawCount_rebase (a a' : ℂ) (h0 h0' : ℤ) (n : ℕ) :
    hlc_sawCount a' h0' n = hlc_sawCount a h0 n := by
  rw [← hlc_card_sawFinset, ← hlc_card_sawFinset,
    hlc_sawFinset_rebase a a' h0 h0' n]


theorem hlc_sawCountR_rebase (a a' : ℂ) (h0 h0' : ℤ) (n : ℕ) :
    hlc_sawCountR a' h0' n = hlc_sawCountR a h0 n := by
  simp only [hlc_sawCountR, hlc_sawCount_rebase a a' h0 h0' n]

end StatMech.Universality
