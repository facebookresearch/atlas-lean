/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentRegroup

/-! # Regrouping octad terms by octad, kernel-friendly

`ShortData.ofListI` groups the octad terms of a flat list into one block per octad by inserting
each term into the block of its octad (structural recursion only; the kernel evaluates it in
`O(terms × octads)` steps, unlike the well-founded `List.mergeSort` of `ShortData.ofListG`).  The
short block (`shortVec_ofListI`) and the range conditions (`ofListI_ok`) are kept. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Insert the octad term `(e, c)` of octad `o` into the block of `o`. -/
def insertOct (o e : ℕ) (c : ℤ) : List (ℕ × List (ℕ × ℤ)) → List (ℕ × List (ℕ × ℤ))
  | [] => [(o, [(e, c)])]
  | b :: bs => if b.1 = o then (b.1, (e, c) :: b.2) :: bs else b :: insertOct o e c bs

/-- Group octad terms by octad. -/
def groupOctI : List (ℕ × ℤ) → List (ℕ × List (ℕ × ℤ))
  | [] => []
  | p :: L => insertOct ((p.1 - 552) / 64) ((p.1 - 552) % 64) p.2 (groupOctI L)

/-- Insertion adds one flat term up to order. -/
theorem octsFlat_insertOct (o e : ℕ) (c : ℤ) : ∀ bs : List (ℕ × List (ℕ × ℤ)),
    (octsFlat (insertOct o e c bs)).Perm ((552 + 64 * o + e, c) :: octsFlat bs)
  | [] => by simp [insertOct, octsFlat, octFlat]
  | b :: bs => by
    rw [insertOct]
    split_ifs with hb
    · simp only [octsFlat, octFlat, List.map_cons, List.cons_append]
      rw [hb]
    · simp only [octsFlat]
      exact ((octsFlat_insertOct o e c bs).append_left (octFlat b.1 b.2)).trans List.perm_middle

/-- Grouping keeps the flat octad terms up to order. -/
theorem octsFlat_groupOctI : ∀ L : List (ℕ × ℤ), (∀ p ∈ L, 552 ≤ p.1) →
    (octsFlat (groupOctI L)).Perm L
  | [], _ => by simp [groupOctI, octsFlat]
  | p :: L, h => by
    have ih := octsFlat_groupOctI L (fun q hq => h q (by simp [hq]))
    have hp := octLabel_split p.1 (h p (by simp))
    rw [groupOctI]
    refine (octsFlat_insertOct _ _ _ _).trans ?_
    rw [hp]
    exact ih.cons _

/-- Insertion keeps valid blocks. -/
theorem insertOct_ok (o e : ℕ) (c : ℤ) (ho : o < 759) (he : e < 64) :
    ∀ bs : List (ℕ × List (ℕ × ℤ)), (∀ b ∈ bs, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64) →
      ∀ b ∈ insertOct o e c bs, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64
  | [], _ => by
    intro b hb
    simp only [insertOct, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact ⟨ho, fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rw [hq]; exact he⟩
  | b0 :: bs, h => by
    intro b hb
    rw [insertOct] at hb
    split_ifs at hb with h0
    · simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · refine ⟨(h b0 (by simp)).1, fun q hq => ?_⟩
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact he
        · exact (h b0 (by simp)).2 q hq
      · exact h b (by simp [hb])
    · simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact h _ (by simp)
      · exact insertOct_ok o e c ho he bs (fun b' hb' => h b' (by simp [hb'])) b hb

/-- Grouped blocks are valid. -/
theorem groupOctI_ok : ∀ L : List (ℕ × ℤ), (∀ p ∈ L, 552 ≤ p.1 ∧ p.1 < 49128) →
    ∀ b ∈ groupOctI L, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64
  | [], _ => by simp [groupOctI]
  | p :: L, h => by
    have hp := h p (by simp)
    rw [groupOctI]
    exact insertOct_ok _ _ _ (by omega) (Nat.mod_lt _ (by norm_num)) _
      (groupOctI_ok L (fun q hq => h q (by simp [hq])))

/-- Regroup a flat list by kind, with one block per octad. -/
def ShortData.ofListI (T : List (ℕ × ℤ)) : ShortData :=
  ⟨T.filter (fun p => decide (p.1 < 552)),
    groupOctI (T.filter (fun p => decide (552 ≤ p.1) && decide (p.1 < 49128))),
    T.filter (fun p => decide (49128 ≤ p.1))⟩

/-- Grouping by insertion keeps the short block. -/
theorem shortVec_ofListI (T : List (ℕ × ℤ)) :
    shortVec (ShortData.ofListI T).flat = shortVec T := by
  rw [← shortVec_ofList T]
  unfold ShortData.flat ShortData.ofListI ShortData.ofList
  simp only
  rw [octsFlat_singletons _ (fun p hp => by
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact hp.2.1), shortVec_append, shortVec_append, shortVec_append, shortVec_append,
    shortVec_perm (octsFlat_groupOctI _ (fun p hp => by
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact hp.2.1))]

/-- Lists grouped by insertion with labels below `98280` are valid short data. -/
theorem ofListI_ok (T : List (ℕ × ℤ)) (hT : T.all (fun p => decide (p.1 < 98280)) = true) :
    (ShortData.ofListI T).ok = true := by
  have h0 := ofList_ok T hT
  simp only [ShortData.ok, ShortData.ofList, Bool.and_eq_true, List.all_eq_true] at h0
  simp only [ShortData.ok, ShortData.ofListI, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨h0.1.1, fun b hb => ?_⟩, h0.2⟩
  obtain ⟨hb1, hb2⟩ := groupOctI_ok _ (fun p hp => by
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.2) b hb
  simp only [decide_eq_true_eq]
  exact ⟨hb1, fun q hq => by simpa using hb2 q hq⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
