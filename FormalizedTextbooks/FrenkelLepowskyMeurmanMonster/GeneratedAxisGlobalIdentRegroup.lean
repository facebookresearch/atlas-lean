/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord

/-! # Regrouping octad terms by octad

`ShortData.ofList` puts every octad term of a transported list in its own block; the octad part
of the triality pairing then scans all blocks for every term of the other vector.
`ShortData.ofListG` sorts the octad terms by label and groups consecutive terms of the same
octad into one block (`groupOct`), keeping the short block (`shortVec_ofListG`) and the range
conditions (`ofListG_ok`).  `IdentVec.real_short_congr` exchanges equal short blocks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Group consecutive octad terms of the same octad into blocks. -/
def groupOct : List (ℕ × ℤ) → List (ℕ × List (ℕ × ℤ))
  | [] => []
  | p :: L =>
    match groupOct L with
    | [] => [((p.1 - 552) / 64, [((p.1 - 552) % 64, p.2)])]
    | b :: bs => if b.1 = (p.1 - 552) / 64 then (b.1, ((p.1 - 552) % 64, p.2) :: b.2) :: bs
        else ((p.1 - 552) / 64, [((p.1 - 552) % 64, p.2)]) :: b :: bs

/-- An octad label is recovered from its octad and sign label. -/
theorem octLabel_split (l : ℕ) (h : 552 ≤ l) : 552 + 64 * ((l - 552) / 64) + (l - 552) % 64 = l := by
  have := Nat.div_add_mod (l - 552) 64
  omega

/-- Grouping keeps the flat octad terms. -/
theorem octsFlat_groupOct : ∀ L : List (ℕ × ℤ), (∀ p ∈ L, 552 ≤ p.1) → octsFlat (groupOct L) = L
  | [], _ => rfl
  | p :: L, h => by
    have ih := octsFlat_groupOct L (fun q hq => h q (by simp [hq]))
    have hp := octLabel_split p.1 (h p (by simp))
    rw [groupOct]
    split
    · next hg =>
      rw [hg] at ih
      simp only [octsFlat, octFlat, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [hp, ← ih]
      rfl
    · next b bs hg =>
      rw [hg] at ih
      split_ifs with hb
      · simp only [octsFlat, octFlat, List.map_cons, List.cons_append]
        rw [hb, hp]
        simp only [octsFlat, octFlat] at ih
        rw [← hb, ← ih]
      · simp only [octsFlat, octFlat, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append]
        rw [hp, ← ih]
        rfl

/-- Blocks of grouped octad terms have valid indices. -/
theorem groupOct_ok : ∀ L : List (ℕ × ℤ), (∀ p ∈ L, 552 ≤ p.1 ∧ p.1 < 49128) →
    ∀ b ∈ groupOct L, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64
  | [], _ => by simp [groupOct]
  | p :: L, h => by
    have ih := groupOct_ok L (fun q hq => h q (by simp [hq]))
    have hp := h p (by simp)
    have h1 : (p.1 - 552) / 64 < 759 := by omega
    have h2 : (p.1 - 552) % 64 < 64 := Nat.mod_lt _ (by norm_num)
    rw [groupOct]
    split
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact ⟨h1, fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rw [hq]; exact h2⟩
    · next b0 bs hg =>
      rw [hg] at ih
      split_ifs with hb
      · intro b hbm
        simp only [List.mem_cons] at hbm
        rcases hbm with rfl | hbm
        · refine ⟨(ih b0 (by simp)).1, fun q hq => ?_⟩
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact h2
          · exact (ih b0 (by simp)).2 q hq
        · exact ih b (by simp [hbm])
      · intro b hbm
        simp only [List.mem_cons] at hbm
        rcases hbm with rfl | hbm
        · exact ⟨h1, fun q hq => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rw [hq]; exact h2⟩
        · exact ih b (List.mem_cons.mpr hbm)

/-- The octad terms of a list, sorted by label. -/
def sortedOct (T : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (T.filter (fun p => decide (552 ≤ p.1) && decide (p.1 < 49128))).mergeSort
    (fun a b => decide (a.1 ≤ b.1))

/-- Regroup a flat list by kind, with one block per octad run in label order. -/
def ShortData.ofListG (T : List (ℕ × ℤ)) : ShortData :=
  ⟨T.filter (fun p => decide (p.1 < 552)), groupOct (sortedOct T),
    T.filter (fun p => decide (49128 ≤ p.1))⟩

/-- Sorted octad terms are octad terms. -/
theorem mem_sortedOct (T : List (ℕ × ℤ)) (p : ℕ × ℤ) (hp : p ∈ sortedOct T) :
    552 ≤ p.1 ∧ p.1 < 49128 := by
  rw [sortedOct, List.mem_mergeSort] at hp
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.2

/-- Short blocks are invariant under permutations. -/
theorem shortVec_perm {A B : List (ℕ × ℤ)} (h : A.Perm B) : shortVec A = shortVec B := by
  unfold shortVec
  exact (h.map _).sum_eq

/-- Grouped regrouping keeps the short block. -/
theorem shortVec_ofListG (T : List (ℕ × ℤ)) :
    shortVec (ShortData.ofListG T).flat = shortVec T := by
  rw [← shortVec_ofList T]
  unfold ShortData.flat ShortData.ofListG ShortData.ofList
  simp only
  rw [octsFlat_groupOct _ (fun p hp => (mem_sortedOct T p hp).1),
    octsFlat_singletons _ (fun p hp => by
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact hp.2.1), shortVec_append, shortVec_append, shortVec_append, shortVec_append]
  rw [sortedOct, shortVec_perm (List.mergeSort_perm _ _)]

/-- Grouped regrouped lists with labels below `98280` are valid short data. -/
theorem ofListG_ok (T : List (ℕ × ℤ)) (hT : T.all (fun p => decide (p.1 < 98280)) = true) :
    (ShortData.ofListG T).ok = true := by
  have h0 := ofList_ok T hT
  simp only [ShortData.ok, ShortData.ofList, Bool.and_eq_true, List.all_eq_true] at h0
  simp only [ShortData.ok, ShortData.ofListG, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨h0.1.1, fun b hb => ?_⟩, h0.2⟩
  obtain ⟨hb1, hb2⟩ := groupOct_ok (sortedOct T) (fun p hp => mem_sortedOct T p hp) b hb
  simp only [decide_eq_true_eq]
  exact ⟨hb1, fun q hq => by simpa using hb2 q hq⟩

/-- Representations with equal short blocks have equal coordinates. -/
theorem IdentVec.real_short_congr (M : MatRep) (S1 S2 : ShortData) (d : ℚ)
    (T : GeneratedAxisGlobalRationalTensor) (h : shortVec S1.flat = shortVec S2.flat) :
    (⟨M, S1, d, T⟩ : IdentVec).real = (⟨M, S2, d, T⟩ : IdentVec).real := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  rw [IdentVec.real_short, IdentVec.real_short]
  simp only [h]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
