/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.RankBound

/-! Stored consumers and counterexamples for canonical reachable-state rank bounds. -/

namespace Batteries.UnionFind

private theorem empty_reachable : Reachable empty := Reachable.empty

private theorem find_of_root (u : UnionFind) (x : Fin u.size) (hx : u.parent x = x) :
    u.find x = ⟨u, x, rfl⟩ := by
  have ha : (u.find x).1.arr = u.arr := by
    apply Array.ext (find_size u x)
    intro i hi hi'
    rw [getElem_find u x i hi']
    simp only [Function.iterate_fixed hx, exists_const, rootD_eq_self.mpr hx]
    by_cases he : x.val = i
    · subst i
      rw [parent, parentD_eq x.isLt] at hx
      simp only [↓reduceIte]
      cases hn : u.arr[x.val] with
      | mk p r =>
        simp only [hn] at hx
        cases hx
        rfl
    · simp only [he, ↓reduceIte]
  have hs : (u.find x).1 = u := by
    generalize (u.find x).1 = v at ha ⊢
    cases v
    cases u
    cases ha
    rfl
  have hr := find_root_2 u x
  rw [rootD_eq_self.mpr hx] at hr
  generalize u.find x = result at hs hr ⊢
  obtain ⟨v, r⟩ := result
  dsimp only at hs hr
  subst v
  have he : r = ⟨x, rfl⟩ := Subtype.ext (Fin.ext hr)
  cases he
  rfl

private theorem arr_union_of_roots (u : UnionFind) (x y : Fin u.size)
    (hx : u.parent x = x) (hy : u.parent y = y) :
    (u.union x y).arr = (u.link x y hy).arr := by
  simp only [union, arr_link]
  rw [find_of_root u x hx]
  dsimp only
  rw [find_of_root u y hy]

private def s2 : UnionFind := empty.push.push.union ⟨0, by decide⟩ ⟨1, by decide⟩

private theorem s2_reachable : Reachable s2 :=
  (empty_reachable.push.push).union _ _

private theorem s2_arr : s2.arr = #[⟨1, 0⟩, ⟨1, 1⟩] := by
  rw [s2, arr_union_of_roots _ _ _ (by simp) (by simp)]
  rfl

private theorem s2_parent (i : Nat) : s2.parent i = if i = 0 then 1 else i := by
  simp only [parent, parentD, s2_arr]
  split <;> rename_i h
  · change i < 2 at h
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> rfl
  · have hi : i ≠ 0 := by intro hi; subst i; exact h (by decide)
    simp [hi]

private theorem s2_root_zero : s2.rootD 0 = 1 := by
  rw [← rootD_parent s2 0, s2_parent]
  exact rootD_eq_self.mpr (by simp [s2_parent])

private theorem s2_rank : s2.rank 1 = 1 := by simp [rank, rankD, s2_arr]

private theorem s2_log : Nat.log2 s2.size = 1 := by rw [size, s2_arr]; decide

private theorem s2_tight : s2.rank (s2.rootD 0) ≤ Nat.log2 s2.size ∧
    s2.rank (s2.rootD 0) = Nat.log2 s2.size := by
  refine ⟨s2_reachable.rank_rootD_le_log2 (by rw [size, s2_arr]; decide), ?_⟩
  rw [s2_root_zero, s2_rank, s2_log]

private def four01 : UnionFind :=
  empty.push.push.push.push.union ⟨0, by decide⟩ ⟨1, by decide⟩

private theorem four01_arr : four01.arr = #[⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨3, 0⟩] := by
  rw [four01, arr_union_of_roots _ _ _ (by simp) (by simp)]
  rfl

private def fourPairs : UnionFind :=
  four01.union ⟨2, by rw [size, four01_arr]; decide⟩
    ⟨3, by rw [size, four01_arr]; decide⟩

private theorem fourPairs_arr : fourPairs.arr = #[⟨1, 0⟩, ⟨1, 1⟩, ⟨3, 0⟩, ⟨3, 1⟩] := by
  rw [fourPairs, arr_union_of_roots _ _ _
    (by simp [parent, parentD, four01_arr]) (by simp [parent, parentD, four01_arr])]
  simp [arr_link, linkAux, four01_arr]

private def s4 : UnionFind :=
  fourPairs.union ⟨1, by rw [size, fourPairs_arr]; decide⟩
    ⟨3, by rw [size, fourPairs_arr]; decide⟩

private theorem s4_reachable : Reachable s4 :=
  (((empty_reachable.push.push.push.push).union _ _).union _ _).union _ _

private theorem s4_arr : s4.arr = #[⟨1, 0⟩, ⟨3, 1⟩, ⟨3, 0⟩, ⟨3, 2⟩] := by
  rw [s4, arr_union_of_roots _ _ _
    (by simp [parent, parentD, fourPairs_arr]) (by simp [parent, parentD, fourPairs_arr])]
  simp [arr_link, linkAux, fourPairs_arr]

private theorem s4_size : s4.size = 4 := by rw [size, s4_arr]; rfl

private theorem s4_parent (i : Nat) :
    s4.parent i = if i < 4 then if i = 0 then 1 else 3 else i := by
  simp only [parent, parentD, s4_arr]
  split <;> rename_i h
  · change i < 4 at h
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;> rfl
  · change ¬i < 4 at h
    simp [h]

private theorem s4_root (i : Nat) (hi : i < 4) : s4.rootD i = 3 := by
  have h3 : s4.rootD 3 = 3 := rootD_eq_self.mpr (by simp [s4_parent])
  have h1 : s4.rootD 1 = 3 := by
    rw [← rootD_parent s4 1, s4_parent]
    exact h3
  rw [← rootD_parent s4 i, s4_parent]
  simp only [hi, ↓reduceIte]
  split
  · exact h1
  · exact h3

private theorem s4_rank : s4.rank 3 = 2 := by simp [rank, rankD, s4_arr]

private theorem s4_log : Nat.log2 s4.size = 2 := by rw [s4_size]; decide

private theorem s4_tight_rank : s4.rank (s4.rootD 0) ≤ Nat.log2 s4.size ∧
    s4.rank (s4.rootD 0) = Nat.log2 s4.size := by
  refine ⟨s4_reachable.rank_rootD_le_log2 (by rw [s4_size]; decide), ?_⟩
  rw [s4_root 0 (by decide), s4_rank, s4_log]

private theorem s4_first_depth : s4.parent^[2] 0 = s4.rootD 0 ∧
    ∀ k < 2, s4.parent^[k] 0 ≠ s4.rootD 0 := by
  constructor
  · change s4.parent (s4.parent 0) = s4.rootD 0
    simp [s4_parent, s4_root]
  · intro k hk
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with rfl | rfl <;> simp [s4_parent, s4_root]

private theorem s4_tight_depth :
    ∃ d, s4.parent^[d] 0 = s4.rootD 0 ∧ (∀ k < d, s4.parent^[k] 0 ≠ s4.rootD 0) ∧
      d = Nat.log2 s4.size := by
  obtain ⟨d, hd, hf, hb⟩ := s4_reachable.exists_first_iterate_rootD_le_log2
    ⟨0, by rw [s4_size]; decide⟩
  refine ⟨d, hd, hf, ?_⟩
  rw [s4_log] at hb ⊢
  by_contra hne
  exact s4_first_depth.2 d (by omega) hd

private def compressed : UnionFind := (s4.find ⟨0, by rw [s4_size]; decide⟩).1

private theorem compressed_size : compressed.size = 4 := by
  simp [compressed, s4_size]

private theorem compressed_reachable : Reachable compressed := s4_reachable.find _

private theorem compressed_parent (i : Nat) (hi : i < 4) : compressed.parent i = 3 := by
  classical
  rw [compressed, find_parent_eq_ite_iterate, s4_root 0 (by decide)]
  split
  · rfl
  · rename_i h
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact h ⟨0, rfl⟩
    simp [s4_parent, hi, hi0]

private theorem compressed_rank : compressed.rank 1 = 1 := by
  have hi : 1 < compressed.size := by rw [compressed_size]; decide
  rw [rank, rankD_eq hi]
  dsimp only [compressed] at hi ⊢
  rw [getElem_find]
  · simp [s4_arr]
  · rw [s4_size]
    decide

open Classical in
private noncomputable def descendants (u : UnionFind) (v : Nat) : Finset Nat :=
  (Finset.range u.size).filter fun i ↦ ∃ k, u.parent^[k] i = v

private theorem compressed_descendants : descendants compressed 1 = {1} := by
  classical
  ext i
  simp only [descendants, Finset.mem_filter, Finset.mem_range, compressed_size,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hi, k, hk⟩
    cases k with
    | zero => exact hk
    | succ k =>
      rw [Function.iterate_succ_apply, compressed_parent i hi,
        Function.iterate_fixed (compressed_parent 3 (by decide))] at hk
      contradiction
  · rintro rfl
    exact ⟨by decide, 0, rfl⟩

private theorem per_node_bound_false : Reachable compressed ∧ compressed.rank 1 = 1 ∧
    (descendants compressed 1).card = 1 ∧
    (descendants compressed 1).card < 2 ^ compressed.rank 1 := by
  simp [compressed_reachable, compressed_rank, compressed_descendants]

private def triple01 : UnionFind :=
  empty.push.push.push.union ⟨0, by decide⟩ ⟨1, by decide⟩

private theorem triple01_arr : triple01.arr = #[⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩] := by
  rw [triple01, arr_union_of_roots _ _ _ (by simp) (by simp)]
  rfl

private def badLink : UnionFind :=
  triple01.link ⟨0, by rw [size, triple01_arr]; decide⟩
    ⟨2, by rw [size, triple01_arr]; decide⟩ (by simp [parent, parentD, triple01_arr])

private theorem badLink_arr : badLink.arr = #[⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by
  simp [badLink, arr_link, linkAux, triple01_arr]

private theorem badLink_roots :
    badLink.rootD 0 = 2 ∧ badLink.rootD 1 = 1 ∧ badLink.rootD 2 = 2 := by
  have h2 : badLink.rootD 2 = 2 := rootD_eq_self.mpr (by
    simp [parent, parentD, badLink_arr])
  refine ⟨?_, rootD_eq_self.mpr (by simp [parent, parentD, badLink_arr]), h2⟩
  rw [← rootD_parent badLink 0]
  simpa [parent, parentD, badLink_arr] using h2

private theorem badLink_component : badLink.component 1 = {1} := by
  ext i
  simp only [mem_component, Finset.mem_singleton, size, badLink_arr]
  constructor
  · rintro ⟨hi, hr⟩
    change i < 3 at hi
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h with rfl | rfl | rfl
    · rw [badLink_roots.1] at hr
      contradiction
    · rfl
    · rw [badLink_roots.2.2] at hr
      contradiction
  · rintro rfl
    exact ⟨by decide, badLink_roots.2.1⟩

private theorem raw_link_source : Reachable triple01 ∧ triple01.parent 0 ≠ 0 := by
  exact ⟨(empty_reachable.push.push.push).union _ _,
    by simp [parent, parentD, triple01_arr]⟩

private theorem badLink_facts : badLink.parent 1 = 1 ∧ badLink.rank 1 = 1 ∧
    (badLink.component 1).card = 1 := by
  simp [parent, parentD, rank, rankD, badLink_arr, badLink_component]

private theorem raw_link_not_reachable : ¬ Reachable badLink := by
  intro h
  have hb := h.two_pow_rank_le_card_component (r := 1)
    (by rw [size, badLink_arr]; decide) badLink_facts.1
  rw [badLink_facts.2.1, badLink_facts.2.2] at hb
  contradiction

private def inflated : UnionFind where
  arr := #[⟨0, 5⟩]
  parentD_lt := by
    intro i hi
    have hz : i = 0 := by change i < 1 at hi; omega
    subst i
    decide
  rankD_lt := by
    intro i h
    have hi := lt_of_parentD h
    have hz : i = 0 := by change i < 1 at hi; omega
    subst i
    exact (h rfl).elim

private theorem inflated_component : inflated.component 0 = {0} := by
  ext i
  simp only [mem_component, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, _⟩
    change i < 1 at hi
    omega
  · rintro rfl
    exact ⟨by decide, rootD_eq_self.mpr rfl⟩

private theorem bare_structure_not_reachable : inflated.rank 0 = 5 ∧ ¬ Reachable inflated := by
  refine ⟨rfl, ?_⟩
  intro h
  have hb := h.two_pow_rank_le_card_component (r := 0) (by decide) rfl
  rw [inflated_component] at hb
  change 32 ≤ 1 at hb
  contradiction

private theorem range_guard_required : ∃ u r, Reachable u ∧ u.parent r = r ∧
    ¬ 2 ^ u.rank r ≤ (u.component r).card := by
  refine ⟨empty, 0, empty_reachable, rfl, ?_⟩
  simp [component, size]

private theorem singleton_boundary : Reachable empty.push ∧ empty.push.rank 0 = 0 ∧
    Nat.log2 empty.push.size = 0 ∧
    empty.push.rank (empty.push.rootD 0) ≤ Nat.log2 empty.push.size := by
  exact ⟨empty_reachable.push, rfl, rfl,
    empty_reachable.push.rank_rootD_le_log2 (by decide)⟩

private theorem empty_rank_bound (x : Nat) (hx : x < empty.size) :
    empty.rank (empty.rootD x) ≤ Nat.log2 empty.size :=
  empty_reachable.rank_rootD_le_log2 hx

private theorem same_component_rank (i : Nat) :
    (s4.union ⟨0, by rw [s4_size]; decide⟩ ⟨2, by rw [s4_size]; decide⟩).rank i =
      s4.rank i := by
  rw [rank_union]
  simp [s4_root]

private def unequalUnion : UnionFind :=
  triple01.union ⟨1, by rw [size, triple01_arr]; decide⟩
    ⟨2, by rw [size, triple01_arr]; decide⟩

private theorem unequalUnion_arr : unequalUnion.arr = #[⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩] := by
  rw [unequalUnion, arr_union_of_roots _ _ _
    (by simp [parent, parentD, triple01_arr]) (by simp [parent, parentD, triple01_arr])]
  simp [arr_link, linkAux, triple01_arr]

private theorem unequal_rank_bound : unequalUnion.rank 1 = 1 ∧
    2 ^ unequalUnion.rank 1 ≤ (unequalUnion.component 1).card := by
  refine ⟨by simp [rank, rankD, unequalUnion_arr], ?_⟩
  have hu : Reachable unequalUnion := raw_link_source.1.union _ _
  exact hu.two_pow_rank_le_card_component
    (by rw [size, unequalUnion_arr]; decide)
    (by simp [parent, parentD, unequalUnion_arr])

end Batteries.UnionFind
