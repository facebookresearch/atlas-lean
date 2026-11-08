/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPath

/-!
# HAMPATH, backward direction, part 1: clause detours are normal

`detoursNormal_of_isHamPath`: every Hamiltonian path of Sipser's graph `toHam φ` (Sipser,
Theorem 7.46) has normal detours (`DetoursNormal`): each clause vertex `j` sits between the two
vertices of its pair in one diamond row.

* The arcs (`mem_hamEdges`, `hamEdges_cases`): frame arcs, arcs between row neighbours, and
  clause detours. With `T = hpT m i`, `hpR m i l = T + 1 + l` and `hpT m (i + 1) = T + 3 m + 2`
  (`hpT_succ`); distinct diamonds are `3 m + 2` apart (`hpT_sep`), clause vertices lie below `m`.
  The in- and out-neighbours of a row vertex (`hamEdges_to_hpR`, `hamEdges_from_hpR`) are its
  row neighbours, the frame tops for a row end, and clause `j` for the pair `3 j + 1`, `3 j + 2`;
  those of clause `j` (`hamEdges_to_clause`, `hamEdges_from_clause`) are vertices of its pairs.
* Along a Hamiltonian path (`[u, v] <:+: p`: `v` comes right after `u`), consecutive vertices
  are joined by arcs (`hamEdges_of_infix`), and every vertex other than `s` has a predecessor
  and every vertex other than `t` a successor (`hamPath_exists_pred`, `hamPath_exists_succ`, and
  their row and clause forms). Both are unique, and they differ, since `p` has no duplicates.
* Sipser's separator argument (`hamPath_pair_false`): if clause `j` is entered from the pair
  vertex `a = hpR m i la` and left elsewhere than the other pair vertex `c = hpR m i lc`, then
  `c`, whose neighbours are `a`, `j` and a separator `d`, is forced to be entered from `d` and
  left to `a`. The separator on the other side of `a` then has a single free neighbour
  (`hamPath_separator_false`); a row end there is forced from the top to the next top, and the
  other row end has a single free neighbour (`hamPath_rowEnd_false`). Both contradictions come
  from one rule: a vertex whose only free predecessor and successor are one vertex `z`
  would close the cycle `z, v, z`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-! ### The vertex numbering -/

theorem le_hpT (m i : ℕ) : m ≤ hpT m i := Nat.le_add_right _ _

theorem hpT_zero (m : ℕ) : hpT m 0 = m := by simp [hpT]

theorem hpT_succ (m i : ℕ) : hpT m (i + 1) = hpT m i + (3 * m + 2) := by
  simp only [hpT, Nat.add_mul, Nat.one_mul]; omega

theorem hpT_add_le {m i i' : ℕ} (h : i < i') : hpT m i + (3 * m + 2) ≤ hpT m i' := by
  rw [← hpT_succ]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- Distinct diamonds are `3 m + 2` apart. -/
theorem hpT_sep {m i i' : ℕ} (h : i ≠ i') :
    hpT m i + (3 * m + 2) ≤ hpT m i' ∨ hpT m i' + (3 * m + 2) ≤ hpT m i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  exacts [Or.inl (hpT_add_le h), Or.inr (hpT_add_le h)]

/-! ### The arcs -/

/-- The arcs of `hamEdges φ`: in diamond `i` of the variable `x = (hamVars φ).getD i 0`, the frame,
the row, and the detours of the clauses containing `x` or its negation. -/
theorem mem_hamEdges {φ : CNF} {u v : ℕ} :
    (u, v) ∈ hamEdges φ ↔ ∃ i < (hamVars φ).length,
      ((u = hpT φ.length i ∧ v = hpR φ.length i 0 ∨
          u = hpT φ.length i ∧ v = hpR φ.length i (3 * φ.length) ∨
          u = hpR φ.length i 0 ∧ v = hpT φ.length (i + 1) ∨
          u = hpR φ.length i (3 * φ.length) ∧ v = hpT φ.length (i + 1)) ∨
        ∃ l < 3 * φ.length,
          u = hpR φ.length i l ∧ v = hpR φ.length i (l + 1) ∨
          u = hpR φ.length i (l + 1) ∧ v = hpR φ.length i l) ∨
      ∃ j < φ.length,
        ((hamVars φ).getD i 0, true) ∈ φ.getD j [] ∧
          (u = hpR φ.length i (3 * j + 1) ∧ v = j ∨ u = j ∧ v = hpR φ.length i (3 * j + 2)) ∨
        ((hamVars φ).getD i 0, false) ∈ φ.getD j [] ∧
          (u = hpR φ.length i (3 * j + 2) ∧ v = j ∨ u = j ∧ v = hpR φ.length i (3 * j + 1)) := by
  simp only [hamEdges, diamondEdges, List.mem_flatMap, List.mem_range, List.mem_append,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, List.mem_ite_nil_right]

/-- The arcs of `hamEdges φ`, forgetting which literal a detour comes from. -/
theorem hamEdges_cases {φ : CNF} {u v : ℕ} (h : (u, v) ∈ hamEdges φ) :
    ∃ i < (hamVars φ).length,
      (u = hpT φ.length i ∧ (v = hpR φ.length i 0 ∨ v = hpR φ.length i (3 * φ.length))) ∨
      ((u = hpR φ.length i 0 ∨ u = hpR φ.length i (3 * φ.length)) ∧
        v = hpT φ.length (i + 1)) ∨
      (∃ l < 3 * φ.length, u = hpR φ.length i l ∧ v = hpR φ.length i (l + 1) ∨
        u = hpR φ.length i (l + 1) ∧ v = hpR φ.length i l) ∨
      (∃ j < φ.length,
        (u = hpR φ.length i (3 * j + 1) ∨ u = hpR φ.length i (3 * j + 2)) ∧ v = j ∨
        u = j ∧ (v = hpR φ.length i (3 * j + 1) ∨ v = hpR φ.length i (3 * j + 2))) := by
  obtain ⟨i, hi, h⟩ := mem_hamEdges.1 h
  refine ⟨i, hi, ?_⟩
  rcases h with ((h | h | h | h) | ⟨l, hl, h⟩) | ⟨j, hj, ⟨-, h | h⟩ | ⟨-, h | h⟩⟩
  · exact Or.inl ⟨h.1, Or.inl h.2⟩
  · exact Or.inl ⟨h.1, Or.inr h.2⟩
  · exact Or.inr (Or.inl ⟨Or.inl h.1, h.2⟩)
  · exact Or.inr (Or.inl ⟨Or.inr h.1, h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨l, hl, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hj, Or.inl ⟨Or.inl h.1, h.2⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hj, Or.inr ⟨h.1, Or.inr h.2⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hj, Or.inl ⟨Or.inr h.1, h.2⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hj, Or.inr ⟨h.1, Or.inl h.2⟩⟩))

/-- The in-neighbours of the row vertex `hpR m i l`: its row neighbours, the top `hpT m i` if
it is a row end, and clause `v` if it is a vertex of the pair of `v`. -/
theorem hamEdges_to_hpR {φ : CNF} {v i l : ℕ} (h : (v, hpR φ.length i l) ∈ hamEdges φ)
    (hl : l ≤ 3 * φ.length) :
    (l < 3 * φ.length ∧ v = hpR φ.length i (l + 1)) ∨ (0 < l ∧ v = hpR φ.length i (l - 1)) ∨
      ((l = 0 ∨ l = 3 * φ.length) ∧ v = hpT φ.length i) ∨
      (v < φ.length ∧ (l = 3 * v + 1 ∨ l = 3 * v + 2)) := by
  obtain ⟨i', -, hc⟩ := hamEdges_cases h
  have h1 := le_hpT φ.length i'
  have h2 := le_hpT φ.length i
  rcases eq_or_ne i' i with rfl | hne
  · simp only [hpR, hpT_succ] at hc ⊢
    rcases hc with hc | hc | ⟨l', hl', hc⟩ | ⟨j, hj, hc⟩ <;> omega
  · have := hpT_sep (m := φ.length) hne
    simp only [hpR, hpT_succ] at hc
    rcases hc with hc | hc | ⟨l', hl', hc⟩ | ⟨j, hj, hc⟩ <;> omega

/-- The out-neighbours of the row vertex `hpR m i l`: its row neighbours, the next top
`hpT m (i + 1)` if it is a row end, and clause `v` if it is a vertex of the pair of `v`. -/
theorem hamEdges_from_hpR {φ : CNF} {v i l : ℕ} (h : (hpR φ.length i l, v) ∈ hamEdges φ)
    (hl : l ≤ 3 * φ.length) :
    (l < 3 * φ.length ∧ v = hpR φ.length i (l + 1)) ∨ (0 < l ∧ v = hpR φ.length i (l - 1)) ∨
      ((l = 0 ∨ l = 3 * φ.length) ∧ v = hpT φ.length (i + 1)) ∨
      (v < φ.length ∧ (l = 3 * v + 1 ∨ l = 3 * v + 2)) := by
  obtain ⟨i', -, hc⟩ := hamEdges_cases h
  have h1 := le_hpT φ.length i'
  have h2 := le_hpT φ.length i
  rcases eq_or_ne i' i with rfl | hne
  · simp only [hpR, hpT_succ] at hc ⊢
    rcases hc with hc | hc | ⟨l', hl', hc⟩ | ⟨j, hj, hc⟩ <;> omega
  · have := hpT_sep (m := φ.length) hne
    simp only [hpR, hpT_succ] at hc
    rcases hc with hc | hc | ⟨l', hl', hc⟩ | ⟨j, hj, hc⟩ <;> omega

/-- The in-neighbours of clause `j` are vertices of its pairs. -/
theorem hamEdges_to_clause {φ : CNF} {v j : ℕ} (h : (v, j) ∈ hamEdges φ) (hj : j < φ.length) :
    ∃ i < (hamVars φ).length,
      v = hpR φ.length i (3 * j + 1) ∨ v = hpR φ.length i (3 * j + 2) := by
  obtain ⟨i, hi, hc⟩ := hamEdges_cases h
  refine ⟨i, hi, ?_⟩
  have h1 := le_hpT φ.length i
  simp only [hpR, hpT_succ] at hc ⊢
  rcases hc with hc | hc | ⟨l', hl', hc⟩ | ⟨j', hj', hc⟩ <;> omega

/-- The out-neighbours of clause `j` are vertices of its pairs. -/
theorem hamEdges_from_clause {φ : CNF} {v j : ℕ} (h : (j, v) ∈ hamEdges φ) (hj : j < φ.length) :
    ∃ i < (hamVars φ).length,
      v = hpR φ.length i (3 * j + 1) ∨ v = hpR φ.length i (3 * j + 2) := by
  obtain ⟨i, hi, hc⟩ := hamEdges_cases h
  refine ⟨i, hi, ?_⟩
  have h1 := le_hpT φ.length i
  simp only [hpR, hpT_succ] at hc ⊢
  rcases hc with hc | hc | ⟨l', hl', hc⟩ | ⟨j', hj', hc⟩ <;> omega

/-! ### Neighbours along a duplicate-free list

Proof-internal facts about the two-element infix relation `[u, v] <:+: p` (`v` comes right after
`u` in `p`). -/

section Infix

variable {α : Type*} {p : List α} {u v w : α}

private theorem pair_infix_iff :
    [u, v] <:+: p ↔ ∃ (i : ℕ) (h : i + 1 < p.length), p[i] = u ∧ p[i + 1] = v := by
  rw [List.infix_iff_getElem?]
  constructor
  · rintro ⟨k, hk, hw⟩
    have h0 := hw 0 (by simp)
    have h1 := hw 1 (by simp)
    simp only [List.length_cons, List.length_nil] at hk
    simp only [List.getElem?_eq_some_iff, List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.zero_add, Nat.add_comm 1 k] at h0 h1
    obtain ⟨_, h0⟩ := h0
    obtain ⟨_, h1⟩ := h1
    exact ⟨k, by omega, h0, h1⟩
  · rintro ⟨i, hi, rfl, rfl⟩
    refine ⟨i, by simp; omega, fun t ht => ?_⟩
    obtain _ | _ | t := t
    · simp
    · simp [Nat.add_comm 1 i, List.getElem?_eq_getElem hi]
    · exact absurd ht (by simp)

private theorem pair_infix_right_unique (hp : p.Nodup) (h₁ : [u, v] <:+: p)
    (h₂ : [u, w] <:+: p) : v = w := by
  obtain ⟨i, hi, rfl, rfl⟩ := pair_infix_iff.1 h₁
  obtain ⟨i', hi', h, rfl⟩ := pair_infix_iff.1 h₂
  obtain rfl : i' = i := hp.getElem_inj_iff.1 h
  rfl

private theorem pair_infix_left_unique (hp : p.Nodup) (h₁ : [u, v] <:+: p)
    (h₂ : [w, v] <:+: p) : u = w := by
  obtain ⟨i, hi, rfl, rfl⟩ := pair_infix_iff.1 h₁
  obtain ⟨i', hi', rfl, h⟩ := pair_infix_iff.1 h₂
  obtain rfl : i' = i := by have := hp.getElem_inj_iff.1 h; omega
  rfl

private theorem not_pair_infix_swap (hp : p.Nodup) (h₁ : [u, v] <:+: p) (h₂ : [v, u] <:+: p) :
    False := by
  obtain ⟨i, hi, rfl, rfl⟩ := pair_infix_iff.1 h₁
  obtain ⟨i', hi', h, h'⟩ := pair_infix_iff.1 h₂
  have := hp.getElem_inj_iff.1 h
  have := hp.getElem_inj_iff.1 h'
  omega

/-- An element other than the head has a predecessor. -/
private theorem exists_pair_infix_left (hv : v ∈ p) (hh : p.head? ≠ some v) :
    ∃ u, [u, v] <:+: p := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  cases i with
  | zero => simp [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] at hh
  | succ i => exact ⟨p[i], pair_infix_iff.2 ⟨i, hi, rfl, rfl⟩⟩

/-- An element other than the last one has a successor. -/
private theorem exists_pair_infix_right (hv : v ∈ p) (hl : p.getLast? ≠ some v) :
    ∃ w, [v, w] <:+: p := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  by_cases h : i + 1 < p.length
  · exact ⟨p[i + 1], pair_infix_iff.2 ⟨i, h, rfl, rfl⟩⟩
  · obtain rfl : i = p.length - 1 := by omega
    simp [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hi] at hl

private theorem triple_infix_of_pair_infix (hp : p.Nodup) (h₁ : [u, v] <:+: p)
    (h₂ : [v, w] <:+: p) : [u, v, w] <:+: p := by
  obtain ⟨i, hi, rfl, rfl⟩ := pair_infix_iff.1 h₁
  obtain ⟨i', hi', h, rfl⟩ := pair_infix_iff.1 h₂
  obtain rfl : i' = i + 1 := hp.getElem_inj_iff.1 h
  rw [List.infix_iff_getElem?]
  refine ⟨i, by simp; omega, fun t ht => ?_⟩
  obtain _ | _ | _ | t := t
  · simp
  · simp [Nat.add_comm 1 i, List.getElem?_eq_getElem (Nat.lt_of_succ_lt hi')]
  · simp [Nat.add_comm 2 i, List.getElem?_eq_getElem hi']
  · exact absurd ht (by simp)

/-- An element whose predecessor is `z` or `w₁` and whose successor is `z` or `w₂`, where `w₁` is
not its predecessor and `w₂` not its successor, would close the cycle `z, v, z`. -/
private theorem pair_infix_forced_false {z w₁ w₂ : α} (hp : p.Nodup) (hin : ∃ x, [x, v] <:+: p)
    (hout : ∃ y, [v, y] <:+: p) (hx : ∀ x, [x, v] <:+: p → x = z ∨ x = w₁)
    (hy : ∀ y, [v, y] <:+: p → y = z ∨ y = w₂) (h₁ : ¬ [w₁, v] <:+: p)
    (h₂ : ¬ [v, w₂] <:+: p) : False := by
  obtain ⟨x, hx'⟩ := hin
  obtain ⟨y, hy'⟩ := hout
  rcases hx x hx' with rfl | rfl
  · rcases hy y hy' with rfl | rfl
    · exact not_pair_infix_swap hp hx' hy'
    · exact h₂ hy'
  · exact h₁ hx'

end Infix

/-- A Hamiltonian path visits every vertex. -/
theorem mem_of_isHamPath {n s t : ℕ} {es : List (ℕ × ℕ)} {p : List ℕ}
    (h : IsHamPath n es s t p) {v : ℕ} (hv : v < n) : v ∈ p := by
  obtain ⟨hnd, hlen, hlt, -⟩ := h
  have hsub : p.toFinset ⊆ Finset.range n := fun x hx => by
    simpa using hlt x (by simpa using hx)
  have heq : p.toFinset = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by simp [List.toFinset_card_of_nodup hnd, hlen])
  have : v ∈ p.toFinset := heq ▸ Finset.mem_range.2 hv
  simpa using this

/-! ### Sipser's separator argument -/

section Detours

variable {φ : CNF} {p : List ℕ}
  (h : IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)
    (hpT φ.length 0) (hpT φ.length (hamVars φ).length) p)
include h

/-- Consecutive vertices of a Hamiltonian path of `toHam φ` are joined by an arc. -/
theorem hamEdges_of_infix {u v : ℕ} (hn : [u, v] <:+: p) : (u, v) ∈ hamEdges φ :=
  (List.isChain_pair.1 (h.2.2.2.2.2.infix hn)).1

theorem hamPath_exists_pred {v : ℕ} (hv : v < hpT φ.length (hamVars φ).length + 1)
    (h0 : v ≠ hpT φ.length 0) : ∃ u, [u, v] <:+: p :=
  exists_pair_infix_left (mem_of_isHamPath h hv) (by rw [h.2.2.2.1]; simpa using Ne.symm h0)

theorem hamPath_exists_succ {v : ℕ} (hv : v < hpT φ.length (hamVars φ).length + 1)
    (hk : v ≠ hpT φ.length (hamVars φ).length) : ∃ w, [v, w] <:+: p :=
  exists_pair_infix_right (mem_of_isHamPath h hv) (by rw [h.2.2.2.2.1]; simpa using Ne.symm hk)

theorem hamPath_exists_pred_hpR {i l : ℕ} (hi : i < (hamVars φ).length) (hl : l ≤ 3 * φ.length) :
    ∃ u, [u, hpR φ.length i l] <:+: p := by
  have := hpT_add_le (m := φ.length) hi
  have := le_hpT φ.length i
  refine hamPath_exists_pred h ?_ ?_ <;> simp only [hpR, hpT_zero] <;> omega

theorem hamPath_exists_succ_hpR {i l : ℕ} (hi : i < (hamVars φ).length) (hl : l ≤ 3 * φ.length) :
    ∃ w, [hpR φ.length i l, w] <:+: p := by
  have := hpT_add_le (m := φ.length) hi
  refine hamPath_exists_succ h ?_ ?_ <;> simp only [hpR] <;> omega

theorem hamPath_exists_pred_clause {j : ℕ} (hj : j < φ.length) : ∃ u, [u, j] <:+: p := by
  have := le_hpT φ.length (hamVars φ).length
  exact hamPath_exists_pred h (by omega) (by rw [hpT_zero]; omega)

theorem hamPath_exists_succ_clause {j : ℕ} (hj : j < φ.length) : ∃ w, [j, w] <:+: p := by
  have := le_hpT φ.length (hamVars φ).length
  exact hamPath_exists_succ h (by omega) (by omega)

/-- A row end entered from the top and left to the next top: then the other row end has its row
neighbour as both predecessor and successor. -/
theorem hamPath_rowEnd_false {i l : ℕ} (hi : i < (hamVars φ).length) (hm : 0 < φ.length)
    (hl : l = 0 ∨ l = 3 * φ.length) (h₁ : [hpT φ.length i, hpR φ.length i l] <:+: p)
    (h₂ : [hpR φ.length i l, hpT φ.length (i + 1)] <:+: p) : False := by
  obtain ⟨lz, hlz⟩ : ∃ lz, (l = 0 ∧ lz = 3 * φ.length - 1) ∨ (l = 3 * φ.length ∧ lz = 1) := by
    rcases hl with hl | hl
    exacts [⟨_, Or.inl ⟨hl, rfl⟩⟩, ⟨_, Or.inr ⟨hl, rfl⟩⟩]
  refine pair_infix_forced_false h.1 (v := hpR φ.length i (3 * φ.length - l))
    (z := hpR φ.length i lz) (w₁ := hpT φ.length i) (w₂ := hpT φ.length (i + 1))
    (hamPath_exists_pred_hpR h hi (by omega)) (hamPath_exists_succ_hpR h hi (by omega))
    (fun x hx => ?_) (fun y hy => ?_) (fun hn => ?_) (fun hn => ?_)
  · have hc := hamEdges_to_hpR (hamEdges_of_infix h hx) (by omega)
    simp only [hpR] at hc ⊢
    omega
  · have hc := hamEdges_from_hpR (hamEdges_of_infix h hy) (by omega)
    simp only [hpR] at hc ⊢
    omega
  · have := pair_infix_right_unique h.1 h₁ hn
    simp only [hpR] at this
    omega
  · have := pair_infix_left_unique h.1 h₂ hn
    simp only [hpR] at this
    omega

/-- A separator `hpR m i l` (`l = 3 j'`) with a row neighbour `hpR m i lw` that is neither its
predecessor nor its successor. -/
theorem hamPath_separator_false {i l lw : ℕ} (hi : i < (hamVars φ).length) (hl3 : l % 3 = 0)
    (hl : l ≤ 3 * φ.length) (hw : lw = l + 1 ∨ lw + 1 = l) (hwm : lw ≤ 3 * φ.length)
    (h₁ : ¬ [hpR φ.length i lw, hpR φ.length i l] <:+: p)
    (h₂ : ¬ [hpR φ.length i l, hpR φ.length i lw] <:+: p) : False := by
  by_cases hin : 0 < l ∧ l < 3 * φ.length
  · refine pair_infix_forced_false h.1 (v := hpR φ.length i l) (z := hpR φ.length i (2 * l - lw))
      (hamPath_exists_pred_hpR h hi hl) (hamPath_exists_succ_hpR h hi hl) (fun x hx => ?_)
      (fun y hy => ?_) h₁ h₂
    · have hc := hamEdges_to_hpR (hamEdges_of_infix h hx) hl
      simp only [hpR] at hc ⊢
      omega
    · have hc := hamEdges_from_hpR (hamEdges_of_infix h hy) hl
      simp only [hpR] at hc ⊢
      omega
  · obtain ⟨x, hx⟩ := hamPath_exists_pred_hpR h hi hl
    obtain ⟨y, hy⟩ := hamPath_exists_succ_hpR h hi hl
    have hx' : x = hpR φ.length i lw ∨ x = hpT φ.length i := by
      have hc := hamEdges_to_hpR (hamEdges_of_infix h hx) hl
      simp only [hpR] at hc ⊢
      omega
    have hy' : y = hpR φ.length i lw ∨ y = hpT φ.length (i + 1) := by
      have hc := hamEdges_from_hpR (hamEdges_of_infix h hy) hl
      simp only [hpR] at hc ⊢
      omega
    rcases hx' with rfl | rfl
    · exact h₁ hx
    rcases hy' with rfl | rfl
    · exact h₂ hy
    exact hamPath_rowEnd_false h hi (by omega) (by omega) hx hy

/-- Sipser's separator argument: clause `j`, entered from the pair vertex `hpR m i la`, is left
to the other pair vertex `hpR m i lc`. -/
theorem hamPath_pair_false {i j la lc b : ℕ} (hi : i < (hamVars φ).length) (hj : j < φ.length)
    (hlac : (la = 3 * j + 1 ∧ lc = 3 * j + 2) ∨ (la = 3 * j + 2 ∧ lc = 3 * j + 1))
    (ha : [hpR φ.length i la, j] <:+: p) (hb : [j, b] <:+: p) (hbc : b ≠ hpR φ.length i lc) :
    False := by
  have hT := le_hpT φ.length i
  -- The other pair vertex `c` is entered from its separator `d` and left to `a`.
  have hca : [hpR φ.length i lc, hpR φ.length i la] <:+: p := by
    obtain ⟨x, hx⟩ := hamPath_exists_pred_hpR h hi (l := lc) (by omega)
    obtain ⟨y, hy⟩ := hamPath_exists_succ_hpR h hi (l := lc) (by omega)
    have hxd : x = hpR φ.length i (2 * lc - la) := by
      have hc := hamEdges_to_hpR (hamEdges_of_infix h hx) (by omega)
      have : x = hpR φ.length i (2 * lc - la) ∨ x = hpR φ.length i la ∨ x = j := by
        simp only [hpR] at hc ⊢
        omega
      rcases this with hx' | hx' | hx'
      · exact hx'
      · rw [hx'] at hx
        have := pair_infix_right_unique h.1 ha hx
        simp only [hpR] at this
        omega
      · rw [hx'] at hx
        exact absurd (pair_infix_right_unique h.1 hb hx) hbc
    have : y = hpR φ.length i (2 * lc - la) ∨ y = hpR φ.length i la ∨ y = j := by
      have hc := hamEdges_from_hpR (hamEdges_of_infix h hy) (by omega)
      simp only [hpR] at hc ⊢
      omega
    rcases this with hy' | hy' | hy'
    · rw [hy', ← hxd] at hy
      exact (not_pair_infix_swap h.1 hx hy).elim
    · exact hy' ▸ hy
    · rw [hy'] at hy
      have := pair_infix_left_unique h.1 hy ha
      simp only [hpR] at this
      omega
  -- The separator on the other side of `a` has `a` as neither predecessor nor successor.
  refine hamPath_separator_false h hi (l := 2 * la - lc) (lw := la) (by omega) (by omega)
    (by omega) (by omega)
    (fun hn => ?_) (fun hn => ?_)
  · have := pair_infix_right_unique h.1 ha hn
    simp only [hpR] at this
    omega
  · have := pair_infix_left_unique h.1 hn hca
    simp only [hpR] at this
    omega

end Detours

/-- Every Hamiltonian path of `toHam φ` has normal detours. -/
theorem detoursNormal_of_isHamPath {φ : CNF} {p : List ℕ}
    (h : IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)
      (hpT φ.length 0) (hpT φ.length (hamVars φ).length) p) :
    DetoursNormal φ p := by
  intro j hj
  obtain ⟨a, ha⟩ := hamPath_exists_pred_clause h hj
  obtain ⟨b, hb⟩ := hamPath_exists_succ_clause h hj
  obtain ⟨i, hi, hai⟩ := hamEdges_to_clause (hamEdges_of_infix h ha) hj
  refine ⟨i, hi, ?_⟩
  rcases hai with rfl | rfl
  · left
    by_cases hbc : b = hpR φ.length i (3 * j + 2)
    · exact hbc ▸ triple_infix_of_pair_infix h.1 ha hb
    · exact (hamPath_pair_false h hi hj (Or.inl ⟨rfl, rfl⟩) ha hb hbc).elim
  · right
    by_cases hbc : b = hpR φ.length i (3 * j + 1)
    · exact hbc ▸ triple_infix_of_pair_infix h.1 ha hb
    · exact (hamPath_pair_false h hi hj (Or.inr ⟨rfl, rfl⟩) ha hb hbc).elim

end Cslib.Complexity.Karp
