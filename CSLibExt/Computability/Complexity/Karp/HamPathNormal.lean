/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathDetours

/-!
# HAMPATH, backward direction, part 2: normal detours give an assignment

`cnfSat_of_isHamPath`: if `p` is a Hamiltonian path of Sipser's graph for `φ`
(`CSLibExt.Computability.Complexity.Karp.HamPath`) from `hpT m 0` to `hpT m k` whose clause
detours are normal (`DetoursNormal φ p`), then `φ` is satisfiable. Part 1,
`detoursNormal_of_isHamPath` (`Karp.HamPathDetours`), shows that every Hamiltonian path has
normal detours.

Proof (Sipser, Theorem 7.46):

* Arcs, on top of `mem_hamEdges`, `hamEdges_from_hpR` and `hamEdges_to_hpR`: a top points only to
  its row ends (`hpT_arc`), the arc from a row vertex to a clause vertex is a detour of a literal
  of that clause (`hpR_arc_clause`), and `hpRo m i b l` reads row `i` from the left end
  (`b = true`) or the right end, with one out/in characterization for both
  (`hpRo_arc`, `arc_hpRo`).
* Contract the detours: `dropClauses φ p` removes the clause vertices `j < m`. Each clause vertex
  of `p` sits between the two vertices of its pair in one row, which are joined by row arcs, so
  consecutive vertices of `dropClauses φ p` are still joined by arcs (`isChain_dropClauses`),
  and a detour `a, j, c` of `p` becomes the
  step `a, c` (`infix_dropClauses`).
* In `dropClauses φ p`, top `hpT m i` is followed by one end of row `i` (`exists_top_succ`); the
  row is then run to its other end (`row_run`): among non-clause vertices the only arcs join row
  neighbours, a step back would close a two-cycle, and leaving at once from the entry end
  strands the rest of the row (`no_shortcut`). Steps are two-element infixes `[u, v] <:+: l`.
* The assignment sets the variable of diamond `i` true iff `hpT m i` is followed by `hpR m i 0`.
  A detour `hpR m i (3 j + 1), j, hpR m i (3 j + 2)` uses the arc `hpR m i (3 j + 1) → j`, which
  exists only when the variable occurs positively in clause `j`, and forces row `i` to run left
  to right (the opposite direction steps from `hpR m i (3 j + 2)` back to `hpR m i (3 j + 1)`);
  symmetrically for negative occurrences.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-! ### Vertex arithmetic -/

theorem hpT_inj {m i i' : ℕ} (h : hpT m i = hpT m i') : i = i' := by
  by_contra hne
  have := hpT_sep (m := m) hne
  omega

theorem hpR_inj {m i i' l l' : ℕ} (hl : l ≤ 3 * m) (hl' : l' ≤ 3 * m)
    (h : hpR m i l = hpR m i' l') : i = i' ∧ l = l' := by
  rcases eq_or_ne i i' with rfl | hne
  · simp only [hpR] at h; omega
  · have := hpT_sep (m := m) hne
    simp only [hpR] at h; omega

theorem hpR_ne_hpT {m i i' l : ℕ} (hl : l ≤ 3 * m) : hpR m i l ≠ hpT m i' := by
  intro h
  rcases eq_or_ne i i' with rfl | hne
  · simp only [hpR] at h; omega
  · have := hpT_sep (m := m) hne
    simp only [hpR] at h; omega

theorem le_hpR (m i l : ℕ) : m ≤ hpR m i l := by
  have := le_hpT m i
  simp only [hpR]; omega

/-! ### Arcs -/

/-- The out-neighbours of a top are its row ends. -/
theorem hpT_arc {φ : CNF} {i v : ℕ} (h : (hpT φ.length i, v) ∈ hamEdges φ) :
    v = hpR φ.length i 0 ∨ v = hpR φ.length i (3 * φ.length) := by
  obtain ⟨i', -, hc⟩ := hamEdges_cases h
  have h1 := le_hpT φ.length i'
  have h2 := le_hpT φ.length i
  rcases eq_or_ne i' i with rfl | hne
  · simp only [hpR, hpT_succ] at hc ⊢
    rcases hc with hc | hc | ⟨l', hl', hc⟩ | ⟨j, hj, hc⟩ <;> omega
  · have := hpT_sep (m := φ.length) hne
    simp only [hpR, hpT_succ] at hc
    rcases hc with hc | hc | ⟨l', hl', hc⟩ | ⟨j, hj, hc⟩ <;> omega

/-- An arc from a row vertex of diamond `i` to clause `j` is a detour of a literal of the
variable of diamond `i` in clause `j`: positive from `3 j + 1`, negative from `3 j + 2`. -/
theorem hpR_arc_clause {φ : CNF} {i l j : ℕ} (hl : l ≤ 3 * φ.length) (hj : j < φ.length)
    (h : (hpR φ.length i l, j) ∈ hamEdges φ) :
    (l = 3 * j + 1 ∧ ((hamVars φ).getD i 0, true) ∈ φ.getD j []) ∨
      (l = 3 * j + 2 ∧ ((hamVars φ).getD i 0, false) ∈ φ.getD j []) := by
  obtain ⟨i', -, h⟩ := mem_hamEdges.1 h
  have hle := le_hpR φ.length i l
  have hT : ∀ i'', j ≠ hpT φ.length i'' :=
    fun i'' => by have := le_hpT φ.length i''; omega
  have hR : ∀ i'' l'', j ≠ hpR φ.length i'' l'' :=
    fun i'' l'' => by have := le_hpR φ.length i'' l''; omega
  rcases h with ((⟨hu, -⟩ | ⟨hu, -⟩ | ⟨-, hv⟩ | ⟨-, hv⟩) | ⟨l', -, ⟨-, hv⟩ | ⟨-, hv⟩⟩) |
    ⟨j', hj', ⟨hx, ⟨hu, rfl⟩ | ⟨hu, -⟩⟩ | ⟨hx, ⟨hu, rfl⟩ | ⟨hu, -⟩⟩⟩
  · exact absurd hu (hpR_ne_hpT hl)
  · exact absurd hu (hpR_ne_hpT hl)
  · exact absurd hv (hT _)
  · exact absurd hv (hT _)
  · exact absurd hv (hR _ _)
  · exact absurd hv (hR _ _)
  · obtain ⟨rfl, rfl⟩ := hpR_inj hl (by omega) hu; exact .inl ⟨rfl, hx⟩
  · omega
  · obtain ⟨rfl, rfl⟩ := hpR_inj hl (by omega) hu; exact .inr ⟨rfl, hx⟩
  · omega

theorem row_mem_hamEdges {φ : CNF} {i l : ℕ} (hi : i < (hamVars φ).length)
    (hl : l < 3 * φ.length) :
    (hpR φ.length i l, hpR φ.length i (l + 1)) ∈ hamEdges φ ∧
      (hpR φ.length i (l + 1), hpR φ.length i l) ∈ hamEdges φ :=
  ⟨mem_hamEdges.2 ⟨i, hi, .inl (.inr ⟨l, hl, .inl ⟨rfl, rfl⟩⟩)⟩,
    mem_hamEdges.2 ⟨i, hi, .inl (.inr ⟨l, hl, .inr ⟨rfl, rfl⟩⟩)⟩⟩

/-! ### Rows read from either end -/

/-- Row vertex `l` of diamond `i`, counted from the left end (`b = true`) or from the right end
(`b = false`). -/
def hpRo (m i : ℕ) (b : Bool) (l : ℕ) : ℕ := hpR m i (if b then l else 3 * m - l)

theorem hpRo_inj {m i l l' : ℕ} {b : Bool} (hl : l ≤ 3 * m) (hl' : l' ≤ 3 * m)
    (h : hpRo m i b l = hpRo m i b l') : l = l' := by
  cases b
  · simp only [hpRo, Bool.false_eq_true, ite_false] at h
    have := (hpR_inj (by omega) (by omega) h).2; omega
  · exact (hpR_inj hl hl' h).2

theorem hpRo_ne_hpT {m i i' l : ℕ} {b : Bool} (hl : l ≤ 3 * m) : hpRo m i b l ≠ hpT m i' :=
  hpR_ne_hpT (by split <;> omega)

theorem le_hpRo (m i : ℕ) (b : Bool) (l : ℕ) : m ≤ hpRo m i b l := le_hpR _ _ _

theorem hpRo_lt_hpT_succ {m i l : ℕ} {b : Bool} (hl : l ≤ 3 * m) :
    hpRo m i b l < hpT m (i + 1) :=
  hpR_lt_hpT_succ (by split <;> omega)

/-- The non-clause out-neighbours of a row vertex, read from either end. -/
theorem hpRo_arc {φ : CNF} {i l v : ℕ} {b : Bool} (hl : l ≤ 3 * φ.length)
    (hv : φ.length ≤ v) (h : (hpRo φ.length i b l, v) ∈ hamEdges φ) :
    (l < 3 * φ.length ∧ v = hpRo φ.length i b (l + 1)) ∨
      (0 < l ∧ v = hpRo φ.length i b (l - 1)) ∨
      ((l = 0 ∨ l = 3 * φ.length) ∧ v = hpT φ.length (i + 1)) := by
  cases b
  · simp only [hpRo, Bool.false_eq_true, ite_false] at h ⊢
    rcases hamEdges_from_hpR h (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact .inr (.inl ⟨by omega, h2.trans (congrArg (hpR _ _) (by omega))⟩)
    · exact .inl ⟨by omega, h2.trans (congrArg (hpR _ _) (by omega))⟩
    · exact .inr (.inr ⟨by omega, h2⟩)
    · omega
  · rcases hamEdges_from_hpR h hl with h1 | h1 | h1 | ⟨h1, -⟩
    · exact .inl h1
    · exact .inr (.inl h1)
    · exact .inr (.inr h1)
    · omega

/-- The non-clause in-neighbours of a row vertex, read from either end. -/
theorem arc_hpRo {φ : CNF} {i l u : ℕ} {b : Bool} (hl : l ≤ 3 * φ.length)
    (hu : φ.length ≤ u) (h : (u, hpRo φ.length i b l) ∈ hamEdges φ) :
    (0 < l ∧ u = hpRo φ.length i b (l - 1)) ∨
      (l < 3 * φ.length ∧ u = hpRo φ.length i b (l + 1)) ∨
      ((l = 0 ∨ l = 3 * φ.length) ∧ u = hpT φ.length i) := by
  cases b
  · simp only [hpRo, Bool.false_eq_true, ite_false] at h ⊢
    rcases hamEdges_to_hpR h (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact .inl ⟨by omega, h2.trans (congrArg (hpR _ _) (by omega))⟩
    · exact .inr (.inl ⟨by omega, h2.trans (congrArg (hpR _ _) (by omega))⟩)
    · exact .inr (.inr ⟨by omega, h2⟩)
    · omega
  · rcases hamEdges_to_hpR h hl with h1 | h1 | h1 | ⟨h1, -⟩
    · exact .inr (.inl h1)
    · exact .inl h1
    · exact .inr (.inr h1)
    · omega

/-! ### Lists

Proof-internal facts about duplicate-free lists and the two-element infix relation
`[u, v] <:+: l` (`v` comes right after `u` in `l`). -/

section Lists

variable {α : Type*}

private theorem pair_infix_iff {l : List α} {u v : α} :
    [u, v] <:+: l ↔ ∃ (i : ℕ) (h : i + 1 < l.length), l[i] = u ∧ l[i + 1] = v := by
  constructor
  · rintro ⟨s, t, rfl⟩
    exact ⟨s.length, by simp, by simp, by simp [List.getElem_append_right]⟩
  · rintro ⟨i, hi, rfl, rfl⟩
    rw [List.infix_iff_getElem?]
    refine ⟨i, by simp; omega, fun t ht => ?_⟩
    obtain _ | _ | t := t
    · simp
    · simp [Nat.add_comm 1 i, List.getElem?_eq_getElem hi]
    · exact absurd ht (by simp)

private theorem pair_infix_right_unique {l : List α} {u v w : α} (hl : l.Nodup)
    (h₁ : [u, v] <:+: l) (h₂ : [u, w] <:+: l) : v = w := by
  obtain ⟨i, hi, rfl, rfl⟩ := pair_infix_iff.1 h₁
  obtain ⟨i', hi', h, rfl⟩ := pair_infix_iff.1 h₂
  obtain rfl : i' = i := hl.getElem_inj_iff.1 h
  rfl

private theorem pair_infix_left_unique {l : List α} {u v w : α} (hl : l.Nodup)
    (h₁ : [u, v] <:+: l) (h₂ : [w, v] <:+: l) : u = w := by
  obtain ⟨i, hi, rfl, rfl⟩ := pair_infix_iff.1 h₁
  obtain ⟨i', hi', rfl, h⟩ := pair_infix_iff.1 h₂
  obtain rfl : i' = i := by have := hl.getElem_inj_iff.1 h; omega
  rfl

private theorem not_pair_infix_swap {l : List α} {u v : α} (hl : l.Nodup) (h₁ : [u, v] <:+: l)
    (h₂ : [v, u] <:+: l) : False := by
  obtain ⟨i, hi, rfl, rfl⟩ := pair_infix_iff.1 h₁
  obtain ⟨i', hi', h, h'⟩ := pair_infix_iff.1 h₂
  have := hl.getElem_inj_iff.1 h
  have := hl.getElem_inj_iff.1 h'
  omega

private theorem pair_infix_of_triple {l : List α} {a b c : α} (h : [a, b, c] <:+: l) :
    [a, b] <:+: l ∧ [b, c] <:+: l :=
  ⟨List.IsInfix.trans ⟨[], [c], rfl⟩ h, List.IsInfix.trans ⟨[a], [], rfl⟩ h⟩

/-- An element other than the last one has a successor. -/
private theorem exists_pair_infix_right {l : List α} {v : α} (hv : v ∈ l)
    (hl : l.getLast? ≠ some v) : ∃ w, [v, w] <:+: l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  by_cases h : i + 1 < l.length
  · exact ⟨l[i + 1], pair_infix_iff.2 ⟨i, h, rfl, rfl⟩⟩
  · obtain rfl : i = l.length - 1 := by omega
    simp [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hi] at hl

/-- If the head fails `Q` and some element satisfies it, some step goes from outside `Q` into
`Q`. -/
private theorem exists_infix_boundary (Q : α → Prop) {l : List α} {h a : α}
    (hhead : l.head? = some h) (hh : ¬Q h) (ha : a ∈ l) (hQa : Q a) :
    ∃ w s, [w, s] <:+: l ∧ ¬Q w ∧ Q s := by
  induction l generalizing h with
  | nil => simp at ha
  | cons x r ih =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases r with
    | nil =>
      rw [List.mem_singleton] at ha
      exact absurd (ha ▸ hQa) hh
    | cons y r =>
      by_cases hy : Q y
      · exact ⟨x, y, ⟨[], r, rfl⟩, hh, hy⟩
      · have ha' : a ∈ y :: r := by
          rcases List.mem_cons.1 ha with rfl | ha
          · exact absurd hQa hh
          · exact ha
        obtain ⟨w, s, hws, hw, hs⟩ := ih rfl hy ha'
        exact ⟨w, s, hws.trans (List.infix_cons (List.infix_refl _)), hw, hs⟩

/-- Contracting isolated detours: if every element failing `P` sits between two elements
satisfying `P` that are `R`-related, then the `P`-elements form an `R`-chain. -/
private theorem isChain_filter_of_detours {R' R : α → α → Prop} {P : α → Bool}
    (hR : ∀ a b, R' a b → P a → P b → R a b) :
    ∀ {l : List α}, l.IsChain R' →
      (∀ a b c, [a, b, c] <:+: l → P b = false → R a c) →
      (∀ a b, [a, b] <:+: l → P a = false → P b = false → False) →
      (∀ x ∈ l.head?, P x) → (∀ x ∈ l.getLast?, P x) → (l.filter P).IsChain R
  | [], _, _, _, _, _ => by simp
  | [x], _, _, _, hh, _ => by simp [hh x rfl]
  | x :: y :: r, hc, hd, hn, hh, hlast => by
    have hx : P x := hh x rfl
    rw [List.isChain_cons_cons] at hc
    have hsub : ∀ {u : List α}, u <:+: y :: r → u <:+: x :: y :: r :=
      fun h => h.trans (List.infix_cons (List.infix_refl _))
    by_cases hy : P y
    · have ih := isChain_filter_of_detours hR hc.2 (fun a b c h => hd a b c (hsub h))
        (fun a b h => hn a b (hsub h)) (fun z hz => by cases hz; exact hy)
        (fun z hz => hlast z (by rwa [List.getLast?_cons_cons]))
      rw [List.filter_cons_of_pos hx]
      rw [List.filter_cons_of_pos hy] at ih ⊢
      exact List.isChain_cons_cons.2 ⟨hR x y hc.1 hx hy, ih⟩
    · have hy' : P y = false := by simpa using hy
      cases r with
      | nil => exact absurd (hlast y rfl) hy
      | cons z r =>
        have hz : P z := by
          by_contra hz
          exact hn y z ⟨[x], r, rfl⟩ hy' (by simpa using hz)
        have hsub' : ∀ {u : List α}, u <:+: z :: r → u <:+: x :: y :: z :: r :=
          fun h => hsub (h.trans (List.infix_cons (List.infix_refl _)))
        have ih := isChain_filter_of_detours hR (List.isChain_cons_cons.1 hc.2).2
          (fun a b c h => hd a b c (hsub' h)) (fun a b h => hn a b (hsub' h))
          (fun w hw => by cases hw; exact hz)
          (fun w hw => hlast w (by rwa [List.getLast?_cons_cons, List.getLast?_cons_cons]))
        rw [List.filter_cons_of_pos hx, List.filter_cons_of_neg hy, List.filter_cons_of_pos hz]
        rw [List.filter_cons_of_pos hz] at ih
        exact List.isChain_cons_cons.2 ⟨hd x y z ⟨[], r, rfl⟩ hy', ih⟩

end Lists

/-! ### Contracting the detours -/

/-- The non-clause vertices of `p` in order: `p` without the clause vertices `j < φ.length`. -/
def dropClauses (φ : CNF) (p : List ℕ) : List ℕ := p.filter fun v => decide (φ.length ≤ v)

section Contract

variable {φ : CNF} {p : List ℕ}
  (h : IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)
    (hpT φ.length 0) (hpT φ.length (hamVars φ).length) p)
include h

theorem mem_dropClauses {v : ℕ} :
    v ∈ dropClauses φ p ↔ φ.length ≤ v ∧ v < hpT φ.length (hamVars φ).length + 1 := by
  simp only [dropClauses, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨hv, hm⟩ => ⟨hm, h.2.2.1 v hv⟩, fun ⟨hm, hv⟩ => ⟨mem_of_isHamPath h hv, hm⟩⟩

theorem head?_dropClauses : (dropClauses φ p).head? = some (hpT φ.length 0) := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 h.2.2.2.1
  rw [dropClauses, ht, List.filter_cons_of_pos (by simpa using le_hpT _ _)]
  rfl

theorem getLast?_dropClauses :
    (dropClauses φ p).getLast? = some (hpT φ.length (hamVars φ).length) := by
  have hrev : p.reverse.head? = some (hpT φ.length (hamVars φ).length) := by
    rw [List.head?_reverse]; exact h.2.2.2.2.1
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 hrev
  rw [← List.head?_reverse, dropClauses, ← List.filter_reverse, ht,
    List.filter_cons_of_pos (by simpa using le_hpT _ _)]
  rfl

theorem isChain_dropClauses (hd : DetoursNormal φ p) :
    (dropClauses φ p).IsChain fun u v => (u, v) ∈ hamEdges φ := by
  refine isChain_filter_of_detours (fun a b hab _ _ => hab.1) h.2.2.2.2.2 ?_ ?_ ?_ ?_
  · intro a b c habc hb
    simp only [decide_eq_false_iff_not, Nat.not_le] at hb
    have habc := pair_infix_of_triple habc
    obtain ⟨i, hi, h1 | h1⟩ := hd b hb <;> have h1 := pair_infix_of_triple h1 <;>
      rw [pair_infix_left_unique h.1 habc.1 h1.1, pair_infix_right_unique h.1 habc.2 h1.2]
    · exact (row_mem_hamEdges hi (by omega)).1
    · exact (row_mem_hamEdges hi (by omega)).2
  · intro a b hab ha hb
    simp only [decide_eq_false_iff_not, Nat.not_le] at ha hb
    obtain ⟨i, hi, h1 | h1⟩ := hd b hb
    · have := pair_infix_left_unique h.1 hab (pair_infix_of_triple h1).1
      have := le_hpR φ.length i (3 * b + 1)
      omega
    · have := pair_infix_left_unique h.1 hab (pair_infix_of_triple h1).1
      have := le_hpR φ.length i (3 * b + 2)
      omega
  · intro x hx
    rw [h.2.2.2.1, Option.mem_some_iff] at hx
    simpa [← hx] using le_hpT _ _
  · intro x hx
    rw [h.2.2.2.2.1, Option.mem_some_iff] at hx
    simpa [← hx] using le_hpT _ _

omit h in
/-- A detour `a, j, c` of `p` becomes the step `a, c` of `dropClauses φ p`. -/
theorem infix_dropClauses {a j c : ℕ} (hp : [a, j, c] <:+: p) (hj : j < φ.length)
    (ha : φ.length ≤ a) (hc : φ.length ≤ c) : [a, c] <:+: dropClauses φ p := by
  obtain ⟨s, t, rfl⟩ := hp
  refine ⟨s.filter fun v => decide (φ.length ≤ v), t.filter fun v => decide (φ.length ≤ v), ?_⟩
  simp [dropClauses, List.filter_append, ha, hc, Nat.not_le.2 hj]

theorem hpT_mem_dropClauses {i : ℕ} (hi : i ≤ (hamVars φ).length) :
    hpT φ.length i ∈ dropClauses φ p :=
  (mem_dropClauses h).2 ⟨le_hpT _ _, Nat.lt_succ_of_le (hpT_mono hi)⟩

theorem hpRo_mem_dropClauses {i l : ℕ} {b : Bool} (hi : i < (hamVars φ).length)
    (hl : l ≤ 3 * φ.length) : hpRo φ.length i b l ∈ dropClauses φ p :=
  (mem_dropClauses h).2 ⟨le_hpRo _ _ _ _,
    lt_of_lt_of_le (hpRo_lt_hpT_succ hl) (le_trans (hpT_mono hi) (Nat.le_succ _))⟩

/-! ### Each row is run from end to end -/

/-- A step of `dropClauses φ p` is an arc between non-clause vertices. -/
theorem arc_of_infix_dropClauses {u v : ℕ} (hd : DetoursNormal φ p)
    (huv : [u, v] <:+: dropClauses φ p) :
    (u, v) ∈ hamEdges φ ∧ φ.length ≤ u ∧ φ.length ≤ v :=
  ⟨(List.isChain_pair.1 ((isChain_dropClauses h hd).infix huv)),
    ((mem_dropClauses h).1 (huv.subset (by simp))).1,
    ((mem_dropClauses h).1 (huv.subset (by simp))).1⟩

/-- Every vertex of `dropClauses φ p` but the last top has a successor there. -/
theorem exists_infix_dropClauses {v : ℕ} (hv : v ∈ dropClauses φ p)
    (hk : v ≠ hpT φ.length (hamVars φ).length) : ∃ w, [v, w] <:+: dropClauses φ p :=
  exists_pair_infix_right hv (by rw [getLast?_dropClauses h]; simpa using Ne.symm hk)

/-- Entering row `i` at one end and leaving at once for the next top strands the rest of the
row: its first vertex in `dropClauses φ p` would need an arc from outside the row. -/
theorem no_shortcut {i : ℕ} {b : Bool} (hi : i < (hamVars φ).length) (hm : 0 < φ.length)
    (hd : DetoursNormal φ p)
    (h1 : [hpT φ.length i, hpRo φ.length i b 0] <:+: dropClauses φ p)
    (h2 : [hpRo φ.length i b 0, hpT φ.length (i + 1)] <:+: dropClauses φ p) : False := by
  have hnd : (dropClauses φ p).Nodup := h.1.filter _
  obtain ⟨w, s, hws, hw, l, hl1, hl2, rfl⟩ :=
    exists_infix_boundary (fun v => ∃ l, 1 ≤ l ∧ l ≤ 3 * φ.length ∧ v = hpRo φ.length i b l)
      (head?_dropClauses h) (fun ⟨l, _, hl, he⟩ => hpRo_ne_hpT hl he.symm)
      (hpRo_mem_dropClauses h hi (by omega)) ⟨1, le_rfl, by omega, rfl⟩
  obtain ⟨harc, hwm, -⟩ := arc_of_infix_dropClauses h hd hws
  rcases arc_hpRo hl2 hwm harc with ⟨-, rfl⟩ | ⟨hl, rfl⟩ | ⟨hl | hl, rfl⟩
  · obtain rfl : l = 1 := by
      by_contra hne
      exact hw ⟨l - 1, by omega, by omega, rfl⟩
    rw [Nat.sub_self] at hws
    exact hpRo_ne_hpT (l := 1) (by omega) (pair_infix_right_unique hnd hws h2)
  · exact hw ⟨l + 1, by omega, hl, rfl⟩
  · omega
  · subst hl
    have := hpRo_inj le_rfl (Nat.zero_le _) (pair_infix_right_unique hnd hws h1)
    omega

/-- Once top `hpT m i` is followed by the end `b` of row `i`, the row is run to its other end. -/
theorem row_run {i : ℕ} {b : Bool} (hi : i < (hamVars φ).length) (hd : DetoursNormal φ p)
    (h0 : [hpT φ.length i, hpRo φ.length i b 0] <:+: dropClauses φ p) :
    ∀ l < 3 * φ.length,
      [hpRo φ.length i b l, hpRo φ.length i b (l + 1)] <:+: dropClauses φ p := by
  have hnd : (dropClauses φ p).Nodup := h.1.filter _
  have hsucc : ∀ l ≤ 3 * φ.length, ∃ w, [hpRo φ.length i b l, w] <:+: dropClauses φ p :=
    fun l hl => exists_infix_dropClauses h (hpRo_mem_dropClauses h hi hl) (hpRo_ne_hpT hl)
  intro l
  induction l with
  | zero =>
    intro hl
    obtain ⟨w, hw⟩ := hsucc 0 (Nat.zero_le _)
    obtain ⟨harc, -, hwm⟩ := arc_of_infix_dropClauses h hd hw
    rcases hpRo_arc (Nat.zero_le _) hwm harc with ⟨-, rfl⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact hw
    · omega
    · exact (no_shortcut h hi (by omega) hd h0 hw).elim
  | succ l ih =>
    intro hl
    have ih := ih (by omega)
    obtain ⟨w, hw⟩ := hsucc (l + 1) (by omega)
    obtain ⟨harc, -, hwm⟩ := arc_of_infix_dropClauses h hd hw
    rcases hpRo_arc (by omega) hwm harc with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h1, -⟩
    · exact hw
    · exact (not_pair_infix_swap hnd ih hw).elim
    · omega

/-- Every top but the last is followed by one end of its row. -/
theorem exists_top_succ {i : ℕ} (hi : i < (hamVars φ).length) (hd : DetoursNormal φ p) :
    ∃ b, [hpT φ.length i, hpRo φ.length i b 0] <:+: dropClauses φ p := by
  obtain ⟨w, hw⟩ := exists_infix_dropClauses h (hpT_mem_dropClauses h hi.le)
    (fun he => by have := hpT_inj he; omega)
  rcases hpT_arc (arc_of_infix_dropClauses h hd hw).1 with rfl | rfl
  · exact ⟨true, by simpa [hpRo] using hw⟩
  · exact ⟨false, by simpa [hpRo] using hw⟩

end Contract

/-! ### The assignment -/

theorem idxOf_getD_hamVars {φ : CNF} {i : ℕ} (hi : i < (hamVars φ).length) :
    (hamVars φ).idxOf ((hamVars φ).getD i 0) = i := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.Nodup.idxOf_getElem (List.nodup_dedup _) i hi

/-- SAT ≤ HAMPATH, backward direction for paths with normal detours: a Hamiltonian path of
Sipser's graph whose clause detours are normal yields a satisfying assignment (variable `i` is
true iff row `i` is run left to right). -/
theorem cnfSat_of_isHamPath {φ : CNF} {p : List ℕ}
    (h : IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)
      (hpT φ.length 0) (hpT φ.length (hamVars φ).length) p)
    (hd : DetoursNormal φ p) : CNFSat φ := by
  classical
  have hnd : (dropClauses φ p).Nodup := h.1.filter _
  refine ⟨fun x => decide ([hpT φ.length ((hamVars φ).idxOf x),
    hpR φ.length ((hamVars φ).idxOf x) 0] <:+: dropClauses φ p), ?_⟩
  intro C hC
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hC
  obtain ⟨i, hi, h1 | h1⟩ := hd j hj
  · have harc := hamEdges_of_infix h (pair_infix_of_triple h1).1
    rcases hpR_arc_clause (by omega) hj harc with ⟨-, hx⟩ | ⟨h3, -⟩
    · rw [List.getD_eq_getElem _ _ hj] at hx
      refine ⟨(hamVars φ).getD i 0, true, hx, ?_⟩
      beta_reduce
      rw [idxOf_getD_hamVars hi, decide_eq_true_iff]
      obtain ⟨b, hb⟩ := exists_top_succ h hi hd
      cases b
      · have hrun := row_run h hi hd hb (3 * φ.length - (3 * j + 2)) (by omega)
        simp only [hpRo, Bool.false_eq_true, ite_false] at hrun
        rw [show 3 * φ.length - (3 * φ.length - (3 * j + 2)) = 3 * j + 2 by omega,
          show 3 * φ.length - (3 * φ.length - (3 * j + 2) + 1) = 3 * j + 1 by omega] at hrun
        exact (not_pair_infix_swap hnd (infix_dropClauses h1 hj (le_hpR _ _ _) (le_hpR _ _ _))
          hrun).elim
      · simpa [hpRo] using hb
    · omega
  · have harc := hamEdges_of_infix h (pair_infix_of_triple h1).1
    rcases hpR_arc_clause (by omega) hj harc with ⟨h3, -⟩ | ⟨-, hx⟩
    · omega
    · rw [List.getD_eq_getElem _ _ hj] at hx
      refine ⟨(hamVars φ).getD i 0, false, hx, ?_⟩
      beta_reduce
      rw [idxOf_getD_hamVars hi, decide_eq_false_iff_not]
      intro hb
      have hrun := row_run (b := true) h hi hd (by simpa [hpRo] using hb) (3 * j + 1) (by omega)
      simp only [hpRo, ite_true] at hrun
      exact not_pair_infix_swap hnd hrun (infix_dropClauses h1 hj (le_hpR _ _ _) (le_hpR _ _ _))

end Cslib.Complexity.Karp
