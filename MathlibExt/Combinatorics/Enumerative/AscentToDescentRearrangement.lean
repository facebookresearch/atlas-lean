/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Chain

/-!
# Ascents and descents of rearranged words

The ascent-to-descent rearrangement takes each ascent of a word to a descent at the same
position, and these are all the descents of the rearranged word.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fuel-bounded ascent-to-descent rearrangement.** For a fuel $N \in \mathbb{N}$ and a word
$x = x_1 \cdots x_m$ over $\mathbb{N}$, the word $\nu_N(x)$ is defined by recursion on $N$:
$\nu_0(x) = x$, and $\nu_{N+1}(x) = x$ when $m \le 1$. For $m \ge 2$, let $A$ be the set of
positions of the least letter of $x$ and $B$ the set of positions of its greatest letter. If
$b \le a$ for all $a \in A$ and $b \in B$ (Case 1), put $i = \max A$ and $j = \min B$; then
$\nu_{N+1}(x) = \nu_N(x_1 \cdots x_{j-1})\, x_i\, \nu_N(x_{j+1} \cdots x_{i-1})\, x_j\,
\nu_N(x_{i+1} \cdots x_m)$. Otherwise (Case 2), let $i$ be the greatest $a \in A$ such that
$a < b$ for some $b \in B$, and $j$ the least $b \in B$ with $b > i$; then
$\nu_{N+1}(x) = \nu_N(x_1 \cdots x_{i-1})\, x_j\, \nu_N(x_{i+1} \cdots x_{j-1})\, x_i\,
\nu_N(x_{j+1} \cdots x_m)$.

Every recursive call is on a strictly shorter word, so fuel $N = m$ never runs out.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu` (Section 2). -/
public def ascentToDescentRearrangementAux : ℕ → List ℕ → List ℕ
  | 0, l => l
  | fuel + 1, l =>
    if l.length ≤ 1 then l else
      let mn := l.foldr min (l.headD 0)
      let mx := l.foldr max (l.headD 0)
      let amin := (List.range l.length).filter fun k => l.getD k 0 == mn
      let amax := (List.range l.length).filter fun k => l.getD k 0 == mx
      if amin.all fun a => amax.all fun b => b ≤ a then
        let i := amin.foldr max 0
        let j := amax.foldr min l.length
        ascentToDescentRearrangementAux fuel (l.take j) ++ [l.getD i 0] ++
          ascentToDescentRearrangementAux fuel ((l.drop (j + 1)).take (i - j - 1)) ++
          [l.getD j 0] ++ ascentToDescentRearrangementAux fuel (l.drop (i + 1))
      else
        let i := (amin.filter fun a => amax.any fun b => a < b).foldr max 0
        let j := (amax.filter fun b => i < b).foldr min l.length
        ascentToDescentRearrangementAux fuel (l.take i) ++ [l.getD j 0] ++
          ascentToDescentRearrangementAux fuel ((l.drop (i + 1)).take (j - i - 1)) ++
          [l.getD i 0] ++ ascentToDescentRearrangementAux fuel (l.drop (j + 1))

/-- **Ascent-to-descent rearrangement.** For a word $x = x_1 \cdots x_m$ over $\mathbb{N}$, the
ascent-to-descent rearrangement of $x$ is $\nu(x) = \nu_m(x)$, the fuel-bounded
ascent-to-descent rearrangement $\nu_N(x)$ with fuel $N = m$, the length of $x$.

Every recursive call of $\nu_N$ is on a strictly shorter word, so the fuel $m$ never runs out.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu` (Section 2). -/
public def ascentToDescentRearrangement (x : List ℕ) : List ℕ :=
  ascentToDescentRearrangementAux x.length x

/-- **Words of length at most one are fixed by the ascent-to-descent rearrangement.** Every word
$x$ over $\mathbb{N}$ of length at most $1$ satisfies $\nu(x) = x$, where $\nu$ is the
ascent-to-descent rearrangement.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Definition `nu`, Case 0. -/
public theorem ascentToDescentRearrangement_of_length_le_one {x : List ℕ} (hx : x.length ≤ 1) :
    ascentToDescentRearrangement x = x := by
  unfold ascentToDescentRearrangement
  cases h : x.length with
  | zero => rfl
  | succ k => simp only [ascentToDescentRearrangementAux, hx, ↓reduceIte]

/-- **Example of the ascent-to-descent rearrangement.** The ascent-to-descent rearrangement $\nu$
satisfies $\nu(1\,4\,1\,3\,4\,3\,1\,2\,1) = 4\,1\,4\,3\,1\,1\,2\,1\,3$, $\nu(1\,4) = 4\,1$ and
$\nu(3\,1\,2\,1) = 1\,2\,1\,3$.

The last two are the sub-steps of the first: $\nu(1\,4)$ falls under Case 2 of the definition
and $\nu(3\,1\,2\,1)$ under Case 1.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Example following Definition `nu`. -/
public theorem ascentToDescentRearrangement_example :
    ascentToDescentRearrangement [1, 4, 1, 3, 4, 3, 1, 2, 1] = [4, 1, 4, 3, 1, 1, 2, 1, 3] ∧
      ascentToDescentRearrangement [1, 4] = [4, 1] ∧
      ascentToDescentRearrangement [3, 1, 2, 1] = [1, 2, 1, 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

set_option quotPrecheck false in
/-- Ascent set (1-based positions) of a word `x : List ℕ`. -/
local notation "ascList" x:max =>
  Finset.image (· + 1)
    ((Finset.range (List.length x - 1)).filter fun i => List.getD x i 0 < List.getD x (i + 1) 0)

set_option quotPrecheck false in
/-- Descent set (1-based positions) of a word `x : List ℕ`. -/
local notation "desList" x:max =>
  Finset.image (· + 1)
    ((Finset.range (List.length x - 1)).filter fun i => List.getD x (i + 1) 0 < List.getD x i 0)

namespace ascList_eq_desList_ascentToDescentRearrangement

-- Pair the two words position by position. Successive pairs record the comparison
-- to prove, and both coordinates of each pair come from the original block.
private def edge (p q : ℕ × ℕ) : Prop := p.1 < q.1 ↔ q.2 < p.2

private def Matches (x y : List ℕ) : Prop :=
  ∃ z : List (ℕ × ℕ), z.map Prod.fst = x ∧ z.map Prod.snd = y ∧ z.IsChain edge ∧
    ∀ p ∈ z, p.2 ∈ x

private lemma matches_short {x : List ℕ} (hx : x.length ≤ 1) : Matches x x := by
  cases x with
  | nil => exact ⟨[], rfl, rfl, .nil, by simp⟩
  | cons a t =>
    obtain rfl : t = [] := List.length_eq_zero_iff.mp (by simpa using hx)
    exact ⟨[(a, a)], rfl, rfl, .singleton _, by simp⟩

private lemma chain_snoc {z : List (ℕ × ℕ)} {p : ℕ × ℕ} (hz : z.IsChain edge)
    (hp : ∀ t ∈ z, edge t p) : (z ++ [p]).IsChain edge := by
  apply hz.append (.singleton _)
  simpa using fun t ht => hp t (List.mem_of_mem_getLast? ht)

private lemma chain_cons {z : List (ℕ × ℕ)} {p : ℕ × ℕ} (hz : z.IsChain edge)
    (hp : ∀ t ∈ z, edge p t) : (p :: z).IsChain edge :=
  hz.cons fun t ht => hp t (List.mem_of_mem_head? ht)

private lemma matches_join {l m r l' m' r' : List ℕ} {a b : ℕ}
    (hl : Matches l l') (hm : Matches m m') (hr : Matches r r')
    (left : ∀ u ∈ l, ∀ v ∈ l, edge (u, v) (a, b))
    (mid : ∀ u ∈ m, ∀ v ∈ m, edge (a, b) (u, v) ∧ edge (u, v) (b, a))
    (right : ∀ u ∈ r, ∀ v ∈ r, edge (b, a) (u, v)) :
    Matches (l ++ [a] ++ m ++ [b] ++ r) (l' ++ [b] ++ m' ++ [a] ++ r') := by
  obtain ⟨L, rfl, rfl, hL, memL⟩ := hl
  obtain ⟨M, rfl, rfl, hM, memM⟩ := hm
  obtain ⟨R, rfl, rfl, hR, memR⟩ := hr
  refine ⟨L ++ [(a, b)] ++ M ++ [(b, a)] ++ R, by simp, by simp, ?_, ?_⟩
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [List.isChain_split, List.isChain_cons_split]
    refine ⟨chain_snoc hL fun t ht => left _ (List.mem_map_of_mem ht) _ (memL t ht),
      chain_cons (chain_snoc hM ?_) ?_, chain_cons hR fun t ht =>
        right _ (List.mem_map_of_mem ht) _ (memR t ht)⟩
    · exact fun t ht => (mid _ (List.mem_map_of_mem ht) _ (memM t ht)).2
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact (mid _ (List.mem_map_of_mem h) _ (memM t h)).1
      · obtain rfl := List.mem_singleton.mp h
        rfl
  · simp only [List.mem_append, List.mem_singleton]
    grind

-- The seeded folds used for both letters and positions attain their extrema
-- in the list with the seed adjoined.
private lemma fold_min_spec {α : Type*} [LinearOrder α] (l : List α) (d : α) :
    l.foldr min d ∈ d :: l ∧ ∀ x ∈ d :: l, l.foldr min d ≤ x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons] at *
    grind

private lemma fold_max_spec {α : Type*} [LinearOrder α] (l : List α) (d : α) :
    l.foldr max d ∈ d :: l ∧ ∀ x ∈ d :: l, x ≤ l.foldr max d :=
  fold_min_spec (α := αᵒᵈ) l d

private lemma getD_at {x : List ℕ} {i : ℕ} (hi : i < x.length) : x.getD i 0 = x[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private lemma split_at {x : List ℕ} {i j : ℕ} (hij : i < j) (hj : j < x.length) :
    x.take i ++ [x.getD i 0] ++ ((x.drop (i + 1)).take (j - i - 1)) ++
      [x.getD j 0] ++ x.drop (j + 1) = x := by
  have hj' : i + 1 + (j - i - 1) = j := by omega
  rw [getD_at (by omega), getD_at hj]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hdrop : (x.drop (i + 1)).drop (j - i - 1) = x.drop j := by rw [List.drop_drop, hj']
  rw [List.getElem_cons_drop, ← hdrop, List.take_append_drop,
    List.getElem_cons_drop, List.take_append_drop]

private lemma matches_swap {x : List ℕ} {i j : ℕ} (hij : i < j) (hj : j < x.length)
    (f : List ℕ → List ℕ) (ih : ∀ s, s.length < x.length → Matches s (f s))
    (left : ∀ k < i, ∀ t < i, edge (x.getD k 0, x.getD t 0) (x.getD i 0, x.getD j 0))
    (mid : ∀ k, i < k → k < j → ∀ t, i < t → t < j →
      edge (x.getD i 0, x.getD j 0) (x.getD k 0, x.getD t 0) ∧
      edge (x.getD k 0, x.getD t 0) (x.getD j 0, x.getD i 0))
    (right : ∀ k, j < k → k < x.length → ∀ t, j < t → t < x.length →
      edge (x.getD j 0, x.getD i 0) (x.getD k 0, x.getD t 0)) :
    Matches x (f (x.take i) ++ [x.getD j 0] ++ f ((x.drop (i + 1)).take (j - i - 1)) ++
      [x.getD i 0] ++ f (x.drop (j + 1))) := by
  have pre {u} (hu : u ∈ x.take i) : ∃ k < i, x.getD k 0 = u := by
    obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp hu
    exact ⟨k, by omega, getD_at (by omega)⟩
  have inner {u} (hu : u ∈ (x.drop (i + 1)).take (j - i - 1)) :
      ∃ k, i < k ∧ k < j ∧ x.getD k 0 = u := by
    obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp hu
    refine ⟨i + 1 + k, by omega, by omega, ?_⟩
    rw [List.getElem_drop, getD_at (by omega)]
  have post {u} (hu : u ∈ x.drop (j + 1)) : ∃ k, j < k ∧ k < x.length ∧ x.getD k 0 = u := by
    obtain ⟨k, hk, rfl⟩ := List.mem_drop_iff_getElem.mp hu
    exact ⟨j + 1 + k, by omega, by omega, getD_at (by omega)⟩
  conv_lhs => rw [← split_at hij hj]
  apply matches_join (ih _ (by simp; omega)) (ih _ (by simp; omega)) (ih _ (by simp; omega))
  · intro u hu v hv
    obtain ⟨k, hk, rfl⟩ := pre hu
    obtain ⟨t, ht, rfl⟩ := pre hv
    exact left k hk t ht
  · intro u hu v hv
    obtain ⟨k, hk, hkj, rfl⟩ := inner hu
    obtain ⟨t, ht, htj, rfl⟩ := inner hv
    exact mid k hk hkj t ht htj
  · intro u hu v hv
    obtain ⟨k, hk, hkx, rfl⟩ := post hu
    obtain ⟨t, ht, htx, rfl⟩ := post hv
    exact right k hk hkx t ht htx

private lemma fold_min_mem {α : Type*} [LinearOrder α] {l : List α} {d : α}
    (h : ∃ a ∈ l, a ≤ d) : l.foldr min d ∈ l := by
  obtain ⟨a, ha, had⟩ := h
  obtain ⟨hm, hle⟩ := fold_min_spec l d
  rcases List.mem_cons.mp hm with he | hm
  · have := hle a (.tail _ ha)
    have : l.foldr min d = a := le_antisymm this (he.symm ▸ had)
    rwa [this]
  · exact hm

private lemma fold_max_mem {α : Type*} [LinearOrder α] {l : List α} {d : α}
    (h : ∃ a ∈ l, d ≤ a) : l.foldr max d ∈ l :=
  fold_min_mem (α := αᵒᵈ) h

private lemma matches_aux (fuel : ℕ) (x : List ℕ) (hlen : x.length ≤ fuel) :
    Matches x (ascentToDescentRearrangementAux fuel x) := by
  induction fuel generalizing x with
  | zero => exact matches_short (by omega)
  | succ fuel ih =>
    rw [ascentToDescentRearrangementAux]
    by_cases hs : x.length ≤ 1
    · simpa only [ite_eq_left hs] using matches_short hs
    rw [ite_eq_right hs]
    let mn := x.foldr min (x.headD 0)
    let mx := x.foldr max (x.headD 0)
    let pos (a : ℕ) := (List.range x.length).filter fun k => x.getD k 0 == a
    have mem_pos {a k} : k ∈ pos a ↔ k < x.length ∧ x.getD k 0 = a := by simp [pos]
    have head_mem : x.headD 0 ∈ x := by cases x <;> simp_all
    have occurs {a : ℕ} (ha : a ∈ x) : ∃ k, k ∈ pos a := by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      exact ⟨k, mem_pos.mpr ⟨hk, getD_at hk⟩⟩
    obtain ⟨u, hu⟩ := occurs (fold_min_mem ⟨_, head_mem, le_rfl⟩ : mn ∈ x)
    obtain ⟨v, hv⟩ := occurs (fold_max_mem ⟨_, head_mem, le_rfl⟩ : mx ∈ x)
    have bounds (k : ℕ) (hk : k < x.length) : mn ≤ x.getD k 0 ∧ x.getD k 0 ≤ mx := by
      rw [getD_at hk]
      have hm : x[k] ∈ x.headD 0 :: x := .tail _ (List.getElem_mem hk)
      exact ⟨(fold_min_spec ..).2 _ hm, (fold_max_spec ..).2 _ hm⟩
    have recurse (s : List ℕ) (h : s.length < x.length) :
        Matches s (ascentToDescentRearrangementAux fuel s) := ih s (by omega)
    change Matches x (if (pos mn).all (fun a => (pos mx).all fun b => b ≤ a) then _ else _)
    split
    next h =>
      -- All maxima precede all minima. Only the prefix and suffix exclude both extrema.
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      let i := (pos mn).foldr max 0
      let j := (pos mx).foldr min x.length
      have hi : i ∈ pos mn := fold_max_mem ⟨u, hu, Nat.zero_le _⟩
      have hj : j ∈ pos mx := fold_min_mem ⟨v, hv, (mem_pos.mp hv).1.le⟩
      obtain ⟨hiLen, hiVal⟩ := mem_pos.mp hi
      obtain ⟨hjLen, hjVal⟩ := mem_pos.mp hj
      have hiMax (k) (hk : k ∈ pos mn) : k ≤ i := (fold_max_spec ..).2 _ (.tail _ hk)
      have hjMin (k) (hk : k ∈ pos mx) : j ≤ k := (fold_min_spec ..).2 _ (.tail _ hk)
      have hne : mn ≠ mx := by
        intro he
        have h0 := bounds 0 (by omega)
        have h1 := bounds 1 (by omega)
        have := h 0 (mem_pos.mpr ⟨by omega, by omega⟩) 1 (mem_pos.mpr ⟨by omega, by omega⟩)
        omega
      have hji : j < i := lt_of_le_of_ne (h i hi j hj) fun he =>
        hne (hiVal.symm.trans (he ▸ hjVal))
      have strict (k : ℕ) (hk : k < x.length) (ho : k < j ∨ i < k) :
          mn < x.getD k 0 ∧ x.getD k 0 < mx := by
        obtain ⟨hm, hM⟩ := bounds k hk
        constructor
        · apply lt_of_le_of_ne hm
          intro he
          have hmin := mem_pos.mpr ⟨hk, he.symm⟩
          have := h k hmin j hj
          have := hiMax k hmin
          omega
        · apply lt_of_le_of_ne hM
          intro he
          have hmax := mem_pos.mpr ⟨hk, he⟩
          have := h i hi k hmax
          have := hjMin k hmax
          omega
      apply matches_swap hji hiLen _ recurse
      · intro k hk t ht
        exact ⟨fun _ => hiVal ▸ (strict t (by omega) (.inl ht)).1,
          fun _ => hjVal ▸ (strict k (by omega) (.inl hk)).2⟩
      · intro k _ hk t _ ht
        have := bounds k (by omega)
        have := bounds t (by omega)
        simp only [edge, hiVal, hjVal]
        omega
      · intro k hk hkx t ht htx
        exact ⟨fun _ => hjVal ▸ (strict t htx (.inr ht)).2,
          fun _ => hiVal ▸ (strict k hkx (.inr hk)).1⟩
    next h =>
      -- Choose the last minimum followed by a maximum, then the first such maximum.
      simp only [List.all_eq_true, decide_eq_true_eq, not_forall, exists_prop, not_le] at h
      obtain ⟨a, ha, b, hb, hab⟩ := h
      let candidates := (pos mn).filter fun a => (pos mx).any fun b => a < b
      have candidate {k} : k ∈ candidates ↔ k ∈ pos mn ∧ ∃ t ∈ pos mx, k < t := by
        simp [candidates]
      let i := candidates.foldr max 0
      have hi : i ∈ candidates := fold_max_mem ⟨a, candidate.mpr ⟨ha, b, hb, hab⟩, Nat.zero_le _⟩
      obtain ⟨hiMin, c, hc, hic⟩ := candidate.mp hi
      let after := (pos mx).filter fun t => i < t
      have after_mem {t} : t ∈ after ↔ t ∈ pos mx ∧ i < t := by simp [after]
      let j := after.foldr min x.length
      have hj : j ∈ after := fold_min_mem ⟨c, after_mem.mpr ⟨hc, hic⟩, (mem_pos.mp hc).1.le⟩
      obtain ⟨hjMax, hij⟩ := after_mem.mp hj
      obtain ⟨hjLen, hjVal⟩ := mem_pos.mp hjMax
      have hiVal := (mem_pos.mp hiMin).2
      have strict (k : ℕ) (hik : i < k) (hkj : k < j) : mn < x.getD k 0 ∧ x.getD k 0 < mx := by
        have hk : k < x.length := by omega
        obtain ⟨hm, hM⟩ := bounds k hk
        constructor
        · apply lt_of_le_of_ne hm
          intro he
          have hmem := candidate.mpr ⟨mem_pos.mpr ⟨hk, he.symm⟩, j, hjMax, hkj⟩
          exact hik.not_ge ((fold_max_spec ..).2 _ (.tail 0 hmem))
        · apply lt_of_le_of_ne hM
          intro he
          have hmem := after_mem.mpr ⟨mem_pos.mpr ⟨hk, he⟩, hik⟩
          exact hkj.not_ge ((fold_min_spec ..).2 _ (.tail x.length hmem))
      apply matches_swap hij hjLen _ recurse
      · intro k hk t ht
        have := bounds k (by omega)
        have := bounds t (by omega)
        simp only [edge, hiVal, hjVal]
        omega
      · intro k hk hkj t ht htj
        have := strict k hk hkj
        have := strict t ht htj
        simp only [edge, hiVal, hjVal]
        omega
      · intro k _ hk t _ ht
        have := bounds k hk
        have := bounds t ht
        simp only [edge, hiVal, hjVal]
        omega

end ascList_eq_desList_ascentToDescentRearrangement

open ascList_eq_desList_ascentToDescentRearrangement in
/-- **Ascents of a word are the descents of its rearrangement.** For a word
$x = x_1 \cdots x_m$ over $\mathbb{N}$, let the ascent set $\mathrm{Asc}(x)$ be the set of
$i \in \{1, \dots, m - 1\}$ with $x_i < x_{i+1}$, and the descent set $\mathrm{Des}(x)$ the set
of $i \in \{1, \dots, m - 1\}$ with $x_i > x_{i+1}$. Then every word $x$ over $\mathbb{N}$
satisfies $\mathrm{Asc}(x) = \mathrm{Des}(\nu(x))$, where $\nu$ is the ascent-to-descent
rearrangement.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 11 (`jis-2024-24.8.6-lem-11`). -/
public theorem ascList_eq_desList_ascentToDescentRearrangement (x : List ℕ) :
    ascList x = desList (ascentToDescentRearrangement x) := by
  obtain ⟨z, hx, hy, hz, _⟩ := matches_aux x.length x le_rfl
  change z.map Prod.snd = ascentToDescentRearrangement x at hy
  rw [← hy, ← hx]
  apply congrArg (Finset.image (· + 1))
  simp only [List.length_map]
  apply Finset.filter_congr
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have h₀ : i < z.length := by omega
  have h₁ : i + 1 < z.length := by omega
  simpa only [edge, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h₀,
    List.getElem?_eq_getElem h₁, Option.map_some, Option.getD_some] using hz.getElem i h₁

end

end MetaMathlibExt
