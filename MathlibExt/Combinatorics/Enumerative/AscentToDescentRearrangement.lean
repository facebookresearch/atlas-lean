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
import Mathlib.Data.List.GetD

/-!
# Ascents and descents of rearranged words

The ascent-to-descent rearrangement of a finite word over $\mathbb{N}$ takes each ascent
of the word to a descent at the same position, and these are all the descents of the
rearranged word. The map is injective: its output determines the two positions at
which the extreme letters were exchanged, and the intervening blocks are inverted
recursively. Constant words are determined by their content and length alone.

## References

* Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
  Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
  Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, pp. 1–34,
  Definition 7 and Lemmas 11 and 13.
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
    Matches (l ++ a :: (m ++ b :: r)) (l' ++ b :: (m' ++ a :: r')) := by
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

private lemma split_at {x : List ℕ} {i j : ℕ} (hij : i < j) (hj : j < x.length) :
    x.take i ++ [x.getD i 0] ++ ((x.drop (i + 1)).take (j - i - 1)) ++
      [x.getD j 0] ++ x.drop (j + 1) = x := by
  have hj' : i + 1 + (j - i - 1) = j := by omega
  rw [List.getD_eq_getElem _ 0 (by omega), List.getD_eq_getElem _ 0 hj]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hdrop : (x.drop (i + 1)).drop (j - i - 1) = x.drop j := by rw [List.drop_drop, hj']
  rw [List.getElem_cons_drop, ← hdrop, List.take_append_drop,
    List.getElem_cons_drop, List.take_append_drop]

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

private def middle (x : List ℕ) (i j : ℕ) : List ℕ :=
  (x.drop (i + 1)).take (j - i - 1)

private lemma getD_drop_add (x : List ℕ) (i k : ℕ) :
    (x.drop i).getD k 0 = x.getD (i + k) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

private lemma getD_mem_middle {x : List ℕ} {i j k : ℕ} (hik : i < k) (hkj : k < j)
    (hk : k < x.length) : x.getD k 0 ∈ middle x i j := by
  have hs : i + 1 + (k - (i + 1)) = k := by omega
  refine List.mem_take_iff_getElem.mpr ⟨k - (i + 1), by simp [List.length_drop]; omega, ?_⟩
  rw [← List.getD_eq_getElem _ 0 (by simp [List.length_drop]; omega), getD_drop_add, hs]

-- All occurrences of `a` precede all occurrences of `b` (for distinct letters).
private def Separated (a b : ℕ) (x : List ℕ) : Prop :=
  x.Pairwise fun u v => u ≠ b ∨ v ≠ a

private lemma separated_iff {a b : ℕ} {x : List ℕ} : Separated a b x ↔
    ∀ i j, i < j → j < x.length → x.getD i 0 = b → x.getD j 0 ≠ a := by
  rw [Separated, List.pairwise_iff_getElem]
  constructor
  · intro h i j hij hj hiVal hjVal
    have hrel := h i j (hij.trans hj) hj hij
    rw [← List.getD_eq_getElem x 0 (hij.trans hj), ← List.getD_eq_getElem x 0 hj,
      hiVal, hjVal] at hrel
    exact hrel.elim (fun e => e rfl) (fun e => e rfl)
  · intro h i j hi hj hij
    by_cases e : x[i] = b
    · exact Or.inr (fun hjVal => h i j hij hj ((List.getD_eq_getElem x 0 hi).trans e)
        ((List.getD_eq_getElem x 0 hj).trans hjVal))
    · exact Or.inl e

private lemma separated_of_absent {a b : ℕ} {x : List ℕ} (h : a ∉ x ∨ b ∉ x) :
    Separated a b x := by
  rw [separated_iff]
  intro i j hij hj hiVal hjVal
  rcases h with ha | hb
  · exact ha (hjVal ▸ (List.getD_eq_getElem x 0 hj).symm ▸ List.getElem_mem hj)
  · have hi := hij.trans hj
    exact hb (hiVal ▸ (List.getD_eq_getElem x 0 hi).symm ▸ List.getElem_mem hi)

private def swapSplit (f : List ℕ → List ℕ) (x : List ℕ) (i j : ℕ) : List ℕ :=
  f (x.take i) ++ x.getD j 0 :: (f (middle x i j) ++ x.getD i 0 :: f (x.drop (j + 1)))

private inductive ForwardCut (x : List ℕ) (lo hi i j : ℕ) : Prop
  | separated (left : x.getD i 0 = hi) (right : x.getD j 0 = lo)
      (order : Separated hi lo x)
      (outside : ∀ a, a ∈ x.take i ∨ a ∈ x.drop (j + 1) → lo < a ∧ a < hi)
  | crossing (left : x.getD i 0 = lo) (right : x.getD j 0 = hi)
      (inside : ∀ a ∈ middle x i j, lo < a ∧ a < hi)
      (suffix : Separated hi lo (x.drop (j + 1)))

private structure SwapStep (x : List ℕ) where
  i : ℕ
  j : ℕ
  lo : ℕ
  hi : ℕ
  ordered : i < j
  inside : j < x.length
  bounds : ∀ a ∈ x, lo ≤ a ∧ a ≤ hi
  cut : ForwardCut x lo hi i j

private lemma SwapStep.extrema_mem {x} (s : SwapStep x) : s.lo ∈ x ∧ s.hi ∈ x := by
  have hl := List.getElem_mem (s.ordered.trans s.inside)
  have hr := List.getElem_mem s.inside
  rw [← List.getD_eq_getElem _ 0 (s.ordered.trans s.inside)] at hl
  rw [← List.getD_eq_getElem _ 0 s.inside] at hr
  cases s.cut with
  | separated hl' hr' _ _ => exact ⟨hr' ▸ hr, hl' ▸ hl⟩
  | crossing hl' hr' _ _ => exact ⟨hl' ▸ hl, hr' ▸ hr⟩

private lemma SwapStep.shorter {x} (s : SwapStep x) :
    (x.take s.i).length < x.length ∧ (middle x s.i s.j).length < x.length ∧
      (x.drop (s.j + 1)).length < x.length := by
  have := s.ordered
  have := s.inside
  simp only [middle, List.length_take, List.length_drop]
  omega

-- The selector facts are shared by the ascent-set and injectivity proofs.
private lemma swapStep (fuel : ℕ) (x : List ℕ) (hs : ¬ x.length ≤ 1) :
    ∃ s : SwapStep x, ascentToDescentRearrangementAux (fuel + 1) x =
      swapSplit (ascentToDescentRearrangementAux fuel) x s.i s.j := by
  let mn := x.foldr min (x.headD 0)
  let mx := x.foldr max (x.headD 0)
  let pos (a : ℕ) := (List.range x.length).filter fun k => x.getD k 0 == a
  have mem_pos {a k} : k ∈ pos a ↔ k < x.length ∧ x.getD k 0 = a := by simp [pos]
  have head_mem : x.headD 0 ∈ x := by cases x <;> simp_all
  have occurs {a : ℕ} (ha : a ∈ x) : ∃ k, k ∈ pos a := by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    exact ⟨k, mem_pos.mpr ⟨hk, List.getD_eq_getElem _ 0 hk⟩⟩
  obtain ⟨u, hu⟩ := occurs (fold_min_mem ⟨_, head_mem, le_rfl⟩ : mn ∈ x)
  obtain ⟨v, hv⟩ := occurs (fold_max_mem ⟨_, head_mem, le_rfl⟩ : mx ∈ x)
  have bounds (a : ℕ) (ha : a ∈ x) : mn ≤ a ∧ a ≤ mx :=
    ⟨(fold_min_spec ..).2 _ (.tail _ ha), (fold_max_spec ..).2 _ (.tail _ ha)⟩
  have bounds_at (k : ℕ) (hk : k < x.length) : mn ≤ x.getD k 0 ∧ x.getD k 0 ≤ mx := by
    rw [List.getD_eq_getElem _ 0 hk]
    exact bounds _ (List.getElem_mem hk)
  rw [ascentToDescentRearrangementAux, ite_eq_right hs]
  change ∃ s : SwapStep x, (if (pos mn).all (fun a => (pos mx).all fun b => b ≤ a)
    then _ else _) = _
  by_cases h : (pos mn).all (fun a => (pos mx).all fun b => b ≤ a) = true
  · simp only [ite_eq_left h]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    let i := (pos mx).foldr min x.length
    let j := (pos mn).foldr max 0
    have hi : i ∈ pos mx := fold_min_mem ⟨v, hv, (mem_pos.mp hv).1.le⟩
    have hj : j ∈ pos mn := fold_max_mem ⟨u, hu, Nat.zero_le _⟩
    obtain ⟨hiLen, hiVal⟩ := mem_pos.mp hi
    obtain ⟨hjLen, hjVal⟩ := mem_pos.mp hj
    have hne : mn ≠ mx := by
      intro he
      have h0 := bounds_at 0 (by omega)
      have h1 := bounds_at 1 (by omega)
      have := h 0 (mem_pos.mpr ⟨by omega, by omega⟩) 1 (mem_pos.mpr ⟨by omega, by omega⟩)
      omega
    have hij : i < j := lt_of_le_of_ne (h j hj i hi) fun he =>
      hne (hjVal.symm.trans (he ▸ hiVal))
    have strict (k : ℕ) (hk : k < x.length) (ho : k < i ∨ j < k) :
        mn < x.getD k 0 ∧ x.getD k 0 < mx := by
      obtain ⟨hm, hM⟩ := bounds_at k hk
      constructor
      · apply lt_of_le_of_ne hm
        intro he
        have hmin := mem_pos.mpr ⟨hk, he.symm⟩
        have := h k hmin i hi
        have := (fold_max_spec (pos mn) 0).2 k (.tail _ hmin)
        omega
      · apply lt_of_le_of_ne hM
        intro he
        have hmax := mem_pos.mpr ⟨hk, he⟩
        have := h j hj k hmax
        have := (fold_min_spec (pos mx) x.length).2 k (.tail _ hmax)
        omega
    refine ⟨⟨i, j, mn, mx, hij, hjLen, bounds, .separated hiVal hjVal ?_ ?_⟩, ?_⟩
    · rw [separated_iff]
      intro k t hkt ht hkVal htVal
      exact hkt.not_ge (h k (mem_pos.mpr ⟨hkt.trans ht, hkVal⟩) t (mem_pos.mpr ⟨ht, htVal⟩))
    · rintro a (ha | ha)
      · obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp ha
        simpa only [List.getD_eq_getElem x 0 (n := k) (by omega)] using
          strict k (by omega) (.inl (by omega))
      · obtain ⟨k, hk, rfl⟩ := List.mem_drop_iff_getElem.mp ha
        simpa only [List.getD_eq_getElem x 0 (n := j + 1 + k) (by omega)]
          using strict (j + 1 + k) (by omega) (.inr (by omega))
    · simp only [swapSplit, middle, List.append_assoc, List.cons_append, List.nil_append]
      rfl
  · simp only [ite_eq_right h]
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
    have last_min {k t : ℕ} (hk : k ∈ pos mn) (ht : t ∈ pos mx) (hkt : k < t) : k ≤ i :=
      (fold_max_spec candidates 0).2 k (.tail _ (candidate.mpr ⟨hk, t, ht, hkt⟩))
    refine ⟨⟨i, j, mn, mx, hij, hjLen, bounds, .crossing hiVal hjVal ?_ ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp ha
      have hkj : i + 1 + k < j := by omega
      have hkx : i + 1 + k < x.length := by omega
      rw [List.getElem_drop, ← List.getD_eq_getElem x 0 hkx]
      obtain ⟨hm, hM⟩ := bounds_at (i + 1 + k) hkx
      exact ⟨lt_of_le_of_ne hm fun e => by
          have := last_min (mem_pos.mpr ⟨hkx, e.symm⟩) hjMax hkj
          omega,
        lt_of_le_of_ne hM fun e => hkj.not_ge ((fold_min_spec after x.length).2 _
          (.tail _ (after_mem.mpr ⟨mem_pos.mpr ⟨hkx, e⟩, by omega⟩)))⟩
    · rw [separated_iff]
      intro k t hkt ht hkVal htVal
      simp only [List.length_drop] at ht
      have hkx : j + 1 + k < x.length := by omega
      have htx : j + 1 + t < x.length := by omega
      rw [getD_drop_add] at hkVal htVal
      have := last_min (mem_pos.mpr ⟨hkx, hkVal⟩) (mem_pos.mpr ⟨htx, htVal⟩) (by omega)
      omega
    · simp only [swapSplit, middle, List.append_assoc, List.cons_append, List.nil_append]
      rfl

private lemma matches_aux (fuel : ℕ) (x : List ℕ) (hlen : x.length ≤ fuel) :
    Matches x (ascentToDescentRearrangementAux fuel x) := by
  induction fuel generalizing x with
  | zero => exact matches_short (by omega)
  | succ fuel ih =>
    by_cases hs : x.length ≤ 1
    · simpa only [ascentToDescentRearrangementAux, ite_eq_left hs] using matches_short hs
    obtain ⟨s, hswap⟩ := swapStep fuel x hs
    obtain ⟨hl, hm, hr⟩ := s.shorter
    rw [hswap, swapSplit]
    conv_lhs => rw [← split_at s.ordered s.inside]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply matches_join (ih (x.take s.i) (by omega)) (ih (middle x s.i s.j) (by omega))
      (ih (x.drop (s.j + 1)) (by omega))
    · intro u hu v hv
      have hu' := s.bounds u (List.mem_of_mem_take hu)
      have hv' := s.bounds v (List.mem_of_mem_take hv)
      cases s.cut with
      | separated hl hr _ h =>
        have := h u (.inl hu)
        have := h v (.inl hv)
        simp only [edge, hl, hr]
        omega
      | crossing hl hr _ _ => simp only [edge, hl, hr]; omega
    · intro u hu v hv
      have hu' := s.bounds u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
      have hv' := s.bounds v (List.mem_of_mem_drop (List.mem_of_mem_take hv))
      cases s.cut with
      | separated hl hr _ _ => simp only [edge, hl, hr]; omega
      | crossing hl hr h _ =>
        have := h u hu
        have := h v hv
        simp only [edge, hl, hr]
        omega
    · intro u hu v hv
      have hu' := s.bounds u (List.mem_of_mem_drop hu)
      have hv' := s.bounds v (List.mem_of_mem_drop hv)
      cases s.cut with
      | separated hl hr _ h =>
        have := h u (.inr hu)
        have := h v (.inr hv)
        simp only [edge, hl, hr]
        omega
      | crossing hl hr _ _ => simp only [edge, hl, hr]; omega

private lemma perm_aux (fuel : ℕ) (x : List ℕ) :
    x.Perm (ascentToDescentRearrangementAux fuel x) := by
  induction fuel generalizing x with
  | zero => exact .refl _
  | succ fuel ih =>
    by_cases hs : x.length ≤ 1
    · rw [ascentToDescentRearrangementAux, ite_eq_left hs]
    obtain ⟨s, hswap⟩ := swapStep fuel x hs
    rw [hswap, swapSplit]
    conv_lhs => rw [← split_at s.ordered s.inside]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    let a := x.getD s.i 0
    let b := x.getD s.j 0
    let m := middle x s.i s.j
    let r := x.drop (s.j + 1)
    have hswap : (a :: (m ++ b :: r)).Perm (b :: (m ++ a :: r)) :=
      (List.perm_middle.cons a).trans ((List.Perm.swap b a (m ++ r)).trans
        (List.perm_middle.cons b).symm)
    exact (hswap.append_left _).trans ((ih _).append_cons _ ((ih _).append_cons _ (ih _)))

private lemma SwapStep.slices {fuel x y} (s : SwapStep x)
    (hswap : y = swapSplit (ascentToDescentRearrangementAux fuel) x s.i s.j) :
    let f := ascentToDescentRearrangementAux fuel
    y.take s.i = f (x.take s.i) ∧ y.getD s.i 0 = x.getD s.j 0 ∧
      middle y s.i s.j = f (middle x s.i s.j) ∧ y.getD s.j 0 = x.getD s.i 0 ∧
      y.drop (s.j + 1) = f (x.drop (s.j + 1)) := by
  dsimp only
  let l := ascentToDescentRearrangementAux fuel (x.take s.i)
  let m := ascentToDescentRearrangementAux fuel (middle x s.i s.j)
  let r := ascentToDescentRearrangementAux fuel (x.drop (s.j + 1))
  let a := x.getD s.j 0
  let b := x.getD s.i 0
  have hL : l.length = s.i := by
    rw [← (perm_aux fuel _).length_eq, List.length_take,
      Nat.min_eq_left (s.ordered.trans s.inside).le]
  have hM : m.length = s.j - s.i - 1 := by
    have := s.inside
    rw [← (perm_aux fuel _).length_eq, middle, List.length_take, List.length_drop, Nat.min_eq_left]
    omega
  have hjoin : y = l ++ a :: (m ++ b :: r) := hswap
  have hpre : y = (l ++ [a]) ++ (m ++ b :: r) := by simpa using hjoin
  have hpost : y = ((l ++ [a]) ++ m) ++ b :: r := by simpa using hjoin
  have hpreLen : (l ++ [a]).length = s.i + 1 := by simp [hL]
  have hmidLen : ((l ++ [a]) ++ m).length = s.j := by
    have := s.ordered
    simp only [List.length_append, hpreLen, hM]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hjoin, List.take_left' hL]
  · rw [hjoin, List.getD_append_right _ _ _ _ hL.le, hL, Nat.sub_self]
    rfl
  · rw [middle, hpre, List.drop_left' hpreLen, List.take_left' hM]
  · rw [hpost, List.getD_append_right _ _ _ _ hmidLen.le, hmidLen, Nat.sub_self]
    rfl
  · have h : (((l ++ [a]) ++ m) ++ [b]).length = s.j + 1 := by
      simp only [List.length_append, hmidLen, List.length_singleton]
    rw [show y = (((l ++ [a]) ++ m) ++ [b]) ++ r by simpa using hjoin, List.drop_left' h]

-- With the given bounds, the order of the two extremes reverses when there is no crossing.
private lemma separates_aux (fuel : ℕ) (x : List ℕ) (hlen : x.length ≤ fuel) {lo hi : ℕ}
    (hlt : lo < hi) (bounds : ∀ a ∈ x, lo ≤ a ∧ a ≤ hi) (hsep : Separated hi lo x) :
    Separated lo hi (ascentToDescentRearrangementAux fuel x) := by
  induction fuel generalizing x with
  | zero =>
    rw [ascentToDescentRearrangementAux, separated_iff]
    exact fun i j hij hj => False.elim (by omega)
  | succ fuel ih =>
    by_cases hs : x.length ≤ 1
    · rw [ascentToDescentRearrangementAux, ite_eq_left hs, separated_iff]
      exact fun i j hij hj => False.elim (by omega)
    by_cases hlo : lo ∈ x
    swap
    · exact separated_of_absent (.inl (fun h => hlo ((perm_aux _ _).mem_iff.mpr h)))
    by_cases hhi : hi ∈ x
    swap
    · exact separated_of_absent (.inr (fun h => hhi ((perm_aux _ _).mem_iff.mpr h)))
    obtain ⟨s, hswap⟩ := swapStep fuel x hs
    obtain ⟨hsl, hsh⟩ := s.extrema_mem
    have el : s.lo = lo := le_antisymm (s.bounds _ hlo).1 (bounds _ hsl).1
    have eh : s.hi = hi := le_antisymm (bounds _ hsh).2 (s.bounds _ hhi).2
    cases s.cut with
    | crossing hl hr _ _ =>
      exact (separated_iff.mp hsep s.i s.j s.ordered s.inside (hl.trans el) (hr.trans eh)).elim
    | separated hl hr _ hout =>
      let f := ascentToDescentRearrangementAux fuel
      have hm : (middle x s.i s.j).Sublist x :=
        (List.take_sublist ..).trans (List.drop_sublist ..)
      have hmid : Separated lo hi (f (middle x s.i s.j)) :=
        ih _ (by have := s.shorter.2.1; omega) (fun a ha => bounds a (hm.subset ha))
          (List.Pairwise.sublist hm hsep)
      have outside {a} (ha : a ∈ f (x.take s.i) ∨ a ∈ f (x.drop (s.j + 1))) :
          a ≠ hi ∧ a ≠ lo := by
        obtain ⟨h₁, h₂⟩ := hout a (ha.imp ((perm_aux fuel _).mem_iff.mpr)
          ((perm_aux fuel _).mem_iff.mpr))
        exact ⟨ne_of_lt (h₂.trans_eq eh), ne_of_gt (el.symm.trans_lt h₁)⟩
      have hL : Separated lo hi (f (x.take s.i)) :=
        separated_of_absent (.inr fun h => (outside (.inl h)).1 rfl)
      have hR : Separated lo hi (f (x.drop (s.j + 1))) :=
        separated_of_absent (.inl fun h => (outside (.inr h)).2 rfl)
      rw [hswap, swapSplit, hl, hr, el, eh]
      exact List.pairwise_append.mpr ⟨hL, List.pairwise_cons.mpr ⟨fun _ _ => .inl hlt.ne,
        List.pairwise_append.mpr ⟨hmid, List.pairwise_cons.mpr
          ⟨fun _ hv => .inr (outside (.inr hv)).2, hR⟩, fun _ _ _ hv => .inr (by
            rcases List.mem_cons.mp hv with rfl | hv
            · exact hlt.ne'
            · exact (outside (.inr hv)).2)⟩⟩, fun _ hu _ _ => .inl (outside (.inl hu)).1⟩

-- In the output the cuts are either the first minimum and last maximum, or the
-- last maximum with a later minimum and the first minimum strictly after it.
private inductive InverseCut (lo hi : ℕ) (y : List ℕ) (i j : ℕ) : Prop
  | separated (order : Separated lo hi y) (left : y.getD i 0 = lo) (right : y.getD j 0 = hi)
      (first : ∀ k < i, y.getD k 0 ≠ lo)
      (last : ∀ k, j < k → k < y.length → y.getD k 0 ≠ hi)
  | crossing (left : y.getD i 0 = hi) (right : y.getD j 0 = lo)
      (first : ∀ k, i < k → k < j → y.getD k 0 ≠ lo)
      (last : ∀ k t, i < k → k < t → t < y.length → y.getD k 0 = hi → y.getD t 0 ≠ lo)

private lemma SwapStep.inverseCut {fuel x} (s : SwapStep x)
    (hswap : ascentToDescentRearrangementAux (fuel + 1) x =
      swapSplit (ascentToDescentRearrangementAux fuel) x s.i s.j)
    (hlen : x.length ≤ fuel + 1) (hlt : s.lo < s.hi) :
    InverseCut s.lo s.hi (ascentToDescentRearrangementAux (fuel + 1) x) s.i s.j := by
  obtain ⟨htake, hleft, hmid, hright, hdrop⟩ := s.slices hswap
  have hlen' := (perm_aux (fuel + 1) x).length_eq
  have hij := s.ordered
  have hj := s.inside
  cases s.cut with
  | separated hl hr hsep hout =>
    refine .separated (separates_aux _ _ hlen hlt s.bounds hsep)
      (hleft.trans hr) (hright.trans hl) ?_ ?_
    · intro k hk hval
      have hk' : k < (ascentToDescentRearrangementAux (fuel + 1) x).length := by omega
      have hmem : s.lo ∈ (ascentToDescentRearrangementAux (fuel + 1) x).take s.i := by
        exact List.mem_take_iff_getElem.mpr
          ⟨k, by omega, (List.getD_eq_getElem _ 0 hk').symm.trans hval⟩
      rw [htake, ← (perm_aux fuel _).mem_iff] at hmem
      exact (lt_irrefl _) (hout _ (.inl hmem)).1
    · intro k hk hk' hval
      have hmem : s.hi ∈ (ascentToDescentRearrangementAux (fuel + 1) x).drop (s.j + 1) := by
        refine List.mem_drop_iff_getElem.mpr ⟨k - (s.j + 1), by omega, ?_⟩
        rwa [← List.getD_eq_getElem _ 0 (n := s.j + 1 + (k - (s.j + 1))) (by omega),
          show s.j + 1 + (k - (s.j + 1)) = k by omega]
      rw [hdrop, ← (perm_aux fuel _).mem_iff] at hmem
      exact (lt_irrefl _) (hout _ (.inr hmem)).2
  | crossing hl hr hin hsep =>
    refine .crossing (hleft.trans hr) (hright.trans hl) ?_ ?_
    · intro k hk hkj hval
      have hk' : k < (ascentToDescentRearrangementAux (fuel + 1) x).length := by omega
      have hmem := hval ▸ getD_mem_middle hk hkj hk'
      rw [hmid, ← (perm_aux fuel _).mem_iff] at hmem
      exact (lt_irrefl _) (hin _ hmem).1
    · have htail : Separated s.lo s.hi
          ((ascentToDescentRearrangementAux (fuel + 1) x).drop (s.j + 1)) := by
        rw [hdrop]
        exact separates_aux _ _ (by have := s.shorter.2.2; omega) hlt
          (fun a ha => s.bounds a (List.mem_of_mem_drop ha)) hsep
      intro k t hik hkt ht hkVal htVal
      by_cases hkj : k ≤ s.j
      · rcases hkj.lt_or_eq with hkj | rfl
        · have hmem := hkVal ▸ getD_mem_middle hik hkj (hkt.trans ht)
          rw [hmid, ← (perm_aux fuel _).mem_iff] at hmem
          exact (lt_irrefl _) (hin _ hmem).2
        · exact hlt.ne ((hright.trans hl).symm.trans hkVal)
      · apply separated_iff.mp htail (k - (s.j + 1)) (t - (s.j + 1)) (by omega) (by simp; omega)
        · rwa [getD_drop_add, show s.j + 1 + (k - (s.j + 1)) = k by omega]
        · rwa [getD_drop_add, show s.j + 1 + (t - (s.j + 1)) = t by omega]

private lemma InverseCut.unique {lo hi : ℕ} {y : List ℕ} {i j k t : ℕ}
    (hij : i < j) (hjy : j < y.length) (hkt : k < t) (hty : t < y.length)
    (h : InverseCut lo hi y i j) (h' : InverseCut lo hi y k t) : i = k ∧ j = t := by
  cases h with
  | separated hs hi hj hf hl =>
    cases h' with
    | separated _ hk ht hf' hl' =>
      exact ⟨le_antisymm (le_of_not_gt fun e => hf _ e hk) (le_of_not_gt fun e => hf' _ e hi),
        le_antisymm (le_of_not_gt fun e => hl' _ e hjy hj) (le_of_not_gt fun e => hl _ e hty ht)⟩
    | crossing hk ht _ _ => exact (separated_iff.mp hs k t hkt hty hk ht).elim
  | crossing hi hj hf hl =>
    cases h' with
    | separated hs _ _ _ _ => exact (separated_iff.mp hs i j hij hjy hi hj).elim
    | crossing hk ht hf' hl' =>
      have e : i = k := le_antisymm (le_of_not_gt fun e => hl' i j e hij hjy hi hj)
        (le_of_not_gt fun e => hl k t e hkt hty hk ht)
      subst k
      exact ⟨rfl, le_antisymm (le_of_not_gt fun e => hf t hkt e ht)
        (le_of_not_gt fun e => hf' j hij e hj)⟩

private lemma injective_aux (fuel : ℕ) {x z : List ℕ} (hx : x.length ≤ fuel) (hz : z.length ≤ fuel)
    (he : ascentToDescentRearrangementAux fuel x = ascentToDescentRearrangementAux fuel z) :
    x = z := by
  induction fuel generalizing x z with
  | zero => exact he
  | succ fuel ih =>
    have hp : x.Perm z := (perm_aux (fuel + 1) x).trans (he ▸ (perm_aux (fuel + 1) z).symm)
    have hlen := hp.length_eq
    by_cases hs : x.length ≤ 1
    · have hs' : z.length ≤ 1 := hlen ▸ hs
      simpa only [ascentToDescentRearrangementAux, ite_eq_left hs, ite_eq_left hs'] using he
    have hs' : ¬ z.length ≤ 1 := hlen ▸ hs
    obtain ⟨s, hswap⟩ := swapStep fuel x hs
    obtain ⟨t, hswap'⟩ := swapStep fuel z hs'
    obtain ⟨hsl, hsh⟩ := s.extrema_mem
    obtain ⟨htl, hth⟩ := t.extrema_mem
    have elo : s.lo = t.lo := le_antisymm (s.bounds _ (hp.mem_iff.mpr htl)).1
      (t.bounds _ (hp.mem_iff.mp hsl)).1
    have ehi : s.hi = t.hi := le_antisymm (t.bounds _ (hp.mem_iff.mp hsh)).2
      (s.bounds _ (hp.mem_iff.mpr hth)).2
    have hle := (s.bounds _ hsl).2
    by_cases hlt : s.lo < s.hi
    swap
    · have constant (a) (ha : a ∈ x) : a = s.lo := by have := s.bounds a ha; omega
      rw [List.eq_replicate_of_mem constant, List.eq_replicate_of_mem
        (fun a ha => constant a (hp.mem_iff.mpr ha)), hlen]
    have hlt' : t.lo < t.hi := elo ▸ ehi ▸ hlt
    have hsCut := s.inverseCut hswap hx hlt
    have htCut := t.inverseCut hswap' hz hlt'
    rw [← elo, ← ehi, ← he] at htCut
    have hpOut := (perm_aux (fuel + 1) x).length_eq
    obtain ⟨ei, ej⟩ := hsCut.unique s.ordered (hpOut ▸ s.inside) t.ordered
      (by have := t.inside; omega) htCut
    obtain ⟨xl, xm, xr⟩ := s.shorter
    obtain ⟨zl, zm, zr⟩ := t.shorter
    obtain ⟨hxL, hxi, hxM, hxj, hxR⟩ := s.slices hswap
    obtain ⟨hzL, hzi, hzM, hzj, hzR⟩ := t.slices hswap'
    simp only [← ei, ← ej, ← he] at hzL hzi hzM hzj hzR
    have eqL := ih (show (x.take s.i).length ≤ fuel by omega)
      (show (z.take s.i).length ≤ fuel by rw [ei]; omega) (hxL.symm.trans hzL)
    have eqM := ih (show (middle x s.i s.j).length ≤ fuel by omega)
      (show (middle z s.i s.j).length ≤ fuel by rw [ei, ej]; omega) (hxM.symm.trans hzM)
    have eqR := ih (show (x.drop (s.j + 1)).length ≤ fuel by omega)
      (show (z.drop (s.j + 1)).length ≤ fuel by rw [ej]; omega) (hxR.symm.trans hzR)
    calc
      x = x.take s.i ++ [x.getD s.i 0] ++ middle x s.i s.j ++ [x.getD s.j 0] ++ x.drop (s.j + 1) :=
        (split_at s.ordered s.inside).symm
      _ = z.take t.i ++ [z.getD t.i 0] ++ middle z t.i t.j ++
          [z.getD t.j 0] ++ z.drop (t.j + 1) := by
        rw [← ei, ← ej, eqL, eqM, eqR, hxj.symm.trans hzj, hxi.symm.trans hzi]
      _ = z := split_at t.ordered t.inside

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

open ascList_eq_desList_ascentToDescentRearrangement in
/-- **The ascent-to-descent rearrangement is injective.** The ascent-to-descent rearrangement
$\nu$ is injective on finite words over $\mathbb{N}$: if $\nu(x) = \nu(x')$, then $x = x'$.

Since $\nu$ rearranges letters, this is the same as injectivity of $\nu$ on the rearrangements of
each fixed word.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6,
Lemma 13 (`jis-2024-24.8.6-lem-13`). -/
public theorem ascentToDescentRearrangement_injective :
    Function.Injective ascentToDescentRearrangement := by
  intro x y h
  change ascentToDescentRearrangementAux x.length x =
    ascentToDescentRearrangementAux y.length y at h
  have hlen : x.length = y.length := (perm_aux x.length x).length_eq.trans
    ((congrArg List.length h).trans (perm_aux y.length y).length_eq.symm)
  rw [← hlen] at h
  exact injective_aux x.length le_rfl hlen.ge h

end

end MetaMathlibExt
