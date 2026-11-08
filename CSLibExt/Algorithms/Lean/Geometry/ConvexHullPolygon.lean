/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.ConvexHull

/-!
# Convex hull by Andrew's monotone chain: the upper chain and the hull

The second half of Andrew's algorithm (de Berg, Cheong, van Kreveld and Overmars, *Computational
Geometry*, third edition, Section 1.1, Algorithm `CONVEXHULL`): the upper chain is the same scan
as the lower chain (`CSLibExt.Algorithms.Lean.Geometry.ConvexHull`) run over the points from
right to left, and the hull is the lower chain followed by the upper chain without its two
endpoints, a counterclockwise polygon starting at the first point.

The upper chain's properties come from the lower chain's by the point reflection `p ↦ -p`, which
reverses the `(x, y)` order and leaves every cross product `cross (b - a) (c - a)` unchanged, so
the scan of the reversed list is the reflected scan of the reflected list (`upperHull_eq`).

For points sorted strictly by `(x, y)`:

* `upperHull_*`: the upper chain is a sublist of the reversed input from the last point to the
  first, turns strictly left, and has every input point on or left of each edge.
* `convexHull_left_of_edges`: for at least two points, every input point is on or left of every
  edge of the closed polygon (including the two edges that close it), so the polygon contains
  every point; `convexHull_subset` says its vertices are input points.
* `convexHull_turnsLeft`: if the points are not all collinear, the closed polygon turns strictly
  left at every vertex (`TurnsLeft (H ++ H.take 2)`), so it is strictly convex. Inside each chain
  this is the chain's own property; at the two vertices where the chains meet, a non-strict turn
  would put every point on one line (`junction_turn_left`).

## Cost model

As for the lower chain, one unit per orientation test: at most `2 n` per chain, `4 n` in total
(`convexHull_time_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

open Cslib.Algorithms.Lean TimeM
open scoped List

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The upper chain of points sorted by `(x, y)`: the lower-chain scan over the reversed list,
from the last point back to the first. -/
def upperHull (ps : List (𝕜 × 𝕜)) : TimeM ℕ (List (𝕜 × 𝕜)) := lowerHull ps.reverse

/-- The hull of points sorted by `(x, y)`, counterclockwise from the first point: the lower chain,
then the upper chain without its endpoints. -/
def convexHull (ps : List (𝕜 × 𝕜)) : TimeM ℕ (List (𝕜 × 𝕜)) := do
  let lower ← lowerHull ps
  let upper ← upperHull ps
  pure (lower ++ upper.tail.dropLast)

/-! ## Point reflection -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem cross_neg_sub (a b c : 𝕜 × 𝕜) :
    cross (-a - -b) (-c - -b) = cross (a - b) (c - b) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]; ring

private theorem toLex_neg_lt_iff {a b : 𝕜 × 𝕜} : toLex (-a) < toLex (-b) ↔ toLex b < toLex a := by
  simp only [Prod.Lex.toLex_lt_toLex, Prod.fst_neg, Prod.snd_neg, neg_lt_neg_iff, neg_inj]
  constructor <;> rintro (h | ⟨h1, h2⟩) <;> first | exact Or.inl h | exact Or.inr ⟨h1.symm, h2⟩

omit [IsStrictOrderedRing 𝕜] in
private theorem popNonLeft_neg (p : 𝕜 × 𝕜) (st : List (𝕜 × 𝕜)) :
    (popNonLeft (-p) (st.map Neg.neg)).ret = (popNonLeft p st).ret.map Neg.neg ∧
      (popNonLeft (-p) (st.map Neg.neg)).time = (popNonLeft p st).time := by
  induction st with
  | nil => exact ⟨rfl, rfl⟩
  | cons a rest ih =>
      match rest, ih with
      | [], _ => exact ⟨rfl, rfl⟩
      | b :: r, ih =>
          simp only [List.map_cons] at ih ⊢
          simp only [popNonLeft, ret_bind, time_bind, time_tick, cross_neg_sub]
          split
          · exact ⟨ih.1, by rw [ih.2]⟩
          · exact ⟨rfl, rfl⟩

omit [IsStrictOrderedRing 𝕜] in
private theorem chainScan_neg : ∀ (st ps : List (𝕜 × 𝕜)),
    (chainScan (st.map Neg.neg) (ps.map Neg.neg)).ret = (chainScan st ps).ret.map Neg.neg ∧
      (chainScan (st.map Neg.neg) (ps.map Neg.neg)).time = (chainScan st ps).time
  | st, [] => ⟨rfl, rfl⟩
  | st, p :: ps => by
      simp only [List.map_cons, chainScan, ret_bind, time_bind]
      obtain ⟨h1, h2⟩ := popNonLeft_neg p st
      rw [h1, h2]
      have := chainScan_neg (p :: (popNonLeft p st).ret) ps
      simp only [List.map_cons] at this
      exact ⟨this.1, by rw [this.2]⟩

omit [IsStrictOrderedRing 𝕜] in
/-- The upper chain is the reflected lower chain of the reflected, reversed input. -/
theorem upperHull_eq (ps : List (𝕜 × 𝕜)) :
    (upperHull ps).ret = (lowerHull (ps.reverse.map Neg.neg)).ret.map Neg.neg ∧
      (upperHull ps).time = (lowerHull (ps.reverse.map Neg.neg)).time := by
  have hps : ps.reverse = (ps.reverse.map Neg.neg).map Neg.neg := by
    rw [List.map_map]; simp
  obtain ⟨h1, h2⟩ := chainScan_neg [] (ps.reverse.map Neg.neg)
  simp only [List.map_nil] at h1 h2
  simp only [upperHull, lowerHull, ret_bind, ret_pure, time_bind, time_pure]
  rw [hps, h1, h2, List.map_reverse]
  simp

/-! ## The upper chain -/

private theorem sorted_reflect {ps : List (𝕜 × 𝕜)} (hs : ps.Pairwise fun a b => toLex a < toLex b) :
    (ps.reverse.map Neg.neg).Pairwise fun a b => toLex a < toLex b := by
  rw [List.pairwise_map]
  exact (List.pairwise_reverse.2 hs).imp fun h => toLex_neg_lt_iff.2 h

/-- The upper chain is a sublist of the reversed input. -/
theorem upperHull_sublist (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b) :
    (upperHull ps).ret <+ ps.reverse := by
  rw [(upperHull_eq ps).1]
  have := (lowerHull_sublist _ (sorted_reflect hs)).map Neg.neg
  rwa [List.map_map, show Neg.neg ∘ Neg.neg = (id : 𝕜 × 𝕜 → 𝕜 × 𝕜) from funext neg_neg,
    List.map_id] at this

/-- The upper chain starts at the last input point. -/
theorem upperHull_head? (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b) :
    (upperHull ps).ret.head? = ps.getLast? := by
  rw [(upperHull_eq ps).1, List.head?_map, lowerHull_head? _ (sorted_reflect hs), List.head?_map,
    Option.map_map, show Neg.neg ∘ Neg.neg = (id : 𝕜 × 𝕜 → 𝕜 × 𝕜) from funext neg_neg,
    Option.map_id, List.head?_reverse]
  rfl

/-- The upper chain ends at the first input point. -/
theorem upperHull_getLast? (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b) :
    (upperHull ps).ret.getLast? = ps.head? := by
  rw [(upperHull_eq ps).1, List.getLast?_map, lowerHull_getLast? _ (sorted_reflect hs),
    List.getLast?_map, Option.map_map,
    show Neg.neg ∘ Neg.neg = (id : 𝕜 × 𝕜 → 𝕜 × 𝕜) from funext neg_neg, Option.map_id,
    List.getLast?_reverse]
  rfl

/-- The upper chain turns strictly left at every inner vertex. -/
theorem upperHull_turn_left (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b)
    (i : ℕ) (h : i + 2 < (upperHull ps).ret.length) :
    0 < cross ((upperHull ps).ret[i + 1] - (upperHull ps).ret[i])
      ((upperHull ps).ret[i + 2] - (upperHull ps).ret[i]) := by
  have hU := (upperHull_eq ps).1
  have h' : i + 2 < (lowerHull (ps.reverse.map Neg.neg)).ret.length := by
    rw [hU, List.length_map] at h; exact h
  have key := lowerHull_turn_left _ (sorted_reflect hs) i h'
  simp only [hU, List.getElem_map]
  rw [cross_neg_sub]
  exact key

/-- Every input point is on or left of every edge of the upper chain. -/
theorem upperHull_left_of_edges (ps : List (𝕜 × 𝕜))
    (hs : ps.Pairwise fun a b => toLex a < toLex b) {s : 𝕜 × 𝕜} (hsps : s ∈ ps) :
    (upperHull ps).ret.IsChain fun a b => 0 ≤ cross (b - a) (s - a) := by
  have hmem : -s ∈ ps.reverse.map Neg.neg := List.mem_map.2 ⟨s, List.mem_reverse.2 hsps, rfl⟩
  have key := lowerHull_left_of_edges _ (sorted_reflect hs) hmem
  rw [(upperHull_eq ps).1, List.isChain_map]
  refine key.imp fun {a b} h => ?_
  have := cross_neg_sub b a (-s)
  rw [neg_neg] at this
  rwa [this]

omit [IsStrictOrderedRing 𝕜] in
/-- The upper chain makes at most `2 n` orientation tests. -/
theorem upperHull_time_le (ps : List (𝕜 × 𝕜)) : (upperHull ps).time ≤ 2 * ps.length := by
  have := lowerHull_time_le (ps.reverse.map Neg.neg)
  rwa [List.length_map, List.length_reverse, ← (upperHull_eq ps).2] at this

/-! ## The hull -/

omit [IsStrictOrderedRing 𝕜] in
private theorem convexHull_ret (ps : List (𝕜 × 𝕜)) :
    (convexHull ps).ret = (lowerHull ps).ret ++ (upperHull ps).ret.tail.dropLast := rfl

/-- The hull's vertices are input points. -/
theorem convexHull_subset (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b) :
    ∀ c ∈ (convexHull ps).ret, c ∈ ps := by
  intro c hc
  rw [convexHull_ret] at hc
  rcases List.mem_append.1 hc with h | h
  · exact (lowerHull_sublist ps hs).subset h
  · exact List.mem_reverse.1 ((upperHull_sublist ps hs).subset
      (List.mem_of_mem_tail (List.mem_of_mem_dropLast h)))

/-- For at least two points, every input point is on or left of every edge of the closed hull
polygon `H ++ [H.head]`: the polygon contains all the points. -/
theorem convexHull_left_of_edges (ps : List (𝕜 × 𝕜))
    (hs : ps.Pairwise fun a b => toLex a < toLex b) (hlen : 2 ≤ ps.length) {s : 𝕜 × 𝕜}
    (hsps : s ∈ ps) :
    ((convexHull ps).ret ++ (convexHull ps).ret.take 1).IsChain fun a b =>
      0 ≤ cross (b - a) (s - a) := by
  obtain ⟨f, l, mid, hps⟩ : ∃ f l mid, ps = f :: (mid ++ [l]) := by
    match ps, hlen with
    | f :: rest, hlen =>
        rcases List.eq_nil_or_concat rest with h | ⟨mid, l, h⟩
        · subst h; simp at hlen
        · exact ⟨f, l, mid, by rw [h, List.concat_eq_append]⟩
  have hfl : f ≠ l := by
    intro hfl
    have := List.rel_of_pairwise_cons (hps ▸ hs) (List.mem_append_right mid List.mem_cons_self)
    rw [hfl] at this
    exact lt_irrefl _ this
  have hLh : (lowerHull ps).ret.head? = some f := by rw [lowerHull_head? ps hs, hps]; rfl
  have hLl : (lowerHull ps).ret.getLast? = some l := by
    rw [lowerHull_getLast? ps hs, hps, List.getLast?_cons, List.getLast?_append]; simp
  have hUh : (upperHull ps).ret.head? = some l := by
    rw [upperHull_head? ps hs, hps, List.getLast?_cons, List.getLast?_append]; simp
  have hUl : (upperHull ps).ret.getLast? = some f := by rw [upperHull_getLast? ps hs, hps]; rfl
  have hLc := lowerHull_left_of_edges ps hs hsps
  have hUc := upperHull_left_of_edges ps hs hsps
  rw [convexHull_ret]
  generalize (lowerHull ps).ret = L at hLh hLl hLc ⊢
  generalize (upperHull ps).ret = U at hUh hUl hUc ⊢
  rcases L with _ | ⟨x, L'⟩
  · simp at hLh
  simp only [List.head?_cons, Option.some.injEq] at hLh
  subst hLh
  rcases U with _ | ⟨y, _ | ⟨u, U'⟩⟩
  · simp at hUh
  · simp only [List.head?_cons, Option.some.injEq] at hUh
    simp only [List.getLast?_singleton, Option.some.injEq] at hUl
    exact absurd (hUl.symm.trans hUh) hfl
  simp only [List.head?_cons, Option.some.injEq] at hUh
  subst hUh
  have hclose : (x :: L' ++ (y :: u :: U').tail.dropLast) ++
      (x :: L' ++ (y :: u :: U').tail.dropLast).take 1 = (x :: L') ++ (u :: U') := by
    have hlast : (u :: U').getLast (List.cons_ne_nil _ _) = x := by
      have h := hUl
      rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at h
      exact Option.some.inj h
    simp only [List.tail_cons, List.cons_append, List.take_succ_cons, List.take_zero,
      List.append_assoc]
    congr 2
    conv_rhs => rw [← List.dropLast_append_getLast (List.cons_ne_nil u U'), hlast]
  rw [hclose, List.isChain_append]
  rw [List.isChain_cons_cons] at hUc
  refine ⟨hLc, hUc.2, ?_⟩
  intro a ha b hb
  rw [hLl] at ha
  simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at ha hb
  subst ha hb
  exact hUc.1

omit [IsStrictOrderedRing 𝕜] in
/-- The hull costs at most `4 n` orientation tests. -/
theorem convexHull_time_le (ps : List (𝕜 × 𝕜)) : (convexHull ps).time ≤ 4 * ps.length := by
  have h1 := lowerHull_time_le ps
  have h2 := upperHull_time_le ps
  simp only [convexHull, time_bind, time_pure]
  omega

/-! ## Strict convexity of the polygon -/

/-- Every consecutive triple turns strictly left. -/
def TurnsLeft : List (𝕜 × 𝕜) → Prop
  | a :: b :: c :: rest => 0 < cross (b - a) (c - a) ∧ TurnsLeft (b :: c :: rest)
  | _ => True

omit [IsStrictOrderedRing 𝕜] in
theorem turnsLeft_iff_getElem : ∀ {l : List (𝕜 × 𝕜)},
    TurnsLeft l ↔ ∀ i (h : i + 2 < l.length), 0 < cross (l[i + 1] - l[i]) (l[i + 2] - l[i])
  | [] => by simp [TurnsLeft]
  | [_] => by simp [TurnsLeft]
  | [_, _] => by simp [TurnsLeft]
  | a :: b :: c :: rest => by
      rw [TurnsLeft, turnsLeft_iff_getElem]
      constructor
      · rintro ⟨h0, h⟩ i hi
        cases i with
        | zero => exact h0
        | succ i => exact h i (by simp at hi ⊢; omega)
      · intro h
        exact ⟨h 0 (by simp), fun i hi => h (i + 1) (by simp at hi ⊢; omega)⟩

omit [IsStrictOrderedRing 𝕜] in
/-- Two turn sequences that overlap in two points glue into one. -/
private theorem turnsLeft_glue : ∀ (A : List (𝕜 × 𝕜)) {x y : 𝕜 × 𝕜} {B : List (𝕜 × 𝕜)},
    TurnsLeft (A ++ [x, y]) → TurnsLeft ([x, y] ++ B) → TurnsLeft (A ++ [x, y] ++ B)
  | [], _, _, _, _, h => by simpa using h
  | [a], x, y, B, h1, h2 => by
      simp only [List.cons_append, List.nil_append] at h1 h2 ⊢
      exact ⟨h1.1, h2⟩
  | a :: b :: A, x, y, B, h1, h2 => by
      obtain ⟨c, rest, hc⟩ : ∃ c rest, A ++ [x, y] = c :: rest := by
        cases A with
        | nil => exact ⟨x, [y], rfl⟩
        | cons c A => exact ⟨c, A ++ [x, y], rfl⟩
      have ih := turnsLeft_glue (b :: A) (B := B) (by
        have : TurnsLeft (a :: b :: (A ++ [x, y])) := by simpa using h1
        rw [hc] at this
        rw [List.cons_append, hc]
        exact this.2) h2
      have h1' : TurnsLeft (a :: b :: (A ++ [x, y])) := by simpa using h1
      rw [hc] at h1'
      have e : A ++ [x, y] ++ B = c :: (rest ++ B) := by rw [hc]; rfl
      simp only [List.cons_append] at ih ⊢
      rw [e] at ih ⊢
      exact ⟨h1'.1, ih⟩

/-- Parallel vectors, one lexicographically positive and one negative, point in opposite
directions: their dot product is negative. -/
private theorem dot_neg_of_parallel {d e : 𝕜 × 𝕜} (hpar : cross d e = 0)
    (hd : toLex (0 : 𝕜 × 𝕜) < toLex d) (he : toLex e < toLex (0 : 𝕜 × 𝕜)) :
    d.1 * e.1 + d.2 * e.2 < 0 := by
  simp only [cross] at hpar
  rw [Prod.Lex.toLex_lt_toLex] at hd he
  simp only [Prod.fst_zero, Prod.snd_zero] at hd he
  rcases hd with hd | ⟨hd1, hd2⟩
  · rcases he with he | ⟨he1, he2⟩
    · have key : d.1 * (d.1 * e.1 + d.2 * e.2) = e.1 * (d.1 ^ 2 + d.2 ^ 2) := by
        linear_combination d.2 * hpar
      have hpos : 0 < d.1 ^ 2 + d.2 ^ 2 := by positivity
      have hneg : e.1 * (d.1 ^ 2 + d.2 ^ 2) < 0 := mul_neg_of_neg_of_pos he hpos
      by_contra hc
      push Not at hc
      have := mul_nonneg hd.le hc
      linarith
    · rw [he1, zero_mul, sub_zero] at hpar
      exact absurd (mul_eq_zero.1 hpar) (by rintro (h | h) <;> linarith)
  · rw [← hd1] at hpar ⊢
    have he1 : e.1 = 0 := by
      have : e.1 * d.2 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith
    have he2 : e.2 < 0 := by
      rcases he with he | ⟨_, he⟩
      · linarith
      · exact he
    rw [he1]
    nlinarith

private theorem lex_sub_pos {a b : 𝕜 × 𝕜} (h : toLex a < toLex b) :
    toLex (0 : 𝕜 × 𝕜) < toLex (b - a) := by
  rw [Prod.Lex.toLex_lt_toLex] at h ⊢
  simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_sub, Prod.snd_sub, sub_pos]
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨by rw [h1, sub_self], h2⟩

private theorem lex_sub_neg {a b : 𝕜 × 𝕜} (h : toLex a < toLex b) :
    toLex (a - b) < toLex (0 : 𝕜 × 𝕜) := by
  rw [Prod.Lex.toLex_lt_toLex] at h ⊢
  simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_sub, Prod.snd_sub, sub_neg]
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨by rw [h1, sub_self], h2⟩

/-- Where two chains meet: if every point is on or left of the edges `ℓ → r` and `r → u`, with
`ℓ` and `u` both before `r` or both after it, then `ℓ → r → u` turns strictly left unless all the
points are collinear. -/
private theorem junction_turn_left {ps : List (𝕜 × 𝕜)} {ℓ r u : 𝕜 × 𝕜}
    (hside : (toLex ℓ < toLex r ∧ toLex u < toLex r) ∨ (toLex r < toLex ℓ ∧ toLex r < toLex u))
    (h1 : ∀ s ∈ ps, 0 ≤ cross (r - ℓ) (s - ℓ)) (h2 : ∀ s ∈ ps, 0 ≤ cross (u - r) (s - r))
    (hu : u ∈ ps) (hncol : ∃ a ∈ ps, ∃ b ∈ ps, ∃ c ∈ ps, cross (b - a) (c - a) ≠ 0) :
    0 < cross (r - ℓ) (u - ℓ) := by
  rcases lt_or_eq_of_le (h1 u hu) with h | h
  · exact h
  exfalso
  set d := r - ℓ with hd
  set e := u - r with he
  have hpar : cross d e = 0 := by
    have : cross d e = cross d (u - ℓ) - cross d d := by
      simp only [hd, he, cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [this, ← h]; simp [cross]
  have hdot : d.1 * e.1 + d.2 * e.2 < 0 := by
    rcases hside with ⟨hl, hu'⟩ | ⟨hl, hu'⟩
    · exact dot_neg_of_parallel hpar (lex_sub_pos hl) (lex_sub_neg hu')
    · have h' := dot_neg_of_parallel (d := -d) (e := -e)
        (by simp only [cross, Prod.fst_neg, Prod.snd_neg] at hpar ⊢; linarith)
        (by rw [hd, neg_sub]; exact lex_sub_pos hl) (by rw [he, neg_sub]; exact lex_sub_neg hu')
      simp only [Prod.fst_neg, Prod.snd_neg] at h'
      linarith
  have hd0 : 0 < d.1 ^ 2 + d.2 ^ 2 := by
    by_contra h0
    have h1' : d.1 = 0 := by nlinarith
    have h2' : d.2 = 0 := by nlinarith
    rw [h1', h2'] at hdot
    simp at hdot
  -- every point lies on the line through `ℓ` and `r`
  have hline : ∀ s ∈ ps, cross d (s - ℓ) = 0 := by
    intro s hs
    have hid : (d.1 ^ 2 + d.2 ^ 2) * cross e (s - r) - (d.1 * e.1 + d.2 * e.2) * cross d (s - r) =
        -(cross d e) * (d.1 * (s - r).1 + d.2 * (s - r).2) := by
      simp only [cross]; ring
    have hsr : cross d (s - r) = cross d (s - ℓ) := by
      simp only [hd, cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hpar, neg_zero, zero_mul, hsr] at hid
    have hA := h1 s hs
    have hB := h2 s hs
    have hC := mul_nonneg hd0.le hB
    have hD : (d.1 * e.1 + d.2 * e.2) * cross d (s - ℓ) ≥ 0 := by linarith
    have hE : cross d (s - ℓ) ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_neg_of_neg_of_pos hdot hc
      linarith
    exact le_antisymm hE hA
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := hncol
  apply habc
  have hx : cross d (b - a) = 0 := by
    have e1 := hline b hb
    have e2 := hline a ha
    have : cross d (b - a) = cross d (b - ℓ) - cross d (a - ℓ) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [this, e1, e2, sub_zero]
  have hy : cross d (c - a) = 0 := by
    have e1 := hline c hc
    have e2 := hline a ha
    have : cross d (c - a) = cross d (c - ℓ) - cross d (a - ℓ) := by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    rw [this, e1, e2, sub_zero]
  have i1 : cross (b - a) (c - a) * d.1 =
      cross d (c - a) * (b - a).1 - cross d (b - a) * (c - a).1 := by simp only [cross]; ring
  have i2 : cross (b - a) (c - a) * d.2 =
      cross d (c - a) * (b - a).2 - cross d (b - a) * (c - a).2 := by simp only [cross]; ring
  rw [hx, hy] at i1 i2
  simp only [zero_mul, sub_zero] at i1 i2
  by_contra hne
  rcases mul_eq_zero.1 i1 with h | h
  · exact hne h
  rcases mul_eq_zero.1 i2 with h' | h'
  · exact hne h'
  rw [h, h'] at hd0
  simp at hd0

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem exists_append_pair {L : List (𝕜 × 𝕜)} {f l : 𝕜 × 𝕜} (hh : L.head? = some f)
    (hl : L.getLast? = some l) (hfl : f ≠ l) : ∃ A ℓ, L = A ++ [ℓ, l] := by
  rcases List.eq_nil_or_concat L with rfl | ⟨L₁, l', rfl⟩
  · simp at hh
  have hl' : l' = l := by simpa using hl
  subst hl'
  rcases List.eq_nil_or_concat L₁ with rfl | ⟨A, ℓ, rfl⟩
  · simp only [List.concat_eq_append, List.nil_append, List.head?_cons,
      Option.some.injEq] at hh
    exact absurd hh.symm hfl
  · exact ⟨A, ℓ, by simp⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem exists_cons_cons {L : List (𝕜 × 𝕜)} {f l : 𝕜 × 𝕜} (hh : L.head? = some f)
    (hl : L.getLast? = some l) (hfl : f ≠ l) : ∃ q L₂, L = f :: q :: L₂ := by
  match L, hh, hl with
  | [x], hh, hl =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      exact absurd (hh.symm.trans hl) hfl
  | x :: y :: r, hh, _ =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact ⟨y, r, by rw [hh]⟩

/-- If the points are not all collinear, the hull polygon is strictly convex: written cyclically
as `H ++ H.take 2`, every consecutive triple turns strictly left, including at the two vertices
where the lower and upper chains meet. -/
theorem convexHull_turnsLeft (ps : List (𝕜 × 𝕜))
    (hs : ps.Pairwise fun a b => toLex a < toLex b)
    (hncol : ∃ a ∈ ps, ∃ b ∈ ps, ∃ c ∈ ps, cross (b - a) (c - a) ≠ 0) :
    TurnsLeft ((convexHull ps).ret ++ (convexHull ps).ret.take 2) := by
  -- at least two distinct points: the first `f` and the last `l`
  obtain ⟨f, l, mid, hps⟩ : ∃ f l mid, ps = f :: (mid ++ [l]) := by
    obtain ⟨a, ha, b, hb, c, hc, habc⟩ := hncol
    match ps, ha, hb with
    | [x], ha, hb =>
        rw [List.mem_singleton] at ha hb
        subst ha hb
        exact absurd (by simp [cross]) habc
    | f :: y :: rest, _, _ =>
        rcases List.eq_nil_or_concat (y :: rest) with h | ⟨mid, l, h⟩
        · simp at h
        · exact ⟨f, l, mid, by rw [h, List.concat_eq_append]⟩
  have hfl : f ≠ l := by
    intro hfl
    have := List.rel_of_pairwise_cons (hps ▸ hs) (List.mem_append_right mid List.mem_cons_self)
    rw [hfl] at this
    exact lt_irrefl _ this
  have hLh : (lowerHull ps).ret.head? = some f := by rw [lowerHull_head? ps hs, hps]; rfl
  have hLl : (lowerHull ps).ret.getLast? = some l := by
    rw [lowerHull_getLast? ps hs, hps, List.getLast?_cons, List.getLast?_append]; simp
  have hUh : (upperHull ps).ret.head? = some l := by
    rw [upperHull_head? ps hs, hps, List.getLast?_cons, List.getLast?_append]; simp
  have hUl : (upperHull ps).ret.getLast? = some f := by rw [upperHull_getLast? ps hs, hps]; rfl
  have hLs : (lowerHull ps).ret.Pairwise fun a b => toLex a < toLex b :=
    hs.sublist (lowerHull_sublist ps hs)
  have hUs : (upperHull ps).ret.Pairwise fun a b => toLex b < toLex a :=
    (List.pairwise_reverse.2 hs).sublist (upperHull_sublist ps hs)
  have hLm : ∀ x ∈ (lowerHull ps).ret, x ∈ ps := fun x hx => (lowerHull_sublist ps hs).subset hx
  have hUm : ∀ x ∈ (upperHull ps).ret, x ∈ ps := fun x hx =>
    List.mem_reverse.1 ((upperHull_sublist ps hs).subset hx)
  have hLt : TurnsLeft (lowerHull ps).ret := turnsLeft_iff_getElem.2 (lowerHull_turn_left ps hs)
  have hUt : TurnsLeft (upperHull ps).ret := turnsLeft_iff_getElem.2 (upperHull_turn_left ps hs)
  have hLc := fun s (hsps : s ∈ ps) => lowerHull_left_of_edges ps hs hsps
  have hUc := fun s (hsps : s ∈ ps) => upperHull_left_of_edges ps hs hsps
  rw [convexHull_ret]
  generalize (lowerHull ps).ret = L at hLh hLl hLs hLm hLt hLc ⊢
  generalize (upperHull ps).ret = U at hUh hUl hUs hUm hUt hUc ⊢
  obtain ⟨q, L₂, hLq⟩ := exists_cons_cons hLh hLl hfl
  obtain ⟨A, ℓ, hLA⟩ := exists_append_pair hLh hLl hfl
  obtain ⟨u, U₂, hUu⟩ := exists_cons_cons hUh hUl (Ne.symm hfl)
  obtain ⟨C, p, hUC⟩ := exists_append_pair hUh hUl (Ne.symm hfl)
  -- the junction at the last point `l`
  have hjr : 0 < cross (l - ℓ) (u - ℓ) := by
    refine junction_turn_left (ps := ps) (Or.inl ⟨?_, ?_⟩) (fun s hs' => ?_) (fun s hs' => ?_)
      (hUm u (by rw [hUu]; simp)) hncol
    · rw [hLA] at hLs
      exact List.rel_of_pairwise_cons (List.pairwise_append.1 hLs).2.1 List.mem_cons_self
    · rw [hUu] at hUs
      exact List.rel_of_pairwise_cons hUs List.mem_cons_self
    · have h := hLc s hs'
      rw [hLA] at h
      exact (List.isChain_cons_cons.1 (h.suffix (List.suffix_append A [ℓ, l]))).1
    · have h := hUc s hs'
      rw [hUu] at h
      exact (List.isChain_cons_cons.1 h).1
  -- the junction at the first point `f`
  have hjf : 0 < cross (f - p) (q - p) := by
    refine junction_turn_left (ps := ps) (Or.inr ⟨?_, ?_⟩) (fun s hs' => ?_) (fun s hs' => ?_)
      (hLm q (by rw [hLq]; simp)) hncol
    · rw [hUC] at hUs
      exact List.rel_of_pairwise_cons (List.pairwise_append.1 hUs).2.1 List.mem_cons_self
    · rw [hLq] at hLs
      exact List.rel_of_pairwise_cons hLs List.mem_cons_self
    · have h := hUc s hs'
      rw [hUC] at h
      exact (List.isChain_cons_cons.1 (h.suffix (List.suffix_append C [p, f]))).1
    · have h := hLc s hs'
      rw [hLq] at h
      exact (List.isChain_cons_cons.1 h).1
  -- glue: lower chain, junction at `l`, upper chain, junction at `f`
  have g1 : TurnsLeft (A ++ [ℓ, l] ++ [u]) :=
    turnsLeft_glue A (by rw [← hLA]; exact hLt) ⟨hjr, trivial⟩
  have g2 : TurnsLeft ((A ++ [ℓ]) ++ [l, u] ++ U₂) :=
    turnsLeft_glue (A ++ [ℓ]) (by simpa using g1) (by rw [hUu] at hUt; simpa using hUt)
  have g2' : TurnsLeft ((A ++ [ℓ] ++ C) ++ [p, f]) := by
    have e : (A ++ [ℓ]) ++ [l, u] ++ U₂ = A ++ [ℓ] ++ C ++ [p, f] := by
      have : [l, u] ++ U₂ = C ++ [p, f] := by rw [← hUC, hUu]; rfl
      rw [List.append_assoc, this]
      simp only [List.append_assoc]
    rw [← e]; exact g2
  have g3 := turnsLeft_glue (A ++ [ℓ] ++ C) g2' (B := [q]) ⟨hjf, trivial⟩
  -- the cyclic polygon is exactly the glued list
  have hW : L ++ U.tail.dropLast ++ (L ++ U.tail.dropLast).take 2 =
      A ++ [ℓ] ++ C ++ [p, f] ++ [q] := by
    have htake : (L ++ U.tail.dropLast).take 2 = [f, q] := by rw [hLq]; simp
    have hlast : U.tail.dropLast ++ [f] = U.tail := by
      have hne : U.tail ≠ [] := by rw [hUu]; simp
      have hg : U.tail.getLast hne = f := by
        have h := hUl
        rw [hUu, List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)]
          at h
        simp only [hUu, List.tail_cons]
        exact Option.some.inj h
      conv_rhs => rw [← List.dropLast_append_getLast hne, hg]
    have hUt' : U = l :: U.tail := by rw [hUu]; rfl
    rw [htake]
    calc L ++ U.tail.dropLast ++ [f, q] = L ++ (U.tail.dropLast ++ [f]) ++ [q] := by simp
      _ = A ++ [ℓ] ++ (l :: U.tail) ++ [q] := by rw [hlast, hLA]; simp
      _ = A ++ [ℓ] ++ C ++ [p, f] ++ [q] := by rw [← hUt', hUC]; simp
  rw [hW]
  exact g3

end Cslib.Algorithms.Lean.Geometry
