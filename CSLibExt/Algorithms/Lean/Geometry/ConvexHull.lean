/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.SegmentIntersection
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Prod.Lex

/-!
# Convex hull by Andrew's monotone chain: the lower chain

Andrew's monotone-chain algorithm (A. M. Andrew, *Another efficient algorithm for convex hulls in
two dimensions*, 1979; de Berg, Cheong, van Kreveld and Overmars, *Computational Geometry*, third
edition, Section 1.1, Algorithm `CONVEXHULL`) is the variant of CLRS's Graham scan (third edition,
Section 33.3) that sorts the points lexicographically instead of by polar angle. This module
proves the half that builds the lower chain: scan the points from left to right, keep a stack, and
before pushing a point pop the top while it does not make a strict left turn.

For points `ps` sorted strictly by `(x, y)`, the returned chain `C`

* starts at the first and ends at the last point of `ps` (`lowerHull_head?`,
  `lowerHull_getLast?`), and is a sublist of `ps` (`lowerHull_sublist`);
* turns strictly left at every inner vertex (`0 < cross (C[i+1] - C[i]) (C[i+2] - C[i])`,
  `lowerHull_turn_left`), so it is strictly convex: no vertex lies on the segment between its
  neighbors;
* has every point of `ps` on or to the left of each of its directed edges
  (`lowerHull_left_of_edges`).

`lowerHullOfPoints_spec` restates them for `lowerHullOfPoints`, which sorts distinct points in any
order first: the vertices are input points, the first and last are the least and greatest points
in `(x, y)` order, and the turn and edge properties are unchanged.

These are the lower-hull properties: every point lies on or above the chain. The upper chain is
the same scan over the reversed list; `CSLibExt.Algorithms.Lean.Geometry.ConvexHullPolygon`
derives its properties by reflection and assembles the two chains into the hull polygon.

Turns are `cross (a - o) (b - o)` with `cross` from `SegmentIntersection`: positive when
`o → a → b` turns left.

## Cost model

One unit per orientation test (one cross product); stack operations and control flow are free.
Each point is pushed once and popped at most once, and each pop loop ends with at most one failed
test, so a scan of `n` points costs at most `2 n` (`lowerHull_time_le`). Sorting the input is not
part of the scan; `lowerHullOfPoints` sorts with `List.mergeSort` first.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

open Cslib.Algorithms.Lean TimeM
open scoped List

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## The scan -/

/-- Pop the top of the stack (top first) while it does not make a strict left turn towards `p`:
the stack `a :: b :: rest` loses `a` when `cross (a - b) (p - b) ≤ 0`. One unit per test. -/
def popNonLeft (p : 𝕜 × 𝕜) : List (𝕜 × 𝕜) → TimeM ℕ (List (𝕜 × 𝕜))
  | a :: b :: rest => do
      ✓
      if cross (a - b) (p - b) ≤ 0 then popNonLeft p (b :: rest) else pure (a :: b :: rest)
  | st => pure st

/-- Process the points in order, popping non-left turns and pushing each point. The stack holds
the chain top first. -/
def chainScan : List (𝕜 × 𝕜) → List (𝕜 × 𝕜) → TimeM ℕ (List (𝕜 × 𝕜))
  | st, [] => pure st
  | st, p :: ps => do
      let st' ← popNonLeft p st
      chainScan (p :: st') ps

/-- The lower chain of points sorted strictly by `(x, y)`, from left to right. -/
def lowerHull (ps : List (𝕜 × 𝕜)) : TimeM ℕ (List (𝕜 × 𝕜)) := do
  let st ← chainScan [] ps
  pure st.reverse

/-- Sort by `(x, y)`, then build the lower chain. -/
def lowerHullOfPoints (ps : List (𝕜 × 𝕜)) : TimeM ℕ (List (𝕜 × 𝕜)) :=
  lowerHull (ps.mergeSort fun a b => decide (toLex a ≤ toLex b))

/-! ## Turn lemmas

Each lemma is a polynomial identity in the coordinates plus a sign argument. The lexicographic
order makes every difference vector point into the closed right half-plane, which is what rules
out turns of more than a half revolution. -/

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem fst_le_of_lex_lt {a b : 𝕜 × 𝕜} (h : toLex a < toLex b) : a.1 ≤ b.1 := by
  rcases Prod.Lex.toLex_lt_toLex.1 h with h | h
  · exact h.le
  · exact h.1.le

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem fst_le_of_lex_le {a b : 𝕜 × 𝕜} (h : toLex a ≤ toLex b) : a.1 ≤ b.1 := by
  rcases Prod.Lex.toLex_le_toLex.1 h with h | h
  · exact h.le
  · exact h.1.le

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem snd_lt_of_lex_lt {a b : 𝕜 × 𝕜} (h : toLex a < toLex b) (he : a.1 = b.1) :
    a.2 < b.2 := by
  rcases Prod.Lex.toLex_lt_toLex.1 h with h | h
  · exact absurd he h.ne
  · exact h.2

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem snd_le_of_lex_le {a b : 𝕜 × 𝕜} (h : toLex a ≤ toLex b) (he : a.1 = b.1) :
    a.2 ≤ b.2 := by
  rcases Prod.Lex.toLex_le_toLex.1 h with h | h
  · exact absurd he h.ne
  · exact h.2

/-- A left turn at `b` and `p` on or left of the edge `b → c` put `p` on or left of `a → b`. -/
private theorem left_of_prev_edge {a b c p : 𝕜 × 𝕜} (hturn : 0 < cross (b - a) (c - a))
    (hleft : 0 ≤ cross (c - b) (p - b)) (hab : toLex a < toLex b) (hbc : toLex b < toLex c)
    (hcp : toLex c < toLex p) : 0 ≤ cross (b - a) (p - a) := by
  have hu := fst_le_of_lex_lt hab
  have hv := fst_le_of_lex_lt hbc
  have hw := fst_le_of_lex_lt hcp
  simp only [cross, Prod.fst_sub, Prod.snd_sub] at *
  -- `v.1 * cross u w = u.1 * cross v w + w.1 * cross u v` with `u = b - a`, `v = c - b`,
  -- `w = p - b`
  have hid : (c.1 - b.1) * ((b.1 - a.1) * (p.2 - a.2) - (p.1 - a.1) * (b.2 - a.2)) =
      (b.1 - a.1) * ((c.1 - b.1) * (p.2 - b.2) - (p.1 - b.1) * (c.2 - b.2)) +
        (p.1 - b.1) * ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)) := by ring
  rcases lt_or_eq_of_le hv with hv | hv
  · have hv : 0 < c.1 - b.1 := by linarith
    by_contra hneg
    push Not at hneg
    have h1 := mul_neg_of_pos_of_neg hv hneg
    have h2 := mul_nonneg (show 0 ≤ b.1 - a.1 by linarith) hleft
    have h3 := mul_nonneg (show 0 ≤ p.1 - b.1 by linarith) hturn.le
    linarith
  · -- the edge `b → c` is vertical, so `p` is directly above `b`
    have hv2 := snd_lt_of_lex_lt hbc hv
    have hv0 : c.1 - b.1 = 0 := by linarith
    rw [hv0, zero_mul, zero_sub] at hleft
    have hw0 : p.1 = b.1 := by
      by_contra hne
      have hpos : 0 < p.1 - b.1 := lt_of_le_of_ne (by linarith) (fun h => hne (by linarith))
      have := mul_pos hpos (show 0 < c.2 - b.2 by linarith)
      linarith
    have hp2 := snd_lt_of_lex_lt hcp (by linarith)
    have : (b.1 - a.1) * (p.2 - a.2) - (p.1 - a.1) * (b.2 - a.2) =
        (b.1 - a.1) * (p.2 - b.2) := by rw [hw0]; ring
    rw [this]
    exact mul_nonneg (by linarith) (by linarith)

/-- One pop, `s` at or after the popped top `a`: the new edge from `o` still has `s` on its left. -/
private theorem pop_left_of_ge {o a p s : 𝕜 × 𝕜} (hs : 0 ≤ cross (p - a) (s - a))
    (hpop : cross (a - o) (p - o) ≤ 0) (hedge : 0 ≤ cross (a - o) (s - o)) :
    0 ≤ cross (p - o) (s - o) := by
  have hid : cross (p - o) (s - o) =
      cross (p - a) (s - a) - cross (a - o) (p - o) + cross (a - o) (s - o) := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hid]; linarith

/-- One pop, `s` between the new top `o` and the popped top `a`. -/
private theorem pop_left_of_between {o a p s : 𝕜 × 𝕜} (hedge : 0 ≤ cross (a - o) (s - o))
    (hpop : cross (a - o) (p - o) ≤ 0) (hos : toLex o ≤ toLex s) (hsa : toLex s < toLex a)
    (hap : toLex a < toLex p) : 0 ≤ cross (p - o) (s - o) := by
  have hz := fst_le_of_lex_le hos
  have hzu := fst_le_of_lex_lt hsa
  have hwa := fst_le_of_lex_lt hap
  simp only [cross, Prod.fst_sub, Prod.snd_sub] at *
  -- `u.1 * cross w z = w.1 * cross u z - z.1 * cross u w` with `u = a - o`, `w = p - o`,
  -- `z = s - o`
  have hid : (a.1 - o.1) * ((p.1 - o.1) * (s.2 - o.2) - (s.1 - o.1) * (p.2 - o.2)) =
      (p.1 - o.1) * ((a.1 - o.1) * (s.2 - o.2) - (s.1 - o.1) * (a.2 - o.2)) -
        (s.1 - o.1) * ((a.1 - o.1) * (p.2 - o.2) - (p.1 - o.1) * (a.2 - o.2)) := by ring
  rcases lt_or_eq_of_le (show o.1 ≤ a.1 by linarith) with hu | hu
  · have hu : 0 < a.1 - o.1 := by linarith
    by_contra hneg
    push Not at hneg
    have h1 := mul_neg_of_pos_of_neg hu hneg
    have h2 := mul_nonneg (show 0 ≤ p.1 - o.1 by linarith) hedge
    have h3 := mul_nonneg (show 0 ≤ s.1 - o.1 by linarith) (neg_nonneg.2 hpop)
    linarith
  · -- vertical edge `o → a`: `s` is on it, above `o`
    have hz0 : s.1 - o.1 = 0 := by linarith
    have hz2 := snd_le_of_lex_le hos (by linarith)
    rw [hz0, zero_mul, sub_zero]
    exact mul_nonneg (by linarith) (by linarith)

/-- After the pops: `s` at or before the kept top `o`, where `q → o → p` turns strictly left and
`s` is on or left of the edge `q → o`. -/
private theorem left_of_new_edge {q o p s : 𝕜 × 𝕜} (hturn : 0 < cross (o - q) (p - q))
    (hedge : 0 ≤ cross (o - q) (s - q)) (hqo : toLex q < toLex o) (hop : toLex o < toLex p)
    (hso : toLex s ≤ toLex o) : 0 ≤ cross (p - o) (s - o) := by
  have hu := fst_le_of_lex_lt hqo
  have hw := fst_le_of_lex_lt hop
  have hz := fst_le_of_lex_le hso
  simp only [cross, Prod.fst_sub, Prod.snd_sub] at *
  -- with `u = q - o`, `w = p - o`, `z = s - o`:
  -- `u.1 * cross w z = w.1 * cross u z - z.1 * cross u w`
  have hid : (q.1 - o.1) * ((p.1 - o.1) * (s.2 - o.2) - (s.1 - o.1) * (p.2 - o.2)) =
      (p.1 - o.1) * ((q.1 - o.1) * (s.2 - o.2) - (s.1 - o.1) * (q.2 - o.2)) -
        (s.1 - o.1) * ((q.1 - o.1) * (p.2 - o.2) - (p.1 - o.1) * (q.2 - o.2)) := by ring
  have huw : (q.1 - o.1) * (p.2 - o.2) - (p.1 - o.1) * (q.2 - o.2) < 0 := by
    have : (o.1 - q.1) * (p.2 - q.2) - (p.1 - q.1) * (o.2 - q.2) =
        -((q.1 - o.1) * (p.2 - o.2) - (p.1 - o.1) * (q.2 - o.2)) := by ring
    linarith
  have huz : (q.1 - o.1) * (s.2 - o.2) - (s.1 - o.1) * (q.2 - o.2) ≤ 0 := by
    have : (o.1 - q.1) * (s.2 - q.2) - (s.1 - q.1) * (o.2 - q.2) =
        -((q.1 - o.1) * (s.2 - o.2) - (s.1 - o.1) * (q.2 - o.2)) := by ring
    linarith
  rcases lt_or_eq_of_le hu with hu | hu
  · have hu : q.1 - o.1 < 0 := by linarith
    by_contra hneg
    push Not at hneg
    have h1 := mul_pos_of_neg_of_neg hu hneg
    have h2 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ p.1 - o.1 by linarith) huz
    have h3 := mul_nonneg_of_nonpos_of_nonpos (show s.1 - o.1 ≤ 0 by linarith) huw.le
    linarith
  · -- a vertical edge `q → o` cannot turn left towards a point to its right
    exfalso
    have hq2 := snd_lt_of_lex_lt hqo hu
    have hu0 : q.1 - o.1 = 0 := by linarith
    rw [hu0, zero_mul, zero_sub] at huw
    have := mul_nonneg (show 0 ≤ p.1 - o.1 by linarith) (show 0 ≤ o.2 - q.2 by linarith)
    nlinarith

/-! ## Stack invariants

The stack lists the chain top first, so its edges are `b → a` for consecutive `a :: b`. -/

/-- Consecutive triples of the stack turn strictly left in chain order. -/
private def ConvexStack : List (𝕜 × 𝕜) → Prop
  | a :: b :: c :: rest => 0 < cross (b - c) (a - c) ∧ ConvexStack (b :: c :: rest)
  | _ => True

/-- `s` is on or left of every edge of the stack. -/
private def LeftStack (s : 𝕜 × 𝕜) (st : List (𝕜 × 𝕜)) : Prop :=
  st.IsChain fun a b => 0 ≤ cross (a - b) (s - b)

/-- Strictly increasing in `(x, y)`. -/
private abbrev LexSorted (ps : List (𝕜 × 𝕜)) : Prop := ps.Pairwise fun a b => toLex a < toLex b

omit [IsStrictOrderedRing 𝕜] in
private theorem convexStack_tail {a : 𝕜 × 𝕜} {rest : List (𝕜 × 𝕜)}
    (h : ConvexStack (a :: rest)) : ConvexStack rest := by
  match rest, h with
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => exact h.2

omit [IsStrictOrderedRing 𝕜] in
private theorem convexStack_of_suffix {l₁ l₂ : List (𝕜 × 𝕜)} (hs : l₁ <:+ l₂)
    (h : ConvexStack l₂) : ConvexStack l₁ := by
  obtain ⟨t, rfl⟩ := hs
  induction t with
  | nil => exact h
  | cons a t ih => exact ih (convexStack_tail h)

/-! ## The pop loop -/

omit [IsStrictOrderedRing 𝕜] in
private theorem popNonLeft_ret_cons_cons (p a b : 𝕜 × 𝕜) (rest : List (𝕜 × 𝕜)) :
    (popNonLeft p (a :: b :: rest)).ret =
      if cross (a - b) (p - b) ≤ 0 then (popNonLeft p (b :: rest)).ret else a :: b :: rest := by
  simp only [popNonLeft, ret_bind]
  split <;> rfl

omit [IsStrictOrderedRing 𝕜] in
private theorem popNonLeft_suffix (p : 𝕜 × 𝕜) (st : List (𝕜 × 𝕜)) :
    (popNonLeft p st).ret <:+ st ∧ (st ≠ [] → (popNonLeft p st).ret ≠ [] ∧
      (popNonLeft p st).ret.getLast? = st.getLast?) := by
  induction st with
  | nil => exact ⟨List.suffix_refl _, fun h => absurd rfl h⟩
  | cons a rest ih =>
      match rest, ih with
      | [], _ => exact ⟨List.suffix_refl _, fun _ => ⟨by simp [popNonLeft], rfl⟩⟩
      | b :: r, ih =>
          rw [popNonLeft_ret_cons_cons]
          split
          · obtain ⟨hsuf, hne⟩ := ih
            obtain ⟨hne, hlast⟩ := hne (List.cons_ne_nil _ _)
            exact ⟨hsuf.trans (List.suffix_cons _ _), fun _ => ⟨hne, by rw [hlast]; simp⟩⟩
          · exact ⟨List.suffix_refl _, fun _ => ⟨List.cons_ne_nil _ _, rfl⟩⟩

omit [IsStrictOrderedRing 𝕜] in
/-- The loop stops at a strict left turn (or at a stack of fewer than two points). -/
private theorem popNonLeft_stop (p : 𝕜 × 𝕜) (st : List (𝕜 × 𝕜)) {a b : 𝕜 × 𝕜}
    {rest : List (𝕜 × 𝕜)} (h : (popNonLeft p st).ret = a :: b :: rest) :
    0 < cross (a - b) (p - b) := by
  induction st with
  | nil => simp [popNonLeft] at h
  | cons a' rest' ih =>
      match rest', ih, h with
      | [], _, h => simp [popNonLeft] at h
      | b' :: r, ih, h =>
          rw [popNonLeft_ret_cons_cons] at h
          split at h
          · exact ih h
          · rename_i hlt
            simp only [List.cons.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact lt_of_not_ge hlt

/-- The pop loop keeps `s ∈ P` on or left of the edge from the top to `p`, for every `s` at or
after the top. -/
private theorem popNonLeft_left (p : 𝕜 × 𝕜) (P : List (𝕜 × 𝕜)) (st : List (𝕜 × 𝕜))
    (hdesc : st.Pairwise fun a b => toLex b < toLex a) (hp : ∀ x ∈ st, toLex x < toLex p)
    (hleft : ∀ s ∈ P, LeftStack s st)
    (hH : ∀ o ∈ st.head?, ∀ s ∈ P, toLex o ≤ toLex s → 0 ≤ cross (p - o) (s - o)) :
    ∀ o ∈ (popNonLeft p st).ret.head?, ∀ s ∈ P, toLex o ≤ toLex s →
      0 ≤ cross (p - o) (s - o) := by
  induction st with
  | nil => simp [popNonLeft]
  | cons a rest ih =>
      match rest, ih, hdesc, hp, hleft, hH with
      | [], _, _, _, _, hH => simpa [popNonLeft] using hH
      | b :: r, ih, hdesc, hp, hleft, hH =>
          rw [popNonLeft_ret_cons_cons]
          split
          · rename_i hpop
            refine ih hdesc.of_cons (fun x hx => hp x (List.mem_cons_of_mem _ hx))
              (fun s hs => (hleft s hs).tail) ?_
            intro o ho s hs hos
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ho
            subst ho
            have hedge : 0 ≤ cross (a - b) (s - b) := (List.isChain_cons_cons.1 (hleft s hs)).1
            by_cases has : toLex a ≤ toLex s
            · exact pop_left_of_ge (hH a rfl s hs has) hpop hedge
            · exact pop_left_of_between hedge hpop hos (lt_of_not_ge has)
                (hp a List.mem_cons_self)
          · exact hH

/-- After the loop, `p` is on or left of every edge of the kept stack. -/
private theorem leftStack_of_left_turns (p : 𝕜 × 𝕜) (st : List (𝕜 × 𝕜)) (hc : ConvexStack st)
    (hdesc : st.Pairwise fun a b => toLex b < toLex a) (hp : ∀ x ∈ st, toLex x < toLex p)
    (htop : ∀ a b rest, st = a :: b :: rest → 0 ≤ cross (a - b) (p - b)) : LeftStack p st := by
  induction st with
  | nil => exact List.isChain_nil
  | cons a rest ih =>
      match rest, ih, hc, hdesc, hp, htop with
      | [], _, _, _, _, _ => exact List.isChain_singleton _
      | [b], _, _, _, _, htop =>
          exact List.isChain_cons_cons.2 ⟨htop a b [] rfl, List.isChain_singleton _⟩
      | b :: c :: r, ih, hc, hdesc, hp, htop =>
          have hab := htop a b (c :: r) rfl
          have hcb : toLex c < toLex b := List.rel_of_pairwise_cons hdesc.of_cons
            List.mem_cons_self
          have hba : toLex b < toLex a := List.rel_of_pairwise_cons hdesc List.mem_cons_self
          have hbc : 0 ≤ cross (b - c) (p - c) :=
            left_of_prev_edge hc.1 hab hcb hba (hp a List.mem_cons_self)
          refine List.isChain_cons_cons.2 ⟨hab, ih hc.2 hdesc.of_cons
            (fun x hx => hp x (List.mem_cons_of_mem _ hx)) ?_⟩
          intro a' b' rest' h
          simp only [List.cons.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact hbc

/-! ## The scan -/

/-- The scan invariant after processing the prefix `P`: the stack, read bottom up, is a sublist of
`P` from its first to its last point, turns strictly left, and has all of `P` on or left of its
edges. -/
private structure ScanInv (P st : List (𝕜 × 𝕜)) : Prop where
  sublist : st.reverse <+ P
  bottom : st.getLast? = P.head?
  top : st.head? = P.getLast?
  convex : ConvexStack st
  left : ∀ s ∈ P, LeftStack s st

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem head_le_of_sorted {P : List (𝕜 × 𝕜)} (hs : LexSorted P) {h : 𝕜 × 𝕜}
    (hh : P.head? = some h) {s : 𝕜 × 𝕜} (hsP : s ∈ P) : toLex h ≤ toLex s := by
  match P, hs, hh with
  | x :: P', hs, hh =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rcases List.mem_cons.1 hsP with rfl | hm
      · exact le_rfl
      · exact (List.rel_of_pairwise_cons hs hm).le

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem le_last_of_sorted {P : List (𝕜 × 𝕜)} (hs : LexSorted P) {l : 𝕜 × 𝕜}
    (hl : P.getLast? = some l) {s : 𝕜 × 𝕜} (hsP : s ∈ P) : toLex s ≤ toLex l := by
  have hr : (P.reverse).Pairwise fun a b => toLex b < toLex a := List.pairwise_reverse.2 hs
  have hh : P.reverse.head? = some l := by rw [List.head?_reverse, hl]
  match P.reverse, hr, hh, List.mem_reverse.2 hsP with
  | x :: P', hr, hh, hm =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rcases List.mem_cons.1 hm with rfl | hm
      · exact le_rfl
      · exact (List.rel_of_pairwise_cons hr hm).le

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem cross_self (v : 𝕜 × 𝕜) : cross v v = 0 := by
  simp only [cross]; ring

omit [IsStrictOrderedRing 𝕜] in
private theorem popNonLeft_nil_ret (p : 𝕜 × 𝕜) : (popNonLeft p []).ret = [] := rfl

/-- One step of the scan preserves the invariant. -/
private theorem scanInv_step {P st : List (𝕜 × 𝕜)} {p : 𝕜 × 𝕜} (inv : ScanInv P st)
    (hs : LexSorted (P ++ [p])) : ScanInv (P ++ [p]) (p :: (popNonLeft p st).ret) := by
  have hsP : LexSorted P := (List.pairwise_append.1 hs).1
  have hpP : ∀ x ∈ P, toLex x < toLex p := fun x hx =>
    (List.pairwise_append.1 hs).2.2 x hx p List.mem_cons_self
  have hstP : ∀ x ∈ st, x ∈ P := fun x hx => inv.sublist.subset (List.mem_reverse.2 hx)
  have hdesc : st.Pairwise fun a b => toLex b < toLex a :=
    List.pairwise_reverse.1 (hsP.sublist inv.sublist)
  rcases List.eq_nil_or_concat P with rfl | ⟨P', l, rfl⟩
  · -- the first point
    have hst : st = [] := by simpa using inv.top
    subst hst
    rw [popNonLeft_nil_ret]
    refine ⟨by simp, by simp, by simp, trivial, ?_⟩
    intro s hs'
    simp only [List.nil_append, List.mem_singleton] at hs'
    subst hs'
    exact List.isChain_singleton _
  · rw [List.concat_eq_append] at *
    have hne : st ≠ [] := by
      intro h; have := inv.top; simp [h] at this
    obtain ⟨hsuf, hne'⟩ := popNonLeft_suffix p st
    obtain ⟨hne', hlast⟩ := hne' hne
    have hstop : ∀ {a b : 𝕜 × 𝕜} {rest : List (𝕜 × 𝕜)},
        (popNonLeft p st).ret = a :: b :: rest → 0 < cross (a - b) (p - b) :=
      popNonLeft_stop p st
    have hH := popNonLeft_left p (P' ++ [l]) st hdesc (fun x hx => hpP x (hstP x hx)) inv.left
      (by
        intro o ho s hs' hos
        have hol : toLex s ≤ toLex o :=
          le_last_of_sorted hsP (inv.top ▸ ho) hs'
        have : s = o := toLex.injective (le_antisymm hol hos)
        subst this
        simp [sub_self, cross])
    generalize (popNonLeft p st).ret = st' at hsuf hne' hlast hstop hH ⊢
    have hdesc' : st'.Pairwise fun a b => toLex b < toLex a := hdesc.sublist hsuf.sublist
    have hst'P : ∀ x ∈ st', toLex x < toLex p := fun x hx =>
      hpP x (hstP x (hsuf.subset hx))
    have hconv' : ConvexStack st' := convexStack_of_suffix hsuf inv.convex
    have hleft' : ∀ s ∈ P' ++ [l], LeftStack s st' := fun s hs' => (inv.left s hs').suffix hsuf
    have hbottom' : st'.getLast? = (P' ++ [l]).head? := hlast.trans inv.bottom
    have hpl : LeftStack p st' := leftStack_of_left_turns p st' hconv' hdesc' hst'P
      (fun a b rest h => (hstop h).le)
    refine ⟨?_, ?_, by simp, ?_, ?_⟩
    · rw [List.reverse_cons]
      exact List.Sublist.append (hsuf.reverse.sublist.trans inv.sublist) (List.Sublist.refl _)
    · rcases st' with _ | ⟨o, r⟩
      · exact absurd rfl hne'
      · rw [List.getLast?_cons_cons, hbottom']
        cases P' <;> rfl
    · rcases st' with _ | ⟨o, _ | ⟨q, r⟩⟩
      · trivial
      · trivial
      · exact ⟨hstop rfl, hconv'⟩
    · intro s hs'
      rcases st' with _ | ⟨o, r⟩
      · exact absurd rfl hne'
      rcases List.mem_append.1 hs' with hs' | hs'
      · refine List.isChain_cons_cons.2 ⟨?_, hleft' s hs'⟩
        by_cases hos : toLex o ≤ toLex s
        · exact hH o rfl s hs' hos
        · rcases r with _ | ⟨q, r⟩
          · have hb : (P' ++ [l]).head? = some o := by rw [← hbottom']; rfl
            exact absurd (head_le_of_sorted hsP hb hs') hos
          · have hedge : 0 ≤ cross (o - q) (s - q) := (List.isChain_cons_cons.1 (hleft' s hs')).1
            have hqo : toLex q < toLex o := List.rel_of_pairwise_cons hdesc' List.mem_cons_self
            exact left_of_new_edge (hstop rfl) hedge hqo (hst'P o List.mem_cons_self)
              (le_of_not_ge hos)
      · simp only [List.mem_singleton] at hs'
        subst hs'
        exact List.isChain_cons_cons.2 ⟨by simp [cross_self], hpl⟩

private theorem chainScan_inv : ∀ (ps P st : List (𝕜 × 𝕜)), ScanInv P st →
    LexSorted (P ++ ps) → ScanInv (P ++ ps) (chainScan st ps).ret
  | [], P, st, inv, _ => by simpa [chainScan] using inv
  | p :: ps, P, st, inv, hs => by
      simp only [chainScan, ret_bind]
      have hs1 : LexSorted (P ++ [p]) :=
        hs.sublist (List.Sublist.append (List.Sublist.refl P)
          (List.singleton_sublist.2 List.mem_cons_self))
      have := chainScan_inv ps (P ++ [p]) _ (scanInv_step inv hs1) (by simpa using hs)
      simpa using this

private theorem scanInv_lowerHull (ps : List (𝕜 × 𝕜)) (hs : LexSorted ps) :
    ScanInv ps (chainScan [] ps).ret := by
  simpa using chainScan_inv ps [] [] ⟨by simp, rfl, rfl, trivial, by simp⟩ (by simpa using hs)

omit [IsStrictOrderedRing 𝕜] in
private theorem lowerHull_ret (ps : List (𝕜 × 𝕜)) :
    (lowerHull ps).ret = (chainScan [] ps).ret.reverse := rfl

omit [IsStrictOrderedRing 𝕜] in
private theorem convexStack_getElem : ∀ {st : List (𝕜 × 𝕜)}, ConvexStack st →
    ∀ j (h : j + 2 < st.length), 0 < cross (st[j + 1] - st[j + 2]) (st[j] - st[j + 2])
  | a :: b :: c :: r, hc, 0, _ => hc.1
  | a :: b :: c :: r, hc, j + 1, h => by
      have := convexStack_getElem hc.2 j (by simp at h ⊢; omega)
      simpa using this

/-! ## Correctness -/

/-- The chain is a sublist of the input: its vertices are input points, in input order. -/
theorem lowerHull_sublist (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b) :
    (lowerHull ps).ret <+ ps :=
  (scanInv_lowerHull ps hs).sublist

/-- The chain starts at the first input point. -/
theorem lowerHull_head? (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b) :
    (lowerHull ps).ret.head? = ps.head? := by
  rw [lowerHull_ret, List.head?_reverse]; exact (scanInv_lowerHull ps hs).bottom

/-- The chain ends at the last input point. -/
theorem lowerHull_getLast? (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b) :
    (lowerHull ps).ret.getLast? = ps.getLast? := by
  rw [lowerHull_ret, List.getLast?_reverse]; exact (scanInv_lowerHull ps hs).top

/-- The chain turns strictly left at every inner vertex. -/
theorem lowerHull_turn_left (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b)
    (i : ℕ) (h : i + 2 < (lowerHull ps).ret.length) :
    0 < cross ((lowerHull ps).ret[i + 1] - (lowerHull ps).ret[i])
      ((lowerHull ps).ret[i + 2] - (lowerHull ps).ret[i]) := by
  have hc := convexStack_getElem (scanInv_lowerHull ps hs).convex
  simp only [lowerHull_ret, List.length_reverse] at h ⊢
  set st := (chainScan [] ps).ret
  obtain ⟨j, hj⟩ : ∃ j, st.length = i + j + 3 := ⟨st.length - i - 3, by omega⟩
  have key := hc j (by omega)
  have hr0 : i < st.reverse.length := by simp only [List.length_reverse]; omega
  have hr1 : i + 1 < st.reverse.length := by simp only [List.length_reverse]; omega
  have hr2 : i + 2 < st.reverse.length := by simp only [List.length_reverse]; omega
  have e0 : st.reverse[i] = st[j + 2] := by rw [List.getElem_reverse]; congr 1; omega
  have e1 : st.reverse[i + 1] = st[j + 1] := by rw [List.getElem_reverse]; congr 1; omega
  have e2 : st.reverse[i + 2] = st[j] := by rw [List.getElem_reverse]; congr 1; omega
  rw [e0, e1, e2]
  exact key

/-- Every input point is on or left of every directed edge of the chain: the chain is the lower
boundary of the hull. -/
theorem lowerHull_left_of_edges (ps : List (𝕜 × 𝕜)) (hs : ps.Pairwise fun a b => toLex a < toLex b)
    {s : 𝕜 × 𝕜} (hsps : s ∈ ps) :
    (lowerHull ps).ret.IsChain fun a b => 0 ≤ cross (b - a) (s - a) := by
  rw [lowerHull_ret, List.isChain_reverse]
  exact (scanInv_lowerHull ps hs).left s hsps

/-! ## Cost -/

omit [IsStrictOrderedRing 𝕜] in
private theorem popNonLeft_time (p : 𝕜 × 𝕜) (st : List (𝕜 × 𝕜)) :
    (popNonLeft p st).time + (popNonLeft p st).ret.length ≤ st.length + 1 := by
  induction st with
  | nil => change 0 + 0 ≤ 0 + 1; omega
  | cons a rest ih =>
      match rest, ih with
      | [], _ => change 0 + 1 ≤ 1 + 1; omega
      | b :: r, ih =>
          rw [popNonLeft_ret_cons_cons]
          simp only [popNonLeft, time_bind, time_tick, List.length_cons] at ih ⊢
          split
          · omega
          · simp only [time_pure, List.length_cons]; omega

omit [IsStrictOrderedRing 𝕜] in
private theorem chainScan_time : ∀ (st ps : List (𝕜 × 𝕜)),
    (chainScan st ps).time + (chainScan st ps).ret.length ≤ st.length + 2 * ps.length
  | st, [] => by simp [chainScan]
  | st, p :: ps => by
      simp only [chainScan, time_bind, ret_bind, List.length_cons]
      have h1 := popNonLeft_time p st
      have h2 := chainScan_time (p :: (popNonLeft p st).ret) ps
      simp only [List.length_cons] at h2
      omega

omit [IsStrictOrderedRing 𝕜] in
/-- A scan of `n` points makes at most `2 n` orientation tests. -/
theorem lowerHull_time_le (ps : List (𝕜 × 𝕜)) : (lowerHull ps).time ≤ 2 * ps.length := by
  have := chainScan_time [] ps
  simp only [lowerHull, time_bind, time_pure, List.length_nil] at this ⊢
  omega

/-! ## Unsorted input -/

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem lexSorted_mergeSort {ps : List (𝕜 × 𝕜)} (hnd : ps.Nodup) :
    LexSorted (ps.mergeSort fun a b => decide (toLex a ≤ toLex b)) := by
  have hle := List.pairwise_mergeSort (le := fun a b : 𝕜 × 𝕜 => decide (toLex a ≤ toLex b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
    (fun a b => by simpa using le_total (toLex a) (toLex b)) ps
  have hne := (List.mergeSort_perm ps fun a b => decide (toLex a ≤ toLex b)).nodup_iff.2 hnd
  exact (hle.and hne).imp fun ⟨h1, h2⟩ =>
    lt_of_le_of_ne (by simpa using h1) (fun h => h2 (toLex.injective h))

/-- For distinct points in any order: the chain's vertices are input points, it starts at the
least and ends at the greatest point in `(x, y)` order, turns strictly left, and has every point
on or left of each edge. -/
theorem lowerHullOfPoints_spec (ps : List (𝕜 × 𝕜)) (hnd : ps.Nodup) :
    let C := (lowerHullOfPoints ps).ret
    (∀ c ∈ C, c ∈ ps) ∧ (ps ≠ [] → C ≠ []) ∧
    (∀ c ∈ C.head?, ∀ s ∈ ps, toLex c ≤ toLex s) ∧
    (∀ c ∈ C.getLast?, ∀ s ∈ ps, toLex s ≤ toLex c) ∧
    (∀ i (h : i + 2 < C.length), 0 < cross (C[i + 1] - C[i]) (C[i + 2] - C[i])) ∧
    ∀ s ∈ ps, C.IsChain fun a b => 0 ≤ cross (b - a) (s - a) := by
  intro C
  set qs := ps.mergeSort fun a b => decide (toLex a ≤ toLex b)
  have hs : LexSorted qs := lexSorted_mergeSort hnd
  have hperm : qs ~ ps := List.mergeSort_perm ps _
  refine ⟨fun c hc => hperm.subset ((lowerHull_sublist qs hs).subset hc), fun hne hC => ?_,
    fun c hc s hsps => ?_, fun c hc s hsps => ?_, lowerHull_turn_left qs hs,
    fun s hsps => lowerHull_left_of_edges qs hs (hperm.symm.subset hsps)⟩
  · have := lowerHull_head? qs hs
    change C.head? = qs.head? at this
    rw [hC, List.head?_nil, eq_comm, List.head?_eq_none_iff] at this
    exact hne (List.Perm.eq_nil (this ▸ hperm.symm))
  · have := lowerHull_head? qs hs
    change C.head? = qs.head? at this
    exact head_le_of_sorted hs (this ▸ hc) (hperm.symm.subset hsps)
  · have := lowerHull_getLast? qs hs
    change C.getLast? = qs.getLast? at this
    exact le_last_of_sorted hs (this ▸ hc) (hperm.symm.subset hsps)

end Cslib.Algorithms.Lean.Geometry
