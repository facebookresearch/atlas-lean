/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import CSLibExt.Algorithms.Lean.DataStructures.SparseTable
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Closest pair of points by divide and conquer

CLRS, third edition, Section 33.4. Sort the points by `x`; split the sorted list at its middle;
solve both halves; let `d` be the smaller closest-pair distance. A closer pair must have one point
in each half, so both lie within `d` of the dividing line (the *strip*). Sorted by `y`, each strip
point only needs to be compared with the following strip points whose `y` differs by less than
`d`.

Distances are compared squared (`dist2`), so coordinates may come from any linearly ordered field
(`ℚ` runs, `ℝ` is the textbook setting). In the code `δ` is the squared distance `d²`: "within `d`
of the line" reads `(x - x_mid)² < δ`, and "`y` differs by less than `d`" reads
`(q.2 - p.2)² < δ`. The answer is the least squared distance between two entries of the list at
different positions (`IsMinPairDist2`), so repeated points give `0`. Optional minima use
`SparseTable.omin`, with `none` as `+∞`. `closestPair_spec` proves the divide-and-conquer result
is that minimum, and it agrees with the brute-force scan (`closestPair_eq_bruteMin`).

The strip loop stops at the first point whose squared `y` gap reaches `δ`, as in CLRS's argument;
this module proves correctness only. CLRS's packing argument (at most seven following points
qualify), which gives the `O(n log n)` bound, is not formalized here.

## Cost model

One unit per squared distance computed. Sorting, splitting and filtering are free.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

open Cslib.Algorithms.Lean TimeM
open scoped List
open Cslib.Algorithms.Lean.SparseTable (omin)

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **Squared distance in the plane.** Let $K$ be a linearly ordered field. The squared distance
between points $p = (p_1, p_2)$ and $q = (q_1, q_2)$ of $K^2$ is $(p_1 - q_1)^2 + (p_2 - q_2)^2$. -/
def dist2 (p q : 𝕜 × 𝕜) : 𝕜 := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- **Least pairwise squared distance.** Let $K$ be a linearly ordered field, and write
$d(p, q) = (p_1 - q_1)^2 + (p_2 - q_2)^2$ for the squared distance between points
$p = (p_1, p_2)$ and $q = (q_1, q_2)$ of $K^2$. For a list $c_1, \dots, c_n$ of points of $K^2$,
an element $\delta$ of $K$ is the least pairwise squared distance of the list when
$\delta = d(c_i, c_j)$ for some $i < j$ and $\delta \le d(c_i, c_j)$ for all $i < j$. -/
def IsMinPairDist2 (ps : List (𝕜 × 𝕜)) (δ : 𝕜) : Prop :=
  (∃ p q, [p, q] <+ ps ∧ dist2 p q = δ) ∧ ∀ p q, [p, q] <+ ps → δ ≤ dist2 p q

/-- **Least squared distance from a point to a list.** Let $K$ be a linearly ordered field, and
write $d(p, q) = (p_1 - q_1)^2 + (p_2 - q_2)^2$ for the squared distance between points
$p = (p_1, p_2)$ and $q = (q_1, q_2)$ of $K^2$. For a point $p$ and a list $c_1, \dots, c_m$ of
points of $K^2$, the least squared distance from $p$ to the list is no value if $m = 0$ and
$\min_{1 \le k \le m} d(p, c_k)$ otherwise. Computing it is charged one unit of cost per point of
the list, $m$ units in total. -/
def minDistFrom (p : 𝕜 × 𝕜) : List (𝕜 × 𝕜) → TimeM ℕ (Option 𝕜)
  | [] => pure none
  | q :: qs => do
      ✓
      let r ← minDistFrom p qs
      pure (omin (some (dist2 p q)) r)

/-- **Brute-force closest pair.** Let $K$ be a field with a linear order, and write
$d(p, q) = (x - x')^2 + (y - y')^2$ for the squared distance between points $p = (x, y)$ and
$q = (x', y')$ of $K^2$. On a list $c_1, \dots, c_n$ of points in $K^2$, the brute-force scan
returns no value if $n < 2$, and otherwise returns $\min_{i < j} d(c_i, c_j)$: for each $i$ it
computes the least squared distance from $c_i$ to the later points $c_{i+1}, \dots, c_n$, and
takes the least of these minima. It is charged one unit of cost per squared distance computed. -/
def bruteMin : List (𝕜 × 𝕜) → TimeM ℕ (Option 𝕜)
  | [] => pure none
  | p :: ps => do
      let a ← minDistFrom p ps
      let b ← bruteMin ps
      pure (omin a b)

/-- **Strip scan from a point.** Let $K$ be a linearly ordered field, and write
$d(p, q) = (p_1 - q_1)^2 + (p_2 - q_2)^2$ for the squared distance between points
$p = (p_1, p_2)$ and $q = (q_1, q_2)$ of $K^2$. Let $\delta \in K$, let $p = (p_1, p_2)$ be a
point of $K^2$ and $c_1, \dots, c_m$ a list of points $c_l = (x_l, y_l)$ of $K^2$, and let
$k \le m$ be largest such that $(y_l - p_2)^2 < \delta$ for all $1 \le l \le k$. The scan from $p$
with threshold $\delta$ returns no value if $k = 0$ and $\min_{1 \le l \le k} d(p, c_l)$
otherwise. It is charged one unit of cost per point $c_1, \dots, c_k$: it stops at the first
point whose squared vertical gap to $p$ is at least $\delta$, without computing its distance. -/
def scanFrom (δ : 𝕜) (p : 𝕜 × 𝕜) : List (𝕜 × 𝕜) → TimeM ℕ (Option 𝕜)
  | [] => pure none
  | q :: qs =>
      if (q.2 - p.2) ^ 2 < δ then do
        ✓
        let r ← scanFrom δ p qs
        pure (omin (some (dist2 p q)) r)
      else pure none

/-- **Closest-pair strip scan.** Let $K$ be a linearly ordered field, $\delta \in K$ and
$c_1, \dots, c_n$ a list of points of $K^2$. For each $i$, the strip scan runs the strip scan from
$c_i$ with threshold $\delta$ on the later points $c_{i+1}, \dots, c_n$. It returns the least of
the values these scans return, or no value if none of them returns a value, and its cost is the
sum of their costs. -/
def stripScan (δ : 𝕜) : List (𝕜 × 𝕜) → TimeM ℕ (Option 𝕜)
  | [] => pure none
  | p :: ps => do
      let a ← scanFrom δ p ps
      let b ← stripScan δ ps
      pure (omin a b)

/-- **Closest-pair recursion.** Let $K$ be a linearly ordered field and $c_1, \dots, c_n$ a list
of points $c_i = (x_i, y_i)$ of $K^2$. If $n \le 3$, the recursion returns the brute-force scan of
the list. Otherwise let $m = \lfloor n/2 \rfloor$, and run the recursion on $c_1, \dots, c_m$ and
on $c_{m+1}, \dots, c_n$. If neither call returns a value, it returns no value. Otherwise let
$\delta$ be the least of the returned values, let $T$ be the list of the points $c_i$ with
$(x_i - x_m)^2 < \delta$ in their original order, sorted by second coordinate with a stable merge
sort, and run the strip scan with threshold $\delta$ on $T$. The recursion returns
$\min(\delta, s)$ if the strip scan returns a value $s$, and $\delta$ otherwise. In the base case
its cost is that of the brute-force scan; otherwise it is the sum of the costs of the two
recursive calls and of the strip scan when it is run, and splitting, filtering and sorting are
free. -/
def closestRec (xs : List (𝕜 × 𝕜)) : TimeM ℕ (Option 𝕜) :=
  if _h : xs.length ≤ 3 then bruteMin xs
  else do
    let L := xs.take (xs.length / 2)
    let R := xs.drop (xs.length / 2)
    let dl ← closestRec L
    let dr ← closestRec R
    match omin dl dr with
    | none => pure none
    | some δ =>
        let xmid := (L.getLast?.map Prod.fst).getD 0
        let strip := xs.filter fun p => (p.1 - xmid) ^ 2 < δ
        let ys := strip.mergeSort fun a b => a.2 ≤ b.2
        let s ← stripScan δ ys
        pure (omin (some δ) s)
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

/-- **Divide-and-conquer closest pair.** Let $K$ be a field with a linear order. Given a list of
points in $K^2$, the closest-pair algorithm sorts the points by first coordinate (merge sort, at
no cost) and runs the closest-pair recursion on the sorted list. It returns a squared distance or
no value, and is charged one unit of cost per squared distance computed.

This is CLRS `CLOSEST-PAIR` (Section 33.4), with distances compared squared. -/
def closestPair (ps : List (𝕜 × 𝕜)) : TimeM ℕ (Option 𝕜) :=
  closestRec (ps.mergeSort fun a b => a.1 ≤ b.1)

/-! ## Answers -/

/-- **Closest-pair answer.** Let $K$ be a linearly ordered field, and write
$d(p, q) = (p_1 - q_1)^2 + (p_2 - q_2)^2$ for the squared distance between points
$p = (p_1, p_2)$ and $q = (q_1, q_2)$ of $K^2$. For a list $c_1, \dots, c_n$ of points of $K^2$,
an optional value $r$ (an element of $K$ or no value) is an answer for the list when every value
$\delta$ that $r$ holds equals $d(c_i, c_j)$ for some $i < j$, and when for all $i < j$, $r$ holds
a value $\delta$ with $\delta \le d(c_i, c_j)$. -/
structure IsAnswer (ps : List (𝕜 × 𝕜)) (r : Option 𝕜) : Prop where
  attained : ∀ δ, r = some δ → ∃ p q, [p, q] <+ ps ∧ dist2 p q = δ
  lower : ∀ p q, [p, q] <+ ps → ∃ δ, r = some δ ∧ δ ≤ dist2 p q

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem dist2_comm (p q : 𝕜 × 𝕜) : dist2 p q = dist2 q p := by
  simp only [dist2]
  ring

theorem sq_sub_fst_le_dist2 (p q : 𝕜 × 𝕜) : (p.1 - q.1) ^ 2 ≤ dist2 p q :=
  le_add_of_nonneg_right (sq_nonneg _)

theorem sq_sub_snd_le_dist2 (p q : 𝕜 × 𝕜) : (q.2 - p.2) ^ 2 ≤ dist2 p q := by
  rw [show (q.2 - p.2) ^ 2 = (p.2 - q.2) ^ 2 by ring]
  exact le_add_of_nonneg_left (sq_nonneg _)

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem optMin_eq_some {a b : Option 𝕜} {δ : 𝕜} (h : omin a b = some δ) :
    a = some δ ∨ b = some δ := by
  match a, b, h with
  | none, _, h => exact Or.inr h
  | some a, none, h => exact Or.inl h
  | some a, some b, h =>
      simp only [omin, Option.some.injEq] at h
      rcases min_choice a b with h' | h' <;> rw [h'] at h <;> simp [h]

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem optMin_le_left {a : Option 𝕜} (b : Option 𝕜) {x : 𝕜}
    (h : ∃ δ, a = some δ ∧ δ ≤ x) : ∃ δ, omin a b = some δ ∧ δ ≤ x := by
  obtain ⟨δ, rfl, hδ⟩ := h
  cases b with
  | none => exact ⟨δ, rfl, hδ⟩
  | some b => exact ⟨min δ b, rfl, (min_le_left _ _).trans hδ⟩

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem optMin_le_right (a : Option 𝕜) {b : Option 𝕜} {x : 𝕜}
    (h : ∃ δ, b = some δ ∧ δ ≤ x) : ∃ δ, omin a b = some δ ∧ δ ≤ x := by
  obtain ⟨δ, rfl, hδ⟩ := h
  cases a with
  | none => exact ⟨δ, rfl, hδ⟩
  | some a => exact ⟨min a δ, rfl, (min_le_right _ _).trans hδ⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two entries at different positions of a list are at different positions of any
permutation, in one order or the other. -/
private theorem pair_sublist_of_perm {l₁ l₂ : List (𝕜 × 𝕜)} {a b : 𝕜 × 𝕜} (hp : l₁ ~ l₂)
    (h : [a, b] <+ l₁) : [a, b] <+ l₂ ∨ [b, a] <+ l₂ := by
  obtain ⟨l, hl, hsub⟩ := List.exists_perm_sublist h hp
  have hlen := hl.length_eq
  match l, hlen, hl, hsub with
  | [x, y], _, hl, hsub =>
      have hx : x ∈ [a, b] := hl.subset List.mem_cons_self
      rcases List.mem_pair.1 hx with rfl | rfl
      · have : [y] ~ [b] := (List.perm_cons x).1 hl
        rw [List.perm_singleton.1 this] at hsub
        exact Or.inl hsub
      · have : [y] ~ [a] := (List.perm_cons x).1 (hl.trans (List.Perm.swap x a []))
        rw [List.perm_singleton.1 this] at hsub
        exact Or.inr hsub

omit [IsStrictOrderedRing 𝕜] in
theorem IsAnswer.perm {l₁ l₂ : List (𝕜 × 𝕜)} {r : Option 𝕜} (h : IsAnswer l₁ r)
    (hp : l₁ ~ l₂) : IsAnswer l₂ r where
  attained δ hδ := by
    obtain ⟨p, q, hpq, hd⟩ := h.attained δ hδ
    rcases pair_sublist_of_perm hp hpq with h' | h'
    · exact ⟨p, q, h', hd⟩
    · exact ⟨q, p, h', by rw [dist2_comm, hd]⟩
  lower p q hpq := by
    rcases pair_sublist_of_perm hp.symm hpq with h' | h'
    · exact h.lower p q h'
    · obtain ⟨δ, hδ, hle⟩ := h.lower q p h'
      exact ⟨δ, hδ, by rwa [dist2_comm]⟩

omit [IsStrictOrderedRing 𝕜] in
theorem IsAnswer.unique {ps : List (𝕜 × 𝕜)} {r r' : Option 𝕜} (h : IsAnswer ps r)
    (h' : IsAnswer ps r') : r = r' := by
  cases r with
  | none =>
      cases r' with
      | none => rfl
      | some δ' =>
          obtain ⟨p, q, hpq, -⟩ := h'.attained δ' rfl
          obtain ⟨δ, hδ, -⟩ := h.lower p q hpq
          simp at hδ
  | some δ =>
      obtain ⟨p, q, hpq, hd⟩ := h.attained δ rfl
      obtain ⟨δ', hδ', hle⟩ := h'.lower p q hpq
      subst hδ'
      obtain ⟨p', q', hpq', hd'⟩ := h'.attained δ' rfl
      obtain ⟨δ'', hδ'', hle'⟩ := h.lower p' q' hpq'
      simp only [Option.some.injEq] at hδ''
      subst hδ''
      exact congrArg some (le_antisymm (hd' ▸ hle') (hd ▸ hle))

omit [IsStrictOrderedRing 𝕜] in
theorem IsAnswer.isMinPairDist2 {ps : List (𝕜 × 𝕜)} {δ : 𝕜} (h : IsAnswer ps (some δ)) :
    IsMinPairDist2 ps δ :=
  ⟨h.attained δ rfl, fun p q hpq => by
    obtain ⟨δ', hδ', hle⟩ := h.lower p q hpq
    simp only [Option.some.injEq] at hδ'
    exact hδ' ▸ hle⟩

/-! ## Brute force -/

/-- **The nearest-point scan returns the least squared distance.** Let $K$ be a linearly ordered
field, write $d(u, v) = (x - x')^2 + (y - y')^2$ for the squared distance between points
$u = (x, y)$ and $v = (x', y')$ of $K^2$, let $p \in K^2$, and let $qs$ be a list of points in
$K^2$. If the scan for the least squared distance from $p$ to the entries of $qs$ returns a value
$\delta$, then $\delta = d(p, q)$ for some entry $q$ of $qs$. For every entry $q$ of $qs$, the
scan returns a value $\delta$ with $\delta \le d(p, q)$. -/
theorem minDistFrom_spec (p : 𝕜 × 𝕜) (qs : List (𝕜 × 𝕜)) :
    (∀ δ, (minDistFrom p qs).ret = some δ → ∃ q ∈ qs, dist2 p q = δ) ∧
      ∀ q ∈ qs, ∃ δ, (minDistFrom p qs).ret = some δ ∧ δ ≤ dist2 p q := by
  induction qs with
  | nil => simp [minDistFrom]
  | cons q qs ih =>
      simp only [minDistFrom, ret_bind, ret_pure]
      refine ⟨fun δ hδ => ?_, fun q' hq' => ?_⟩
      · rcases optMin_eq_some hδ with h | h
        · exact ⟨q, List.mem_cons_self, by simpa using h⟩
        · obtain ⟨q', hq', hd⟩ := ih.1 δ h
          exact ⟨q', List.mem_cons_of_mem _ hq', hd⟩
      · rcases List.mem_cons.1 hq' with rfl | hq'
        · exact optMin_le_left _ ⟨_, rfl, le_rfl⟩
        · exact optMin_le_right _ (ih.2 q' hq')

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem pair_sublist_cons {p a b : 𝕜 × 𝕜} {ps : List (𝕜 × 𝕜)}
    (h : [a, b] <+ p :: ps) : [a, b] <+ ps ∨ (a = p ∧ b ∈ ps) := by
  rcases List.sublist_cons_iff.1 h with h | ⟨r, hr, hsub⟩
  · exact Or.inl h
  · simp only [List.cons.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact Or.inr ⟨rfl, List.singleton_sublist.1 hsub⟩

theorem bruteMin_isAnswer (ps : List (𝕜 × 𝕜)) : IsAnswer ps (bruteMin ps).ret := by
  induction ps with
  | nil => exact ⟨fun δ h => by simp [bruteMin] at h, fun p q h => by simp at h⟩
  | cons p ps ih =>
      have hm := minDistFrom_spec p ps
      simp only [bruteMin, ret_bind, ret_pure]
      refine ⟨fun δ hδ => ?_, fun a b hab => ?_⟩
      · rcases optMin_eq_some hδ with h | h
        · obtain ⟨q, hq, hd⟩ := hm.1 δ h
          exact ⟨p, q, List.cons_sublist_cons.2 (List.singleton_sublist.2 hq), hd⟩
        · obtain ⟨a, b, hab, hd⟩ := ih.attained δ h
          exact ⟨a, b, hab.cons p, hd⟩
      · rcases pair_sublist_cons hab with h | ⟨rfl, hb⟩
        · exact optMin_le_right _ (ih.lower a b h)
        · exact optMin_le_left _ (hm.2 b hb)

/-! ## The strip -/

omit [IsStrictOrderedRing 𝕜] in
theorem scanFrom_attained (δ : 𝕜) (p : 𝕜 × 𝕜) (qs : List (𝕜 × 𝕜)) (d : 𝕜)
    (h : (scanFrom δ p qs).ret = some d) : ∃ q ∈ qs, dist2 p q = d := by
  induction qs with
  | nil => simp [scanFrom] at h
  | cons q qs ih =>
      simp only [scanFrom] at h
      split_ifs at h with hc
      · simp only [ret_bind, ret_pure] at h
        rcases optMin_eq_some h with h | h
        · exact ⟨q, List.mem_cons_self, by simpa using h⟩
        · obtain ⟨q', hq', hd⟩ := ih h
          exact ⟨q', List.mem_cons_of_mem _ hq', hd⟩
      · simp at h

theorem scanFrom_lower (δ : 𝕜) (p : 𝕜 × 𝕜) (qs : List (𝕜 × 𝕜))
    (hs : qs.Pairwise fun a b => a.2 ≤ b.2) (hp : ∀ q ∈ qs, p.2 ≤ q.2) (b : 𝕜 × 𝕜)
    (hb : b ∈ qs) (hgap : (b.2 - p.2) ^ 2 < δ) :
    ∃ d, (scanFrom δ p qs).ret = some d ∧ d ≤ dist2 p b := by
  induction qs with
  | nil => simp at hb
  | cons q qs ih =>
      have hc : (q.2 - p.2) ^ 2 < δ := by
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact hgap
        · have h1 : p.2 ≤ q.2 := hp q List.mem_cons_self
          have h2 : q.2 ≤ b.2 := List.rel_of_pairwise_cons hs hb'
          have : (q.2 - p.2) ^ 2 ≤ (b.2 - p.2) ^ 2 :=
            pow_le_pow_left₀ (by linarith) (by linarith) 2
          exact lt_of_le_of_lt this hgap
      simp only [scanFrom, hc, ite_true, ret_bind, ret_pure]
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact optMin_le_left _ ⟨_, rfl, le_rfl⟩
      · exact optMin_le_right _ (ih hs.of_cons (fun q' hq' => hp q' (List.mem_cons_of_mem _ hq'))
          hb')

omit [IsStrictOrderedRing 𝕜] in
theorem stripScan_attained (δ : 𝕜) (ys : List (𝕜 × 𝕜)) (d : 𝕜)
    (h : (stripScan δ ys).ret = some d) : ∃ a b, [a, b] <+ ys ∧ dist2 a b = d := by
  induction ys with
  | nil => simp [stripScan] at h
  | cons p ps ih =>
      simp only [stripScan, ret_bind, ret_pure] at h
      rcases optMin_eq_some h with h | h
      · obtain ⟨q, hq, hd⟩ := scanFrom_attained δ p ps d h
        exact ⟨p, q, List.cons_sublist_cons.2 (List.singleton_sublist.2 hq), hd⟩
      · obtain ⟨a, b, hab, hd⟩ := ih h
        exact ⟨a, b, hab.cons p, hd⟩

/-- **The strip scan bounds every pair with a small vertical gap.** Let $K$ be a linearly ordered
field, write $d(p, q) = (x - x')^2 + (y - y')^2$ for the squared distance between points
$p = (x, y)$ and $q = (x', y')$ of $K^2$, and let $\delta \in K$. Let $ys$ be a list of points in
$K^2$ sorted by second coordinate: whenever an entry precedes another, its second coordinate is at
most the other's. If $a = (a_1, a_2)$ and $b = (b_1, b_2)$ are entries of $ys$ at positions $i < j$
respectively and $(b_2 - a_2)^2 < \delta$, then the strip scan with threshold $\delta$ on $ys$
returns a value $e$ with $e \le d(a, b)$. -/
theorem stripScan_lower (δ : 𝕜) (ys : List (𝕜 × 𝕜)) (hs : ys.Pairwise fun a b => a.2 ≤ b.2)
    (a b : 𝕜 × 𝕜) (hab : [a, b] <+ ys) (hgap : (b.2 - a.2) ^ 2 < δ) :
    ∃ d, (stripScan δ ys).ret = some d ∧ d ≤ dist2 a b := by
  induction ys with
  | nil => simp at hab
  | cons p ps ih =>
      simp only [stripScan, ret_bind, ret_pure]
      rcases pair_sublist_cons hab with h | ⟨rfl, hb⟩
      · exact optMin_le_right _ (ih hs.of_cons h)
      · exact optMin_le_left _ (scanFrom_lower δ a ps hs.of_cons
          (fun q hq => List.rel_of_pairwise_cons hs hq) b hb hgap)

/-! ## Divide and conquer -/

/-- **The closest-pair recursion is correct on lists sorted by first coordinate.** Let $K$ be a
linearly ordered field, write $d(u, v) = (x - x')^2 + (y - y')^2$ for the squared distance between
points $u = (x, y)$ and $v = (x', y')$ of $K^2$, and let $xs$ be a list of points in $K^2$ sorted
by first coordinate: whenever an entry precedes another, its first coordinate is at most the
other's. If the closest-pair recursion returns a value $\delta$ on $xs$, then $\delta = d(p, q)$
for some entries $p$, $q$ of $xs$ at different positions. For any two entries $p$, $q$ of $xs$ at
different positions, the recursion returns a value $\delta$ with $\delta \le d(p, q)$. -/
theorem closestRec_isAnswer (xs : List (𝕜 × 𝕜)) (hs : xs.Pairwise fun a b => a.1 ≤ b.1) :
    IsAnswer xs (closestRec xs).ret := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    rw [closestRec]
    split_ifs with hle
    · exact bruteMin_isAnswer xs
    · simp only [ret_bind]
      have hLR : xs.take (xs.length / 2) ++ xs.drop (xs.length / 2) = xs :=
        List.take_append_drop _ _
      have hLlen : (xs.take (xs.length / 2)).length = xs.length / 2 := by
        simp only [List.length_take]; omega
      have hRlen : (xs.drop (xs.length / 2)).length = xs.length - xs.length / 2 :=
        List.length_drop
      generalize xs.take (xs.length / 2) = L at hLR hLlen ⊢
      generalize xs.drop (xs.length / 2) = R at hLR hRlen ⊢
      have hsLR : (L ++ R).Pairwise fun a b => a.1 ≤ b.1 := by rw [hLR]; exact hs
      have hLsub : L <+ xs := hLR ▸ List.sublist_append_left L R
      have hRsub : R <+ xs := hLR ▸ List.sublist_append_right L R
      have ihL := ih L.length (by omega) L (hs.sublist hLsub) rfl
      have ihR := ih R.length (by omega) R (hs.sublist hRsub) rfl
      -- the right half has a pair, so both halves give a value
      obtain ⟨δ, hδ⟩ : ∃ δ, omin (closestRec L).ret (closestRec R).ret = some δ := by
        match R, hRlen, ihR with
        | a :: b :: rest, _, ihR =>
            obtain ⟨d, hd, -⟩ := ihR.lower a b (by simp)
            obtain ⟨δ, hδ, -⟩ := optMin_le_right (closestRec L).ret ⟨d, hd, le_refl d⟩
            exact ⟨δ, hδ⟩
        | [], h, _ => simp at h; omega
        | [_], h, _ => simp at h; omega
      rw [hδ]
      simp only [ret_bind, ret_pure]
      -- the halves bound every pair inside them by `δ`
      have hδL : ∀ p q, [p, q] <+ L → δ ≤ dist2 p q := fun p q hpq => by
        obtain ⟨δ', h1, h2⟩ := optMin_le_left (closestRec R).ret (ihL.lower p q hpq)
        rw [hδ, Option.some.injEq] at h1
        exact h1 ▸ h2
      have hδR : ∀ p q, [p, q] <+ R → δ ≤ dist2 p q := fun p q hpq => by
        obtain ⟨δ', h1, h2⟩ := optMin_le_right (closestRec L).ret (ihR.lower p q hpq)
        rw [hδ, Option.some.injEq] at h1
        exact h1 ▸ h2
      set xmid := (Option.map Prod.fst L.getLast?).getD 0 with hxmid
      set strip := xs.filter fun p => decide ((p.1 - xmid) ^ 2 < δ) with hstrip
      set ys := strip.mergeSort fun a b => decide (a.2 ≤ b.2) with hys
      have hperm : ys ~ strip := List.mergeSort_perm _ _
      have hsorted : ys.Pairwise fun a b => a.2 ≤ b.2 :=
        (List.pairwise_mergeSort (le := fun a b => decide (a.2 ≤ b.2))
          (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
          (fun a b => by simpa using le_total a.2 b.2) strip).imp (fun h => by simpa using h)
      constructor
      · intro d hd
        rcases optMin_eq_some hd with h1 | h1
        · rw [Option.some.injEq] at h1
          subst h1
          rcases optMin_eq_some hδ with h2 | h2
          · obtain ⟨p, q, hpq, hd⟩ := ihL.attained _ h2
            exact ⟨p, q, hpq.trans hLsub, hd⟩
          · obtain ⟨p, q, hpq, hd⟩ := ihR.attained _ h2
            exact ⟨p, q, hpq.trans hRsub, hd⟩
        · obtain ⟨a, b, hab, hd⟩ := stripScan_attained δ ys d h1
          rcases pair_sublist_of_perm hperm hab with h | h
          · exact ⟨a, b, h.trans List.filter_sublist, hd⟩
          · exact ⟨b, a, h.trans List.filter_sublist, by rw [dist2_comm]; exact hd⟩
      · intro p q hpq
        by_cases hle : δ ≤ dist2 p q
        · exact optMin_le_left _ ⟨δ, rfl, hle⟩
        refine optMin_le_right _ ?_
        rw [not_le] at hle
        obtain ⟨r₁, r₂, hr, h₁, h₂⟩ := List.sublist_append_iff.1 (hLR ▸ hpq)
        match r₁, hr with
        | [], hr =>
            simp only [List.nil_append] at hr
            exact absurd (hδR p q (hr ▸ h₂)) (not_le.2 hle)
        | [x, y], hr =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at hr
            obtain ⟨rfl, rfl, hr⟩ := hr
            exact absurd (hδL _ _ h₁) (not_le.2 hle)
        | _ :: _ :: _ :: _, hr => simp at hr
        | [x], hr =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            have hpL : p ∈ L := List.singleton_sublist.1 h₁
            have hqR : q ∈ R := List.singleton_sublist.1 h₂
            -- the dividing line separates `p` and `q`
            obtain ⟨L', l, hLl⟩ : ∃ L' l, L = L' ++ [l] := by
              rcases List.eq_nil_or_concat L with hL0 | ⟨L', l, hL'⟩
              · simp [hL0] at hpL
              · exact ⟨L', l, by rw [hL', List.concat_eq_append]⟩
            have hx : xmid = l.1 := by simp [hxmid, hLl]
            have hpl : p.1 ≤ l.1 := by
              rw [hLl] at hpL hsLR
              rcases List.mem_append.1 hpL with h | h
              · exact (List.pairwise_append.1 (List.pairwise_append.1 hsLR).1).2.2 p h l
                  List.mem_cons_self
              · rw [List.mem_singleton.1 h]
            have hlq : l.1 ≤ q.1 := (List.pairwise_append.1 hsLR).2.2 l
              (by rw [hLl]; simp) q hqR
            have hdx := sq_sub_fst_le_dist2 p q
            have hpstrip : (p.1 - xmid) ^ 2 < δ := by
              have : (p.1 - xmid) ^ 2 ≤ (p.1 - q.1) ^ 2 := by
                rw [hx, show (p.1 - l.1) ^ 2 = (l.1 - p.1) ^ 2 by ring,
                  show (p.1 - q.1) ^ 2 = (q.1 - p.1) ^ 2 by ring]
                exact pow_le_pow_left₀ (by linarith) (by linarith) 2
              linarith
            have hqstrip : (q.1 - xmid) ^ 2 < δ := by
              have : (q.1 - xmid) ^ 2 ≤ (p.1 - q.1) ^ 2 := by
                rw [hx, show (p.1 - q.1) ^ 2 = (q.1 - p.1) ^ 2 by ring]
                exact pow_le_pow_left₀ (by linarith) (by linarith) 2
              linarith
            have hpq_strip : [p, q] <+ strip := by
              have := hpq.filter fun p => decide ((p.1 - xmid) ^ 2 < δ)
              simpa [hpstrip, hqstrip] using this
            have hgap := sq_sub_snd_le_dist2 p q
            rcases pair_sublist_of_perm hperm.symm hpq_strip with h | h
            · exact stripScan_lower δ ys hsorted p q h (by linarith)
            · obtain ⟨d, hd, hdle⟩ := stripScan_lower δ ys hsorted q p h (by
                rw [show (p.2 - q.2) ^ 2 = (q.2 - p.2) ^ 2 by ring]; linarith)
              exact ⟨d, hd, by rwa [dist2_comm]⟩

/-! ## Correctness -/

/-- **The closest-pair algorithm returns the answer.** Let $K$ be a linearly ordered field, write
$d(p, q) = (x - x')^2 + (y - y')^2$ for the squared distance between points $p = (x, y)$ and
$q = (x', y')$ of $K^2$, and let $ps$ be a list of points in $K^2$. If the divide-and-conquer
closest-pair algorithm returns a value $\delta$ on $ps$, then $\delta = d(p, q)$ for some entries
$p$, $q$ of $ps$ at different positions. For any two entries $p$, $q$ of $ps$ at different
positions, the algorithm returns a value $\delta$ with $\delta \le d(p, q)$. -/
theorem closestPair_isAnswer (ps : List (𝕜 × 𝕜)) : IsAnswer ps (closestPair ps).ret := by
  have hsorted : (ps.mergeSort fun a b => decide (a.1 ≤ b.1)).Pairwise fun a b => a.1 ≤ b.1 :=
    (List.pairwise_mergeSort (le := fun a b => decide (a.1 ≤ b.1))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
      (fun a b => by simpa using le_total a.1 b.1) ps).imp (fun h => by simpa using h)
  exact (closestRec_isAnswer _ hsorted).perm (List.mergeSort_perm _ _)

/-- **Correctness of divide-and-conquer closest pair.** Let $K$ be a linearly ordered field and let
$ps$ be a list of at least two points in $K^2$. Then the divide-and-conquer closest-pair algorithm
returns a value $\delta$, and $\delta$ is the least squared distance between two entries of $ps$
at different positions: some two entries at different positions have squared distance $\delta$,
and any two entries at different positions have squared distance at least $\delta$.

This is the correctness of CLRS Section 33.4, with distances compared squared. -/
theorem closestPair_spec (ps : List (𝕜 × 𝕜)) (hps : 2 ≤ ps.length) :
    ∃ δ, (closestPair ps).ret = some δ ∧ IsMinPairDist2 ps δ := by
  have h := closestPair_isAnswer ps
  match ps, hps with
  | a :: b :: rest, _ =>
      obtain ⟨δ, hδ, -⟩ := h.lower a b (by simp)
      exact ⟨δ, hδ, (hδ ▸ h).isMinPairDist2⟩

/-- **The closest-pair algorithm returns no value exactly on fewer than two points.** Let $K$ be a
linearly ordered field. For every list of points in $K^2$, the divide-and-conquer closest-pair
algorithm returns no value if and only if the list has fewer than two entries. -/
theorem closestPair_eq_none_iff (ps : List (𝕜 × 𝕜)) :
    (closestPair ps).ret = none ↔ ps.length < 2 := by
  constructor
  · intro hnone
    by_contra hlen
    obtain ⟨δ, hδ, -⟩ := closestPair_spec ps (by omega)
    rw [hnone] at hδ
    simp at hδ
  · intro hlen
    cases h : (closestPair ps).ret with
    | none => rfl
    | some δ =>
        obtain ⟨p, q, hpq, -⟩ := (closestPair_isAnswer ps).attained δ h
        have := hpq.length_le
        simp at this
        omega

/-- **Divide and conquer agrees with brute force.** Let $K$ be a linearly ordered field. For every
list of points in $K^2$, the divide-and-conquer closest-pair algorithm returns the same value as
the brute-force scan (their costs may differ). -/
theorem closestPair_eq_bruteMin (ps : List (𝕜 × 𝕜)) :
    (closestPair ps).ret = (bruteMin ps).ret :=
  (closestPair_isAnswer ps).unique (bruteMin_isAnswer ps)

/-! ## Cost of the brute force -/

omit [IsStrictOrderedRing 𝕜] in
theorem minDistFrom_time (p : 𝕜 × 𝕜) (qs : List (𝕜 × 𝕜)) :
    (minDistFrom p qs).time = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      simp only [minDistFrom, time_bind, time_tick, time_pure, ih, List.length_cons]
      omega

omit [IsStrictOrderedRing 𝕜] in
/-- **Cost of the brute-force closest-pair scan.** Let $K$ be a field with a linear order and let
$ps$ be a list of $n$ points in $K^2$. Counting one unit of cost per squared distance computed,
twice the cost of the brute-force scan on $ps$ equals $n(n-1)$; that is, the scan computes exactly
$n(n-1)/2$ squared distances. -/
theorem bruteMin_time (ps : List (𝕜 × 𝕜)) :
    2 * (bruteMin ps).time = ps.length * (ps.length - 1) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [bruteMin, time_bind, time_pure, minDistFrom_time, List.length_cons,
        Nat.add_sub_cancel, Nat.add_zero]
      rcases ps with _ | ⟨q, qs⟩
      · simp [bruteMin]
      · simp only [List.length_cons] at ih ⊢
        rw [Nat.mul_add, ih, Nat.add_sub_cancel]
        ring

end Cslib.Algorithms.Lean.Geometry
