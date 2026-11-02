/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic

/-!
# Van Emde Boas trees (two-level)

A two-level van Emde Boas tree over the universe `Fin (m * m)`, following the
`√u` decomposition behind the proto-van Emde Boas structure of CLRS, third
edition, Chapter 20, Sections 20.1--20.2, with
`u = m * m`. The universe is split into `m` clusters of `m` consecutive
elements each. An element `x` lives in cluster `x / m` (its high half) at
position `x % m` (its low half). A bit vector `summary` of length `m` records
which clusters are nonempty, and `m` bit vectors `clusters`, each of length
`m`, record the elements of each cluster. The representation invariant `Valid`
requires summary bit `i` to be set exactly when cluster `i` is nonempty.

This file deliberately implements the two-level structure only. It is not
the fully recursive van Emde Boas tree of CLRS Section 20.3 over universes
`2 ^ 2 ^ k`, where the summary and each cluster are themselves van Emde Boas
trees; that recursion is deferred. Unlike the recursive structure, the
global minimum is not cached in a separate field and is stored in its cluster
like every other element; `min?`, `max?`, `successor`, and `predecessor` are
computed from the summary and clusters.

## Main definitions

* `VanEmdeBoas` stores the summary vector and the cluster vectors.
* `VanEmdeBoas.empty`, `VanEmdeBoas.insert`, and `VanEmdeBoas.member`
  are the set operations.
* `VanEmdeBoas.min?`, `VanEmdeBoas.max?`, `VanEmdeBoas.successor`, and
  `VanEmdeBoas.predecessor` are the ordered-set queries; each first consults
  one cluster and then the summary, as in CLRS.
* `VanEmdeBoas.Valid` is the summary invariant.
* `VanEmdeBoas.contents` is the `Finset (Fin (m * m))` abstraction.

## Main statements

Membership in an inserted tree is characterized by `member_insert`, and the
empty tree has no members (`member_empty`). Insertion preserves the invariant
(`valid_insert`) and acts on the abstraction as `Finset.insert`
(`contents_insert`). For valid trees, `min?` returns the least stored element
(`min?_eq_some_iff_of_valid`), `max?` returns the greatest stored element
(`max?_eq_some_iff_of_valid`), `successor` returns the least stored element
strictly above its argument (`successor_eq_some_iff_of_valid`), and
`predecessor` returns the greatest stored element strictly below its argument
(`predecessor_eq_some_iff_of_valid`). Each query returns `none` exactly when
no such element exists.

No running-time bound is claimed: this model carries no cost
instrumentation, and the searches below are implemented by linear index
scans. The two-level layout bounds the number of clusters and cluster
entries consulted by `√u`; the `O (lg lg u)` bound of CLRS requires the
deferred recursive structure.

Deletion is not provided; stored sets only grow.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/--
**Two-level van Emde Boas tree.** For a natural number $m$, a two-level van Emde Boas tree over
the universe $\{0, \dots, m^2 - 1\}$ consists of a summary bit vector of length $m$ and, for each
$i < m$, a cluster bit vector of length $m$; bit $j$ of cluster $i$ records whether the element
$im + j$ is stored. Unlike the fully recursive van Emde Boas tree over universes of size
$2^{2^k}$, the summary and the clusters here are plain bit vectors, not van Emde Boas trees.
-/
public structure VanEmdeBoas (m : Nat) where
  /-- Bit `i` records whether cluster `i` contains a stored element. -/
  summary : Fin m → Bool
  /-- `clusters i j` records whether the element `i * m + j` is stored. -/
  clusters : Fin m → Fin m → Bool

namespace VanEmdeBoas

/-- Coordinates `hi, lo < m` index into the square universe `Fin (m * m)`. -/
private lemma combine_bound {m hi lo : Nat} (hhi : hi < m) (hlo : lo < m) :
    hi * m + lo < m * m := by
  have hlt : hi * m + lo < (hi + 1) * m := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left hlo _
  have hle : (hi + 1) * m ≤ m * m := Nat.mul_le_mul (by omega) (Nat.le_refl m)
  exact lt_of_lt_of_le hlt hle

/-- The element of `Fin (m * m)` with high half `hi` and low half `lo`. -/
@[no_expose] private def combine {m : Nat} (hi lo : Fin m) : Fin (m * m) :=
  ⟨hi.val * m + lo.val, combine_bound hi.isLt lo.isLt⟩

/-- The cluster index of `x`, namely `x / m`. -/
@[no_expose] private def high {m : Nat} (x : Fin (m * m)) : Fin m :=
  ⟨x.val / m, by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      exact absurd x.isLt (by simp)
    · exact (Nat.div_lt_iff_lt_mul hm).mpr x.isLt⟩

/-- The position of `x` within its cluster, namely `x % m`. -/
@[no_expose] private def low {m : Nat} (x : Fin (m * m)) : Fin m :=
  ⟨x.val % m, by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      exact absurd x.isLt (by simp)
    · exact Nat.mod_lt _ hm⟩

private lemma combine_val {m : Nat} (hi lo : Fin m) :
    (combine hi lo).val = hi.val * m + lo.val :=
  rfl

private lemma high_val {m : Nat} (x : Fin (m * m)) :
    (high x).val = x.val / m :=
  rfl

private lemma low_val {m : Nat} (x : Fin (m * m)) :
    (low x).val = x.val % m :=
  rfl

/-- Splitting `x` into its high and low halves gives its division expansion. -/
private lemma val_eq_high_low {m : Nat} (x : Fin (m * m)) :
    x.val = (high x).val * m + (low x).val := by
  rw [high_val, low_val, Nat.mul_comm (x.val / m) m, Nat.div_add_mod]

/-- Combining the halves of `x` recovers `x`. -/
private lemma combine_high_low {m : Nat} (x : Fin (m * m)) :
    combine (high x) (low x) = x := by
  apply Fin.ext
  rw [combine_val, high_val, low_val, Nat.mul_comm (x.val / m) m, Nat.div_add_mod]

/-- The high half of a combined pair is its first coordinate. -/
private lemma high_combine {m : Nat} (hi lo : Fin m) :
    high (combine hi lo) = hi := by
  apply Fin.ext
  show (hi.val * m + lo.val) / m = hi.val
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h := hi.isLt
    omega
  · rw [Nat.mul_comm hi.val m, Nat.mul_add_div hm hi.val lo.val,
      Nat.div_eq_of_lt lo.isLt, Nat.add_zero]

/-- The low half of a combined pair is its second coordinate. -/
private lemma low_combine {m : Nat} (hi lo : Fin m) :
    low (combine hi lo) = lo := by
  apply Fin.ext
  show (hi.val * m + lo.val) % m = lo.val
  rw [Nat.add_comm (hi.val * m) lo.val, Nat.mul_comm hi.val m,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lo.isLt]

/-- Elements with the same high and low halves are equal. -/
private lemma eq_of_high_eq_of_low_eq {m : Nat} {x y : Fin (m * m)}
    (hh : high x = high y) (hl : low x = low y) : x = y := by
  conv_lhs => rw [← combine_high_low x]
  conv_rhs => rw [← combine_high_low y]
  rw [hh, hl]

/-- The high half is monotone in the element. -/
private lemma high_mono {m : Nat} {x y : Fin (m * m)} (h : x.val ≤ y.val) :
    (high x).val ≤ (high y).val := by
  rw [high_val, high_val]
  exact Nat.div_le_div_right h

/-- A pair in an earlier cluster precedes every pair in a later cluster. -/
private lemma combine_val_lt_of_high_lt {m : Nat} {hi₁ hi₂ lo₁ lo₂ : Fin m}
    (h : hi₁.val < hi₂.val) :
    (combine hi₁ lo₁).val < (combine hi₂ lo₂).val := by
  rw [combine_val, combine_val]
  have hlt : hi₁.val * m + lo₁.val < (hi₁.val + 1) * m := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left lo₁.isLt _
  have hle : (hi₁.val + 1) * m ≤ hi₂.val * m :=
    Nat.mul_le_mul (by omega) (Nat.le_refl m)
  exact lt_of_lt_of_le hlt (le_trans hle (Nat.le_add_right _ _))

/-- Within one cluster, pairs are ordered by their low halves. -/
private lemma combine_val_le_of_low_le {m : Nat} {hi lo₁ lo₂ : Fin m}
    (h : lo₁.val ≤ lo₂.val) :
    (combine hi lo₁).val ≤ (combine hi lo₂).val := by
  rw [combine_val, combine_val]
  exact Nat.add_le_add_left h _

/-- Tail-recursive forward scan: the least index in `[start, start + fuel)`
satisfying the predicate, if any. The recursive call is in tail position, so
the scan runs in constant stack space. -/
@[no_expose] private def firstBelowAux (p : Nat → Bool) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 => if p i then some i else firstBelowAux p (i + 1) fuel

/-- The least index below the bound satisfying the predicate, if any. -/
@[no_expose] private def firstBelow (p : Nat → Bool) (n : Nat) : Option Nat :=
  firstBelowAux p 0 n

/-- The greatest index below the bound satisfying the predicate, if any. -/
@[no_expose] private def lastBelow (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 => if p n then some n else lastBelow p n

private lemma firstBelowAux_zero (p : Nat → Bool) (s : Nat) :
    firstBelowAux p s 0 = none :=
  rfl

private lemma firstBelowAux_succ (p : Nat → Bool) (s fuel : Nat) :
    firstBelowAux p s (fuel + 1) =
      if p s then some s else firstBelowAux p (s + 1) fuel :=
  rfl

private lemma firstBelow_zero (p : Nat → Bool) : firstBelow p 0 = none :=
  rfl

private lemma lastBelow_zero (p : Nat → Bool) : lastBelow p 0 = none :=
  rfl

private lemma lastBelow_succ (p : Nat → Bool) (n : Nat) :
    lastBelow p (n + 1) = if p n then some n else lastBelow p n :=
  rfl

/-- An index returned by `firstBelowAux` lies in the scanned interval. -/
private lemma firstBelowAux_bounds {p : Nat → Bool} :
    ∀ {fuel s i : Nat}, firstBelowAux p s fuel = some i → s ≤ i ∧ i < s + fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro s i h
      simp [firstBelowAux_zero] at h
  | succ fuel ih =>
      intro s i h
      rw [firstBelowAux_succ] at h
      cases hp : p s with
      | true =>
          simp [hp] at h
          omega
      | false =>
          simp [hp] at h
          have ⟨h1, h2⟩ := ih h
          omega

/-- An index returned by `firstBelowAux` satisfies the predicate. -/
private lemma firstBelowAux_true {p : Nat → Bool} :
    ∀ {fuel s i : Nat}, firstBelowAux p s fuel = some i → p i = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro s i h
      simp [firstBelowAux_zero] at h
  | succ fuel ih =>
      intro s i h
      rw [firstBelowAux_succ] at h
      cases hp : p s with
      | true =>
          simp [hp] at h
          rw [← h]
          exact hp
      | false =>
          simp [hp] at h
          exact ih h

/-- If `firstBelowAux` finds nothing, the predicate fails on the interval. -/
private lemma firstBelowAux_none {p : Nat → Bool} :
    ∀ {fuel s : Nat}, firstBelowAux p s fuel = none →
      ∀ j, s ≤ j → j < s + fuel → p j = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro s _ j _ hj
      omega
  | succ fuel ih =>
      intro s h j hsj hj
      rw [firstBelowAux_succ] at h
      cases hp : p s with
      | true => simp [hp] at h
      | false =>
          simp [hp] at h
          by_cases hjs : j = s
          · rw [hjs]
            exact hp
          · exact ih h j (by omega) (by omega)

/-- An index returned by `firstBelowAux` is least on the scanned interval. -/
private lemma firstBelowAux_le {p : Nat → Bool} :
    ∀ {fuel s i : Nat}, firstBelowAux p s fuel = some i →
      ∀ {j : Nat}, p j = true → s ≤ j → j < s + fuel → i ≤ j := by
  intro fuel
  induction fuel with
  | zero =>
      intro s i h
      simp [firstBelowAux_zero] at h
  | succ fuel ih =>
      intro s i h j hj hsj hjlt
      rw [firstBelowAux_succ] at h
      cases hp : p s with
      | true =>
          simp [hp] at h
          omega
      | false =>
          simp [hp] at h
          by_cases hjs : j = s
          · rw [hjs, hp] at hj
            simp at hj
          · exact ih h hj (by omega) (by omega)

/-- An index returned by `firstBelow` lies below the bound. -/
private lemma firstBelow_lt {p : Nat → Bool} :
    ∀ {n i : Nat}, firstBelow p n = some i → i < n := by
  intro n i h
  have ⟨_, h2⟩ := firstBelowAux_bounds h
  omega

/-- An index returned by `firstBelow` satisfies the predicate. -/
private lemma firstBelow_true {p : Nat → Bool} :
    ∀ {n i : Nat}, firstBelow p n = some i → p i = true :=
  fun h => firstBelowAux_true h

/-- If `firstBelow` finds nothing, the predicate fails below the bound. -/
private lemma firstBelow_none {p : Nat → Bool} :
    ∀ {n : Nat}, firstBelow p n = none → ∀ j < n, p j = false :=
  fun h j hj => firstBelowAux_none h j (Nat.zero_le j) (by omega)

/-- An index returned by `firstBelow` is least among satisfying indices. -/
private lemma firstBelow_le {p : Nat → Bool} :
    ∀ {n i : Nat}, firstBelow p n = some i →
      ∀ {j : Nat}, p j = true → j < n → i ≤ j := by
  intro n i h j hj hjlt
  exact firstBelowAux_le h hj (Nat.zero_le j) (by omega)

/-- If a satisfying index exists below the bound, `firstBelow` returns one. -/
private lemma firstBelow_some_of {p : Nat → Bool} {n j : Nat}
    (hj : j < n) (hp : p j = true) : ∃ i, firstBelow p n = some i := by
  cases h : firstBelow p n with
  | some i => exact ⟨i, rfl⟩
  | none =>
      have hfalse := firstBelow_none h j hj
      simp [hp] at hfalse

/-- An index returned by `lastBelow` lies below the bound. -/
private lemma lastBelow_lt {p : Nat → Bool} :
    ∀ {n i : Nat}, lastBelow p n = some i → i < n := by
  intro n
  induction n with
  | zero =>
      intro i h
      simp [lastBelow_zero] at h
  | succ n ih =>
      intro i h
      rw [lastBelow_succ] at h
      cases hp : p n with
      | true =>
          simp [hp] at h
          omega
      | false =>
          simp [hp] at h
          have hi : i < n := ih h
          omega

/-- An index returned by `lastBelow` satisfies the predicate. -/
private lemma lastBelow_true {p : Nat → Bool} :
    ∀ {n i : Nat}, lastBelow p n = some i → p i = true := by
  intro n
  induction n with
  | zero =>
      intro i h
      simp [lastBelow_zero] at h
  | succ n ih =>
      intro i h
      rw [lastBelow_succ] at h
      cases hp : p n with
      | true =>
          simp [hp] at h
          rw [← h]
          exact hp
      | false =>
          simp [hp] at h
          exact ih h

/-- If `lastBelow` finds nothing, the predicate fails below the bound. -/
private lemma lastBelow_none {p : Nat → Bool} :
    ∀ {n : Nat}, lastBelow p n = none → ∀ j < n, p j = false := by
  intro n
  induction n with
  | zero =>
      intro _ j hj
      exact (Nat.not_lt_zero j hj).elim
  | succ n ih =>
      intro h j hj
      rw [lastBelow_succ] at h
      cases hp : p n with
      | true => simp [hp] at h
      | false =>
          simp [hp] at h
          by_cases hjn : j = n
          · rw [hjn]
            exact hp
          · exact ih h j (by omega)

/-- An index returned by `lastBelow` is greatest among satisfying indices. -/
private lemma lastBelow_ge {p : Nat → Bool} :
    ∀ {n i : Nat}, lastBelow p n = some i →
      ∀ {j : Nat}, p j = true → j < n → j ≤ i := by
  intro n
  induction n with
  | zero =>
      intro i h
      simp [lastBelow_zero] at h
  | succ n ih =>
      intro i h j hj hjlt
      rw [lastBelow_succ] at h
      cases hp : p n with
      | true =>
          simp [hp] at h
          omega
      | false =>
          simp [hp] at h
          by_cases hjn : j = n
          · rw [hjn, hp] at hj
            simp at hj
          · exact ih h hj (by omega)

/-- If a satisfying index exists below the bound, `lastBelow` returns one. -/
private lemma lastBelow_some_of {p : Nat → Bool} {n j : Nat}
    (hj : j < n) (hp : p j = true) : ∃ i, lastBelow p n = some i := by
  cases h : lastBelow p n with
  | some i => exact ⟨i, rfl⟩
  | none =>
      have hfalse := lastBelow_none h j hj
      simp [hp] at hfalse

/-- A `Fin m` predicate read as a `Nat` predicate that fails from `m` on. -/
@[no_expose] private def belowPred {m : Nat} (p : Fin m → Bool) : Nat → Bool :=
  fun j => if hj : j < m then p ⟨j, hj⟩ else false

private lemma belowPred_apply {m : Nat} (p : Fin m → Bool) (i : Fin m) :
    belowPred p i.val = p i := by
  simp [belowPred, i.isLt, Fin.eta]

/-- The least `Fin m` index satisfying the predicate, if any. -/
@[no_expose] private def firstFin? {m : Nat} (p : Fin m → Bool) : Option (Fin m) :=
  (firstBelow (belowPred p) m).bind fun j =>
    if hj : j < m then some ⟨j, hj⟩ else none

/-- The greatest `Fin m` index satisfying the predicate, if any. -/
@[no_expose] private def lastFin? {m : Nat} (p : Fin m → Bool) : Option (Fin m) :=
  (lastBelow (belowPred p) m).bind fun j =>
    if hj : j < m then some ⟨j, hj⟩ else none

/-- `firstFin?` returns `none` when the underlying search does. -/
private lemma firstFin?_eq_none_of {m : Nat} {p : Fin m → Bool}
    (h : firstBelow (belowPred p) m = none) : firstFin? p = none := by
  simp [firstFin?, h]

/-- `firstFin?` returns the underlying search index, given one. -/
private lemma firstFin?_eq_some_of {m : Nat} {p : Fin m → Bool} {j : Nat}
    (h : firstBelow (belowPred p) m = some j) :
    firstFin? p = some ⟨j, firstBelow_lt h⟩ := by
  simp [firstFin?, h, firstBelow_lt h]

/-- `lastFin?` returns `none` when the underlying search does. -/
private lemma lastFin?_eq_none_of {m : Nat} {p : Fin m → Bool}
    (h : lastBelow (belowPred p) m = none) : lastFin? p = none := by
  simp [lastFin?, h]

/-- `lastFin?` returns the underlying search index, given one. -/
private lemma lastFin?_eq_some_of {m : Nat} {p : Fin m → Bool} {j : Nat}
    (h : lastBelow (belowPred p) m = some j) :
    lastFin? p = some ⟨j, lastBelow_lt h⟩ := by
  simp [lastFin?, h, lastBelow_lt h]

/-- An index returned by `firstFin?` satisfies the predicate. -/
private lemma firstFin?_true {m : Nat} {p : Fin m → Bool} {i : Fin m}
    (h : firstFin? p = some i) : p i = true := by
  cases hf : firstBelow (belowPred p) m with
  | none =>
      rw [firstFin?_eq_none_of hf] at h
      simp at h
  | some j =>
      rw [firstFin?_eq_some_of hf] at h
      have hji : j = i.val := congrArg Fin.val (Option.some.inj h)
      have htrue := firstBelow_true hf
      rw [hji, belowPred_apply] at htrue
      exact htrue

/-- An index returned by `firstFin?` is least among satisfying indices. -/
private lemma firstFin?_le {m : Nat} {p : Fin m → Bool} {i j : Fin m}
    (h : firstFin? p = some i) (hj : p j = true) : i.val ≤ j.val := by
  cases hf : firstBelow (belowPred p) m with
  | none =>
      rw [firstFin?_eq_none_of hf] at h
      simp at h
  | some k =>
      rw [firstFin?_eq_some_of hf] at h
      have hki : k = i.val := congrArg Fin.val (Option.some.inj h)
      have hbp : belowPred p j.val = true := by
        rw [belowPred_apply]
        exact hj
      have hle := firstBelow_le hf hbp j.isLt
      omega

/-- If `firstFin?` finds nothing, the predicate fails everywhere. -/
private lemma firstFin?_none {m : Nat} {p : Fin m → Bool}
    (h : firstFin? p = none) (j : Fin m) : p j = false := by
  cases hf : firstBelow (belowPred p) m with
  | some k =>
      rw [firstFin?_eq_some_of hf] at h
      simp at h
  | none =>
      have hfalse := firstBelow_none hf j.val j.isLt
      rwa [belowPred_apply] at hfalse

/-- If a satisfying index exists, `firstFin?` returns one. -/
private lemma firstFin?_some_of {m : Nat} {p : Fin m → Bool} {j : Fin m}
    (hj : p j = true) : ∃ i, firstFin? p = some i := by
  have hbp : belowPred p j.val = true := by
    rw [belowPred_apply]
    exact hj
  obtain ⟨k, hk⟩ := firstBelow_some_of j.isLt hbp
  exact ⟨⟨k, firstBelow_lt hk⟩, firstFin?_eq_some_of hk⟩

/-- An index returned by `lastFin?` satisfies the predicate. -/
private lemma lastFin?_true {m : Nat} {p : Fin m → Bool} {i : Fin m}
    (h : lastFin? p = some i) : p i = true := by
  cases hf : lastBelow (belowPred p) m with
  | none =>
      rw [lastFin?_eq_none_of hf] at h
      simp at h
  | some j =>
      rw [lastFin?_eq_some_of hf] at h
      have hji : j = i.val := congrArg Fin.val (Option.some.inj h)
      have htrue := lastBelow_true hf
      rw [hji, belowPred_apply] at htrue
      exact htrue

/-- An index returned by `lastFin?` is greatest among satisfying indices. -/
private lemma lastFin?_ge {m : Nat} {p : Fin m → Bool} {i j : Fin m}
    (h : lastFin? p = some i) (hj : p j = true) : j.val ≤ i.val := by
  cases hf : lastBelow (belowPred p) m with
  | none =>
      rw [lastFin?_eq_none_of hf] at h
      simp at h
  | some k =>
      rw [lastFin?_eq_some_of hf] at h
      have hki : k = i.val := congrArg Fin.val (Option.some.inj h)
      have hbp : belowPred p j.val = true := by
        rw [belowPred_apply]
        exact hj
      have hle := lastBelow_ge hf hbp j.isLt
      omega

/-- If `lastFin?` finds nothing, the predicate fails everywhere. -/
private lemma lastFin?_none {m : Nat} {p : Fin m → Bool}
    (h : lastFin? p = none) (j : Fin m) : p j = false := by
  cases hf : lastBelow (belowPred p) m with
  | some k =>
      rw [lastFin?_eq_some_of hf] at h
      simp at h
  | none =>
      have hfalse := lastBelow_none hf j.val j.isLt
      rwa [belowPred_apply] at hfalse

/-- If a satisfying index exists, `lastFin?` returns one. -/
private lemma lastFin?_some_of {m : Nat} {p : Fin m → Bool} {j : Fin m}
    (hj : p j = true) : ∃ i, lastFin? p = some i := by
  have hbp : belowPred p j.val = true := by
    rw [belowPred_apply]
    exact hj
  obtain ⟨k, hk⟩ := lastBelow_some_of j.isLt hbp
  exact ⟨⟨k, lastBelow_lt hk⟩, lastFin?_eq_some_of hk⟩

/-- **Empty van Emde Boas tree.** For a natural number $m$, the empty van Emde Boas tree over
the universe $\{0, 1, \dots, m^2 - 1\}$ is the tree in which all $m$ summary bits and all
$m^2$ cluster bits ($m$ clusters of $m$ bits each) are unset. -/
public def empty {m : Nat} : VanEmdeBoas m where
  summary := fun _ => false
  clusters := fun _ _ => false

/-- **Membership in a van Emde Boas tree.** An element $x$ of the universe
$\{0, 1, \dots, m^2 - 1\}$ is a member of a two-level van Emde Boas tree $t$ when bit
$x \bmod m$ of cluster $\lfloor x / m \rfloor$ of $t$ is set. The summary bits are not consulted. -/
public def member {m : Nat} (t : VanEmdeBoas m) (x : Fin (m * m)) : Bool :=
  t.clusters (high x) (low x)

/-- **Insertion into a van Emde Boas tree.** Let $m$ be a natural number, let $t$ be a van Emde
Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$ and let $x$ be an element of the
universe. Inserting $x$ into $t$ gives the tree obtained from $t$ by setting bit $x \bmod m$ of
cluster $\lfloor x / m \rfloor$ and summary bit $\lfloor x / m \rfloor$, leaving every other bit
unchanged. -/
public def insert {m : Nat} (x : Fin (m * m)) (t : VanEmdeBoas m) :
    VanEmdeBoas m where
  summary := Function.update t.summary (high x) true
  clusters := Function.update t.clusters (high x)
    (Function.update (t.clusters (high x)) (low x) true)

/-- **Summary invariant of a van Emde Boas tree.** A two-level van Emde Boas tree $t$ with $m$
clusters is valid when, for every cluster index $i < m$, summary bit $i$ of $t$ is set exactly when
cluster $i$ of $t$ is nonempty, that is, when some bit $j < m$ of cluster $i$ is set. -/
public def Valid {m : Nat} (t : VanEmdeBoas m) : Prop :=
  ∀ i : Fin m, t.summary i = true ↔ ∃ j : Fin m, t.clusters i j = true

/-- **Set of stored elements of a van Emde Boas tree.** Let $m$ be a natural number. For a van
Emde Boas tree $t$ over the universe $\{0, 1, \dots, m^2 - 1\}$, the set of stored elements of
$t$ is the finite set of those elements of the universe that are members of $t$. -/
public def contents {m : Nat} (t : VanEmdeBoas m) : Finset (Fin (m * m)) :=
  Finset.univ.filter fun x => t.member x = true

private lemma empty_summary {m : Nat} :
    (empty : VanEmdeBoas m).summary = fun _ => false :=
  rfl

private lemma empty_clusters {m : Nat} :
    (empty : VanEmdeBoas m).clusters = fun _ _ => false :=
  rfl

private lemma insert_summary {m : Nat} (x : Fin (m * m)) (t : VanEmdeBoas m) :
    (insert x t).summary = Function.update t.summary (high x) true :=
  rfl

private lemma insert_clusters {m : Nat} (x : Fin (m * m)) (t : VanEmdeBoas m) :
    (insert x t).clusters = Function.update t.clusters (high x)
      (Function.update (t.clusters (high x)) (low x) true) :=
  rfl

/-- **The empty van Emde Boas tree has no members.** For every $m$ and every $x$ in the universe
$\{0, 1, \dots, m^2 - 1\}$, $x$ is not a member of the empty two-level van Emde Boas tree over that
universe. -/
public theorem member_empty {m : Nat} (x : Fin (m * m)) :
    (empty : VanEmdeBoas m).member x = false := by
  simp [member, empty_clusters]

/-- **An inserted element is a member of a van Emde Boas tree.** For every two-level van Emde Boas
tree $t$ over the universe $\{0, 1, \dots, m^2 - 1\}$ and every $x$ in that universe, $x$ is a
member of the tree obtained by inserting $x$ into $t$. -/
public theorem member_insert_self {m : Nat} (x : Fin (m * m))
    (t : VanEmdeBoas m) : (insert x t).member x = true := by
  simp [member, insert_clusters]

/-- **Insertion into a van Emde Boas tree leaves other elements unchanged.** For every two-level
van Emde Boas tree $t$ over the universe $\{0, 1, \dots, m^2 - 1\}$ and all $x \ne y$ in that
universe, $y$ is a member of the tree obtained by inserting $x$ into $t$ if and only if $y$ is a
member of $t$. -/
public theorem member_insert_of_ne {m : Nat} {x y : Fin (m * m)}
    (h : y ≠ x) (t : VanEmdeBoas m) :
    (insert x t).member y = t.member y := by
  simp only [member, insert_clusters]
  by_cases hh : high y = high x
  · have hl : low y ≠ low x := fun hle => h (eq_of_high_eq_of_low_eq hh hle)
    rw [hh, Function.update_self, Function.update_of_ne hl]
  · rw [Function.update_of_ne hh]

/-- **Membership after insertion into a van Emde Boas tree.** For every two-level van Emde Boas
tree $t$ over the universe $\{0, 1, \dots, m^2 - 1\}$ and all $x, y$ in that universe, $y$ is a
member of the tree obtained by inserting $x$ into $t$ if and only if $y = x$ or $y$ is a member
of $t$. -/
public theorem member_insert {m : Nat} (t : VanEmdeBoas m)
    (x y : Fin (m * m)) :
    (insert x t).member y = true ↔ y = x ∨ t.member y = true := by
  by_cases h : y = x
  · subst h
    simp [member_insert_self]
  · rw [member_insert_of_ne h]
    simp [h]

/-- **Insertion into a van Emde Boas tree keeps existing members.** For every two-level van Emde
Boas tree $t$ over the universe $\{0, 1, \dots, m^2 - 1\}$ and all $x, y$ in that universe, if $y$
is a member of $t$, then $y$ is a member of the tree obtained by inserting $x$ into $t$. -/
public theorem member_insert_of_member {m : Nat} (t : VanEmdeBoas m)
    (x y : Fin (m * m)) (h : t.member y = true) :
    (insert x t).member y = true :=
  (member_insert t x y).mpr (Or.inr h)

/-- **The empty van Emde Boas tree is valid.** For every natural number $m$, the empty two-level
van Emde Boas tree over the universe $\{0, \dots, m^2 - 1\}$ satisfies the summary invariant: each
summary bit is set exactly when its cluster is nonempty. -/
public theorem valid_empty {m : Nat} : (empty : VanEmdeBoas m).Valid := by
  intro i
  simp [empty_summary, empty_clusters]

/-- **Insertion preserves validity of van Emde Boas trees.** For every natural number $m$, every
element $x$ of the universe $\{0, \dots, m^2 - 1\}$ and every two-level van Emde Boas tree $t$ over
that universe that satisfies the summary invariant (each summary bit is set exactly when its
cluster is nonempty), the tree obtained from $t$ by inserting $x$ also satisfies the summary
invariant. -/
public theorem valid_insert {m : Nat} (x : Fin (m * m))
    (t : VanEmdeBoas m) (hv : t.Valid) : (insert x t).Valid := by
  intro i
  by_cases hi : i = high x
  · subst hi
    rw [insert_summary, insert_clusters, Function.update_self,
      Function.update_self]
    constructor
    · intro _
      exact ⟨low x, by simp⟩
    · intro _
      rfl
  · rw [insert_summary, insert_clusters, Function.update_of_ne hi,
      Function.update_of_ne hi]
    exact hv i

/-- **The contents of a van Emde Boas tree are its members.** For every two-level van Emde Boas
tree $t$ over the universe $\{0, 1, \dots, m^2 - 1\}$ and every $x$ in that universe, $x$ belongs
to the finite set of stored elements of $t$ if and only if $x$ is a member of $t$. -/
@[simp]
public theorem mem_contents {m : Nat} {t : VanEmdeBoas m} {x : Fin (m * m)} :
    x ∈ t.contents ↔ t.member x = true := by
  simp [contents]

/-- **Contents of the empty van Emde Boas tree.** For every natural number $m$, the set of
stored elements of the empty van Emde Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$
is empty. -/
@[simp]
public theorem contents_empty {m : Nat} :
    (empty : VanEmdeBoas m).contents = ∅ := by
  ext x
  simp [member_empty]

/-- **Contents after insertion into a van Emde Boas tree.** Let $m$ be a natural number, let
$t$ be a van Emde Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$ and let $x$ be an
element of the universe. The set of stored elements of the tree obtained by inserting $x$ into
$t$ is the set of stored elements of $t$ together with $x$. No validity assumption on $t$ is
needed. -/
public theorem contents_insert {m : Nat} (x : Fin (m * m))
    (t : VanEmdeBoas m) :
    (insert x t).contents = Insert.insert x t.contents := by
  ext y
  simp [member_insert, eq_comm (a := y) (b := x)]

/-- **Minimum query of a van Emde Boas tree.** Let $t$ be a two-level van Emde Boas tree over the
universe $\{0, \dots, m^2 - 1\}$. If some summary bit of $t$ is set, let $h$ be the least cluster
index whose summary bit is set; if cluster $h$ has a set position, let $\ell$ be the least one.
The minimum query on $t$ then returns the element $h \cdot m + \ell$. If no summary bit is set,
or cluster $h$ has no set position, it returns no element.

In a valid tree this is the least stored element. -/
public def min? {m : Nat} (t : VanEmdeBoas m) : Option (Fin (m * m)) :=
  match firstFin? t.summary with
  | none => none
  | some hi =>
    match firstFin? (t.clusters hi) with
    | none => none
    | some lo => some (combine hi lo)

/-- Given the two search results, `min?` returns the combined pair. -/
private lemma min?_eq_some_of {m : Nat} {t : VanEmdeBoas m} {hi lo : Fin m}
    (hs : firstFin? t.summary = some hi)
    (hc : firstFin? (t.clusters hi) = some lo) :
    t.min? = some (combine hi lo) := by
  simp [min?, hs, hc]

/-- A value returned by `min?` comes from the two searches. -/
private lemma min?_eq_some_cases {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} (h : t.min? = some x) :
    ∃ hi lo : Fin m, firstFin? t.summary = some hi ∧
      firstFin? (t.clusters hi) = some lo ∧ x = combine hi lo := by
  cases hs : firstFin? t.summary with
  | none => simp [min?, hs] at h
  | some hi =>
      cases hc : firstFin? (t.clusters hi) with
      | none => simp [min?, hs, hc] at h
      | some lo =>
          rw [min?_eq_some_of hs hc] at h
          exact ⟨hi, lo, rfl, hc, (Option.some.inj h).symm⟩

/-- **The van Emde Boas minimum is stored.** Let $t$ be a two-level van Emde Boas tree over the
universe $\{0, \dots, m^2 - 1\}$. If the minimum query on $t$ returns $x$, then $x$ is stored in
$t$. -/
public theorem min?_mem {m : Nat} {t : VanEmdeBoas m} {x : Fin (m * m)}
    (h : t.min? = some x) : t.member x = true := by
  obtain ⟨hi, lo, _, hc, rfl⟩ := min?_eq_some_cases h
  simp only [member, high_combine, low_combine]
  exact firstFin?_true hc

/-- **The van Emde Boas minimum is a lower bound.** Let $t$ be a valid two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$. If the minimum query on $t$ returns $x$, then
$x \le y$ for every $y$ stored in $t$. -/
public theorem min?_least {m : Nat} {t : VanEmdeBoas m} (hv : t.Valid)
    {x y : Fin (m * m)} (h : t.min? = some x) (hy : t.member y = true) :
    x.val ≤ y.val := by
  obtain ⟨hi, lo, hs, hc, rfl⟩ := min?_eq_some_cases h
  have hmem : t.clusters (high y) (low y) = true := hy
  have hsum : t.summary (high y) = true := (hv (high y)).mpr ⟨low y, hmem⟩
  have hle : hi.val ≤ (high y).val := firstFin?_le hs hsum
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hlt' := combine_val_lt_of_high_lt (lo₁ := lo) (lo₂ := low y) hlt
    rw [combine_high_low] at hlt'
    exact hlt'.le
  · have hhieq : hi = high y := Fin.ext heq
    have hcl : t.clusters hi (low y) = true := hhieq ▸ hmem
    have hlo : lo.val ≤ (low y).val := firstFin?_le hc hcl
    have hle' := combine_val_le_of_low_le (hi := hi) hlo
    have hcy : combine hi (low y) = y := by
      rw [hhieq]
      exact combine_high_low y
    rw [hcy] at hle'
    exact hle'

/-- **Empty minimum query in a van Emde Boas tree.** Let $t$ be a valid two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$. The minimum query on $t$ returns no element if and
only if no element of the universe is stored in $t$. -/
public theorem min?_eq_none_iff {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) :
    t.min? = none ↔ ∀ y : Fin (m * m), t.member y = false := by
  constructor
  · intro h y
    cases hm : t.member y with
    | false => rfl
    | true =>
        have hmem : t.clusters (high y) (low y) = true := hm
        have hsum : t.summary (high y) = true :=
          (hv (high y)).mpr ⟨low y, hmem⟩
        obtain ⟨hi, hs⟩ := firstFin?_some_of hsum
        have hsumhi : t.summary hi = true := firstFin?_true hs
        obtain ⟨lo₀, hlo₀⟩ := (hv hi).mp hsumhi
        obtain ⟨lo, hc⟩ := firstFin?_some_of hlo₀
        rw [min?_eq_some_of hs hc] at h
        simp at h
  · intro h
    cases hs : firstFin? t.summary with
    | none => simp [min?, hs]
    | some hi =>
        have hsumhi : t.summary hi = true := firstFin?_true hs
        obtain ⟨lo, hlo⟩ := (hv hi).mp hsumhi
        have hmember : t.member (combine hi lo) = true := by
          simp only [member, high_combine, low_combine]
          exact hlo
        rw [h (combine hi lo)] at hmember
        simp at hmember

/-- **Characterization of the van Emde Boas minimum.** Let $t$ be a valid two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$, and let $x$ be in the universe. The minimum query
on $t$ returns $x$ if and only if $x$ is stored in $t$ and $x \le y$ for every $y$ stored in $t$. -/
public theorem min?_eq_some_iff_of_valid {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) {x : Fin (m * m)} :
    t.min? = some x ↔
      t.member x = true ∧
        ∀ y : Fin (m * m), t.member y = true → x.val ≤ y.val := by
  constructor
  · intro h
    exact ⟨min?_mem h, fun y hy => min?_least hv h hy⟩
  · rintro ⟨hx, hleast⟩
    have hne : t.min? ≠ none := by
      intro hnone
      rw [min?_eq_none_iff hv] at hnone
      rw [hnone x] at hx
      simp at hx
    obtain ⟨x', hx'⟩ : ∃ x' : Fin (m * m), t.min? = some x' := by
      cases h' : t.min? with
      | none => exact (hne h').elim
      | some a => exact ⟨a, rfl⟩
    have h1 : x'.val ≤ x.val := min?_least hv hx' hx
    have h2 : x.val ≤ x'.val := hleast x' (min?_mem hx')
    have heq : x = x' := Fin.ext (le_antisymm h2 h1)
    rw [heq]
    exact hx'

/-- **The empty van Emde Boas tree has no minimum.** For every $m$, the minimum query of the empty
two-level van Emde Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$ returns no element. -/
public theorem min?_empty {m : Nat} : (empty : VanEmdeBoas m).min? = none :=
  (min?_eq_none_iff valid_empty).mpr fun y => member_empty y

/-- **Minimum of a one-element van Emde Boas tree.** For every $x$ in the universe
$\{0, \dots, m^2 - 1\}$, the minimum query on the two-level van Emde Boas tree obtained by
inserting $x$ into the empty tree returns $x$. -/
public theorem min?_insert_empty {m : Nat} (x : Fin (m * m)) :
    (insert x empty).min? = some x := by
  rw [min?_eq_some_iff_of_valid (valid_insert x _ valid_empty)]
  refine ⟨member_insert_self x _, fun y hy => ?_⟩
  rw [member_insert] at hy
  cases hy with
  | inl h =>
      rw [h]
  | inr h =>
      rw [member_empty] at h
      simp at h

/-- **Maximum query of a van Emde Boas tree.** For a two-level van Emde Boas tree $t$ over the
universe $\{0, 1, \dots, m^2 - 1\}$, the maximum query first finds the greatest index $i < m$ whose
summary bit is set, and then the greatest index $j < m$ whose bit is set in cluster $i$; it returns
the element $i m + j$. It returns no element if no summary bit is set, or if no bit of cluster $i$
is set. When the summary bits record exactly the nonempty clusters, this is the greatest stored
element. -/
public def max? {m : Nat} (t : VanEmdeBoas m) : Option (Fin (m * m)) :=
  match lastFin? t.summary with
  | none => none
  | some hi =>
    match lastFin? (t.clusters hi) with
    | none => none
    | some lo => some (combine hi lo)

/-- Given the two search results, `max?` returns the combined pair. -/
private lemma max?_eq_some_of {m : Nat} {t : VanEmdeBoas m} {hi lo : Fin m}
    (hs : lastFin? t.summary = some hi)
    (hc : lastFin? (t.clusters hi) = some lo) :
    t.max? = some (combine hi lo) := by
  simp [max?, hs, hc]

/-- A value returned by `max?` comes from the two searches. -/
private lemma max?_eq_some_cases {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} (h : t.max? = some x) :
    ∃ hi lo : Fin m, lastFin? t.summary = some hi ∧
      lastFin? (t.clusters hi) = some lo ∧ x = combine hi lo := by
  cases hs : lastFin? t.summary with
  | none => simp [max?, hs] at h
  | some hi =>
      cases hc : lastFin? (t.clusters hi) with
      | none => simp [max?, hs, hc] at h
      | some lo =>
          rw [max?_eq_some_of hs hc] at h
          exact ⟨hi, lo, rfl, hc, (Option.some.inj h).symm⟩

/-- **The maximum query of a van Emde Boas tree returns a member.** For every two-level van Emde
Boas tree $t$ over the universe $\{0, 1, \dots, m^2 - 1\}$ and every $x$ in that universe, if the
maximum query of $t$ returns $x$, then $x$ is a member of $t$. No validity hypothesis on $t$ is
needed. -/
public theorem max?_mem {m : Nat} {t : VanEmdeBoas m} {x : Fin (m * m)}
    (h : t.max? = some x) : t.member x = true := by
  obtain ⟨hi, lo, _, hc, rfl⟩ := max?_eq_some_cases h
  simp only [member, high_combine, low_combine]
  exact lastFin?_true hc

/-- **The van Emde Boas maximum query bounds every member.** Let $m$ be a natural number and let
$t$ be a valid van Emde Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$. If the maximum
query on $t$ returns $x$, then $y \le x$ for every member $y$ of $t$. -/
public theorem max?_greatest {m : Nat} {t : VanEmdeBoas m} (hv : t.Valid)
    {x y : Fin (m * m)} (h : t.max? = some x) (hy : t.member y = true) :
    y.val ≤ x.val := by
  obtain ⟨hi, lo, hs, hc, rfl⟩ := max?_eq_some_cases h
  have hmem : t.clusters (high y) (low y) = true := hy
  have hsum : t.summary (high y) = true := (hv (high y)).mpr ⟨low y, hmem⟩
  have hle : (high y).val ≤ hi.val := lastFin?_ge hs hsum
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hlt' := combine_val_lt_of_high_lt (lo₁ := low y) (lo₂ := lo) hlt
    rw [combine_high_low] at hlt'
    exact hlt'.le
  · have hhieq : hi = high y := Fin.ext heq.symm
    have hcl : t.clusters hi (low y) = true := hhieq ▸ hmem
    have hlo : (low y).val ≤ lo.val := lastFin?_ge hc hcl
    have hle' := combine_val_le_of_low_le (hi := hi) hlo
    have hcy : combine hi (low y) = y := by
      rw [hhieq]
      exact combine_high_low y
    rw [hcy] at hle'
    exact hle'

/-- **When the van Emde Boas maximum query returns nothing.** Let $m$ be a natural number and let
$t$ be a valid van Emde Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$. The maximum query
on $t$ returns no element if and only if no element of the universe is a member of $t$. -/
public theorem max?_eq_none_iff {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) :
    t.max? = none ↔ ∀ y : Fin (m * m), t.member y = false := by
  constructor
  · intro h y
    cases hm : t.member y with
    | false => rfl
    | true =>
        have hmem : t.clusters (high y) (low y) = true := hm
        have hsum : t.summary (high y) = true :=
          (hv (high y)).mpr ⟨low y, hmem⟩
        obtain ⟨hi, hs⟩ := lastFin?_some_of hsum
        have hsumhi : t.summary hi = true := lastFin?_true hs
        obtain ⟨lo₀, hlo₀⟩ := (hv hi).mp hsumhi
        obtain ⟨lo, hc⟩ := lastFin?_some_of hlo₀
        rw [max?_eq_some_of hs hc] at h
        simp at h
  · intro h
    cases hs : lastFin? t.summary with
    | none => simp [max?, hs]
    | some hi =>
        have hsumhi : t.summary hi = true := lastFin?_true hs
        obtain ⟨lo, hlo⟩ := (hv hi).mp hsumhi
        have hmember : t.member (combine hi lo) = true := by
          simp only [member, high_combine, low_combine]
          exact hlo
        rw [h (combine hi lo)] at hmember
        simp at hmember

/-- **Correctness of the van Emde Boas maximum query.** Let $m$ be a natural number, let $t$ be a
valid van Emde Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$ and let $x$ be an element of
the universe. The maximum query on $t$ returns $x$ if and only if $x$ is a member of $t$ and
$y \le x$ for every member $y$ of $t$. -/
public theorem max?_eq_some_iff_of_valid {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) {x : Fin (m * m)} :
    t.max? = some x ↔
      t.member x = true ∧
        ∀ y : Fin (m * m), t.member y = true → y.val ≤ x.val := by
  constructor
  · intro h
    exact ⟨max?_mem h, fun y hy => max?_greatest hv h hy⟩
  · rintro ⟨hx, hgreatest⟩
    have hne : t.max? ≠ none := by
      intro hnone
      rw [max?_eq_none_iff hv] at hnone
      rw [hnone x] at hx
      simp at hx
    obtain ⟨x', hx'⟩ : ∃ x' : Fin (m * m), t.max? = some x' := by
      cases h' : t.max? with
      | none => exact (hne h').elim
      | some a => exact ⟨a, rfl⟩
    have h1 : x.val ≤ x'.val := max?_greatest hv hx' hx
    have h2 : x'.val ≤ x.val := hgreatest x' (max?_mem hx')
    have heq : x = x' := Fin.ext (le_antisymm h1 h2)
    rw [heq]
    exact hx'

/-- **Maximum query on the empty van Emde Boas tree.** For every natural number $m$, the
maximum query on the empty van Emde Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$
returns no element. -/
public theorem max?_empty {m : Nat} : (empty : VanEmdeBoas m).max? = none :=
  (max?_eq_none_iff valid_empty).mpr fun y => member_empty y

/-- **Maximum query on a one-element van Emde Boas tree.** Let $m$ be a natural number and let
$x$ be an element of the universe $\{0, 1, \dots, m^2 - 1\}$. The maximum query on the tree
obtained by inserting $x$ into the empty van Emde Boas tree over this universe returns $x$. -/
public theorem max?_insert_empty {m : Nat} (x : Fin (m * m)) :
    (insert x empty).max? = some x := by
  rw [max?_eq_some_iff_of_valid (valid_insert x _ valid_empty)]
  refine ⟨member_insert_self x _, fun y hy => ?_⟩
  rw [member_insert] at hy
  cases hy with
  | inl h =>
      rw [h]
  | inr h =>
      rw [member_empty] at h
      simp at h

/-- Within one cluster, elements are ordered by their low halves. -/
private lemma low_lt_of_lt_of_high_eq {m : Nat} {x z : Fin (m * m)}
    (hxz : x.val < z.val) (hh : (high x).val = (high z).val) :
    (low x).val < (low z).val := by
  have hx := val_eq_high_low x
  have hz := val_eq_high_low z
  rw [← hh] at hz
  omega

/-- Positions past `low x` that are set in the cluster of `x`. -/
@[no_expose] private def succClusterPred {m : Nat} (t : VanEmdeBoas m)
    (x : Fin (m * m)) : Fin m → Bool :=
  fun lo => decide ((low x).val < lo.val) && t.clusters (high x) lo

/-- Clusters past `high x` that the summary marks nonempty. -/
@[no_expose] private def succSummaryPred {m : Nat} (t : VanEmdeBoas m)
    (x : Fin (m * m)) : Fin m → Bool :=
  fun hi => decide ((high x).val < hi.val) && t.summary hi

/-- Positions before `low x` that are set in the cluster of `x`. -/
@[no_expose] private def predClusterPred {m : Nat} (t : VanEmdeBoas m)
    (x : Fin (m * m)) : Fin m → Bool :=
  fun lo => decide (lo.val < (low x).val) && t.clusters (high x) lo

/-- Clusters before `high x` that the summary marks nonempty. -/
@[no_expose] private def predSummaryPred {m : Nat} (t : VanEmdeBoas m)
    (x : Fin (m * m)) : Fin m → Bool :=
  fun hi => decide (hi.val < (high x).val) && t.summary hi

private lemma succClusterPred_eq_true {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} {lo : Fin m} :
    succClusterPred t x lo = true ↔
      (low x).val < lo.val ∧ t.clusters (high x) lo = true := by
  simp [succClusterPred]

private lemma succSummaryPred_eq_true {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} {hi : Fin m} :
    succSummaryPred t x hi = true ↔
      (high x).val < hi.val ∧ t.summary hi = true := by
  simp [succSummaryPred]

private lemma predClusterPred_eq_true {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} {lo : Fin m} :
    predClusterPred t x lo = true ↔
      lo.val < (low x).val ∧ t.clusters (high x) lo = true := by
  simp [predClusterPred]

private lemma predSummaryPred_eq_true {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} {hi : Fin m} :
    predSummaryPred t x hi = true ↔
      hi.val < (high x).val ∧ t.summary hi = true := by
  simp [predSummaryPred]

/-- **Successor query in a two-level van Emde Boas tree.** Let $T$ be a two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$ and let $x = hm + \ell$ with $0 \le h, \ell < m$, so
that $x$ sits at position $\ell$ of cluster $h$. If cluster $h$ has a set position after $\ell$, the
successor of $x$ in $T$ is $hm + \ell'$ for the least such position $\ell'$. Otherwise, let $h'$ be
the least cluster index with $h < h'$ whose summary bit is set; the successor is $h'm + \ell''$ for
the least position $\ell''$ set in cluster $h'$. If there is no such $h'$, or cluster $h'$ has no
set position, $x$ has no successor.

In a valid tree, the successor of $x$ is the least member of $T$ greater than $x$. -/
public def successor {m : Nat} (t : VanEmdeBoas m) (x : Fin (m * m)) :
    Option (Fin (m * m)) :=
  match firstFin? (succClusterPred t x) with
  | some lo => some (combine (high x) lo)
  | none =>
    match firstFin? (succSummaryPred t x) with
    | none => none
    | some hi =>
      match firstFin? (t.clusters hi) with
      | none => none
      | some lo => some (combine hi lo)

/-- Given a set position later in the cluster of `x`, `successor` returns it. -/
private lemma successor_eq_some_cluster {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} {lo : Fin m}
    (h : firstFin? (succClusterPred t x) = some lo) :
    t.successor x = some (combine (high x) lo) := by
  simp [successor, h]

/-- Given the summary and cluster searches, `successor` returns their pair. -/
private lemma successor_eq_some_next {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} {hi lo : Fin m}
    (h1 : firstFin? (succClusterPred t x) = none)
    (h2 : firstFin? (succSummaryPred t x) = some hi)
    (h3 : firstFin? (t.clusters hi) = some lo) :
    t.successor x = some (combine hi lo) := by
  simp [successor, h1, h2, h3]

/-- A value returned by `successor` comes from one of its two searches. -/
private lemma successor_eq_some_cases {m : Nat} {t : VanEmdeBoas m}
    {x y : Fin (m * m)} (h : t.successor x = some y) :
    (∃ lo : Fin m, firstFin? (succClusterPred t x) = some lo ∧
        y = combine (high x) lo) ∨
      (firstFin? (succClusterPred t x) = none ∧
        ∃ hi lo : Fin m, firstFin? (succSummaryPred t x) = some hi ∧
          firstFin? (t.clusters hi) = some lo ∧ y = combine hi lo) := by
  cases h1 : firstFin? (succClusterPred t x) with
  | some lo =>
      refine Or.inl ⟨lo, rfl, ?_⟩
      rw [successor_eq_some_cluster h1] at h
      exact (Option.some.inj h).symm
  | none =>
      cases h2 : firstFin? (succSummaryPred t x) with
      | none => simp [successor, h1, h2] at h
      | some hi =>
          cases h3 : firstFin? (t.clusters hi) with
          | none => simp [successor, h1, h2, h3] at h
          | some lo =>
              refine Or.inr ⟨rfl, hi, lo, rfl, h3, ?_⟩
              rw [successor_eq_some_next h1 h2 h3] at h
              exact (Option.some.inj h).symm

/-- **The van Emde Boas successor is stored.** Let $T$ be a two-level van Emde Boas tree over the
universe $\{0, \dots, m^2 - 1\}$, not necessarily valid, and let $x$ and $y$ be elements of the
universe. If the successor of $x$ in $T$ is $y$, then $y$ is a member of $T$. -/
public theorem successor_mem {m : Nat} {t : VanEmdeBoas m}
    {x y : Fin (m * m)} (h : t.successor x = some y) :
    t.member y = true := by
  rcases successor_eq_some_cases h with ⟨lo, h1, rfl⟩ | ⟨_, hi, lo, _, hc, rfl⟩
  · have hcl : t.clusters (high x) lo = true :=
      (succClusterPred_eq_true.mp (firstFin?_true h1)).2
    simp only [member, high_combine, low_combine]
    exact hcl
  · simp only [member, high_combine, low_combine]
    exact firstFin?_true hc

/-- **The van Emde Boas successor is strictly larger than its argument.** Let $T$ be a two-level
van Emde Boas tree over the universe $\{0, \dots, m^2 - 1\}$, not necessarily valid, and let $x$
and $y$ be elements of the universe. If the successor of $x$ in $T$ is $y$, then $x < y$. -/
public theorem successor_gt {m : Nat} {t : VanEmdeBoas m}
    {x y : Fin (m * m)} (h : t.successor x = some y) :
    x.val < y.val := by
  rcases successor_eq_some_cases h with ⟨lo, h1, rfl⟩ | ⟨_, hi, lo, h2, _, rfl⟩
  · have hlt : (low x).val < lo.val :=
      (succClusterPred_eq_true.mp (firstFin?_true h1)).1
    rw [combine_val, val_eq_high_low x]
    omega
  · have hlt : (high x).val < hi.val :=
      (succSummaryPred_eq_true.mp (firstFin?_true h2)).1
    have hlt' := combine_val_lt_of_high_lt (lo₁ := low x) (lo₂ := lo) hlt
    rw [combine_high_low] at hlt'
    exact hlt'

/-- **No member lies strictly between an element and its van Emde Boas successor.** Let $T$ be a
valid two-level van Emde Boas tree over the universe $\{0, \dots, m^2 - 1\}$ and let $x$, $y$, $z$
be elements of the universe. If the successor of $x$ in $T$ is $y$ and $z$ is a member of $T$ with
$x < z$, then $y \le z$. -/
public theorem successor_least {m : Nat} {t : VanEmdeBoas m} (hv : t.Valid)
    {x y z : Fin (m * m)} (h : t.successor x = some y)
    (hz : t.member z = true) (hxz : x.val < z.val) :
    y.val ≤ z.val := by
  have hmem : t.clusters (high z) (low z) = true := hz
  have hsum : t.summary (high z) = true := (hv (high z)).mpr ⟨low z, hmem⟩
  have hmono : (high x).val ≤ (high z).val := high_mono hxz.le
  rcases successor_eq_some_cases h with ⟨lo, h1, rfl⟩ |
    ⟨h1none, hi, lo, h2, hc, rfl⟩
  · rcases lt_or_eq_of_le hmono with hlt | heq
    · have hlt' := combine_val_lt_of_high_lt (lo₁ := lo) (lo₂ := low z) hlt
      rw [combine_high_low] at hlt'
      exact hlt'.le
    · have hh : high x = high z := Fin.ext heq
      have hlowlt : (low x).val < (low z).val :=
        low_lt_of_lt_of_high_eq hxz heq
      have hclx : t.clusters (high x) (low z) = true := by
        rw [hh]
        exact hmem
      have hpred : succClusterPred t x (low z) = true :=
        succClusterPred_eq_true.mpr ⟨hlowlt, hclx⟩
      have hlole : lo.val ≤ (low z).val := firstFin?_le h1 hpred
      have hle' := combine_val_le_of_low_le (hi := high x) hlole
      have hcy : combine (high x) (low z) = z := by
        rw [hh]
        exact combine_high_low z
      rw [hcy] at hle'
      exact hle'
  · have hhighlt : (high x).val < (high z).val := by
      rcases lt_or_eq_of_le hmono with hlt | heq
      · exact hlt
      · exfalso
        have hh : high x = high z := Fin.ext heq
        have hlowlt : (low x).val < (low z).val :=
          low_lt_of_lt_of_high_eq hxz heq
        have hclx : t.clusters (high x) (low z) = true := by
          rw [hh]
          exact hmem
        have hpred : succClusterPred t x (low z) = true :=
          succClusterPred_eq_true.mpr ⟨hlowlt, hclx⟩
        have hfalse := firstFin?_none h1none (low z)
        rw [hpred] at hfalse
        simp at hfalse
    have hpredsum : succSummaryPred t x (high z) = true :=
      succSummaryPred_eq_true.mpr ⟨hhighlt, hsum⟩
    have hile : hi.val ≤ (high z).val := firstFin?_le h2 hpredsum
    rcases lt_or_eq_of_le hile with hlt | heq
    · have hlt' := combine_val_lt_of_high_lt (lo₁ := lo) (lo₂ := low z) hlt
      rw [combine_high_low] at hlt'
      exact hlt'.le
    · have hhieq : hi = high z := Fin.ext heq
      have hcl : t.clusters hi (low z) = true := hhieq ▸ hmem
      have hlole : lo.val ≤ (low z).val := firstFin?_le hc hcl
      have hle' := combine_val_le_of_low_le (hi := hi) hlole
      have hcy : combine hi (low z) = z := by
        rw [hhieq]
        exact combine_high_low z
      rw [hcy] at hle'
      exact hle'

/-- **A van Emde Boas successor is missing exactly when nothing larger is stored.** Let $T$ be a
valid two-level van Emde Boas tree over the universe $\{0, \dots, m^2 - 1\}$ and let $x$ be an
element of the universe. Then $x$ has no successor in $T$ if and only if every member $z$ of $T$
satisfies $z \le x$. -/
public theorem successor_eq_none_iff {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) {x : Fin (m * m)} :
    t.successor x = none ↔
      ∀ z : Fin (m * m), t.member z = true → z.val ≤ x.val := by
  constructor
  · intro h z hz
    by_contra hnot
    have hxz : x.val < z.val := lt_of_not_ge hnot
    have hmem : t.clusters (high z) (low z) = true := hz
    have hsum : t.summary (high z) = true := (hv (high z)).mpr ⟨low z, hmem⟩
    have hmono : (high x).val ≤ (high z).val := high_mono hxz.le
    cases h1 : firstFin? (succClusterPred t x) with
    | some lo =>
        rw [successor_eq_some_cluster h1] at h
        simp at h
    | none =>
        have hhighlt : (high x).val < (high z).val := by
          rcases lt_or_eq_of_le hmono with hlt | heq
          · exact hlt
          · exfalso
            have hh : high x = high z := Fin.ext heq
            have hlowlt : (low x).val < (low z).val :=
              low_lt_of_lt_of_high_eq hxz heq
            have hclx : t.clusters (high x) (low z) = true := by
              rw [hh]
              exact hmem
            have hpred : succClusterPred t x (low z) = true :=
              succClusterPred_eq_true.mpr ⟨hlowlt, hclx⟩
            have hfalse := firstFin?_none h1 (low z)
            rw [hpred] at hfalse
            simp at hfalse
        have hpredsum : succSummaryPred t x (high z) = true :=
          succSummaryPred_eq_true.mpr ⟨hhighlt, hsum⟩
        obtain ⟨hi, h2⟩ := firstFin?_some_of hpredsum
        have hsumhi : t.summary hi = true :=
          (succSummaryPred_eq_true.mp (firstFin?_true h2)).2
        obtain ⟨lo₀, hlo₀⟩ := (hv hi).mp hsumhi
        obtain ⟨lo, hc⟩ := firstFin?_some_of hlo₀
        rw [successor_eq_some_next h1 h2 hc] at h
        simp at h
  · intro h
    cases h' : t.successor x with
    | none => rfl
    | some y =>
        have hgt : x.val < y.val := successor_gt h'
        have hle : y.val ≤ x.val := h y (successor_mem h')
        exact (Nat.lt_irrefl _ (lt_of_lt_of_le hgt hle)).elim

/-- **The van Emde Boas successor is the least larger member.** Let $T$ be a valid two-level van
Emde Boas tree over the universe $\{0, \dots, m^2 - 1\}$ and let $x$ and $y$ be elements of the
universe. Then the successor of $x$ in $T$ is $y$ if and only if $y$ is a member of $T$, $x < y$,
and $y \le z$ for every member $z$ of $T$ with $x < z$. -/
public theorem successor_eq_some_iff_of_valid {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) {x y : Fin (m * m)} :
    t.successor x = some y ↔
      t.member y = true ∧ x.val < y.val ∧
        ∀ z : Fin (m * m), t.member z = true → x.val < z.val →
          y.val ≤ z.val := by
  constructor
  · intro h
    exact ⟨successor_mem h, successor_gt h,
      fun z hz hxz => successor_least hv h hz hxz⟩
  · rintro ⟨hym, hgt, hleast⟩
    have hne : t.successor x ≠ none := by
      intro hnone
      rw [successor_eq_none_iff hv] at hnone
      have hle : y.val ≤ x.val := hnone y hym
      exact Nat.lt_irrefl _ (lt_of_lt_of_le hgt hle)
    obtain ⟨y', hy'⟩ : ∃ y' : Fin (m * m), t.successor x = some y' := by
      cases h' : t.successor x with
      | none => exact (hne h').elim
      | some a => exact ⟨a, rfl⟩
    have h1 : y'.val ≤ y.val := successor_least hv hy' hym hgt
    have h2 : y.val ≤ y'.val :=
      hleast y' (successor_mem hy') (successor_gt hy')
    have heq : y = y' := Fin.ext (le_antisymm h2 h1)
    rw [heq]
    exact hy'

/-- **The empty van Emde Boas tree has no successors.** For every $m$ and every element $x$ of the
universe $\{0, \dots, m^2 - 1\}$, $x$ has no successor in the empty two-level van Emde Boas tree
over that universe. -/
public theorem successor_empty {m : Nat} (x : Fin (m * m)) :
    (empty : VanEmdeBoas m).successor x = none := by
  rw [successor_eq_none_iff valid_empty]
  intro z hz
  rw [member_empty] at hz
  simp at hz

/-- **Predecessor query in a two-level van Emde Boas tree.** Let $T$ be a two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$ and let $x = hm + \ell$ with $0 \le h, \ell < m$, so
that $x$ sits at position $\ell$ of cluster $h$. If cluster $h$ has a set position before $\ell$,
the predecessor of $x$ in $T$ is $hm + \ell'$ for the greatest such position $\ell'$. Otherwise,
let $h'$ be the greatest cluster index with $h' < h$ whose summary bit is set; the predecessor is
$h'm + \ell''$ for the greatest position $\ell''$ set in cluster $h'$. If there is no such $h'$, or
cluster $h'$ has no set position, $x$ has no predecessor.

In a valid tree, the predecessor of $x$ is the greatest member of $T$ less than $x$. -/
public def predecessor {m : Nat} (t : VanEmdeBoas m) (x : Fin (m * m)) :
    Option (Fin (m * m)) :=
  match lastFin? (predClusterPred t x) with
  | some lo => some (combine (high x) lo)
  | none =>
    match lastFin? (predSummaryPred t x) with
    | none => none
    | some hi =>
      match lastFin? (t.clusters hi) with
      | none => none
      | some lo => some (combine hi lo)

/-- Given a set position earlier in the cluster of `x`, `predecessor`
returns it. -/
private lemma predecessor_eq_some_cluster {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} {lo : Fin m}
    (h : lastFin? (predClusterPred t x) = some lo) :
    t.predecessor x = some (combine (high x) lo) := by
  simp [predecessor, h]

/-- Given the summary and cluster searches, `predecessor` returns their pair. -/
private lemma predecessor_eq_some_prev {m : Nat} {t : VanEmdeBoas m}
    {x : Fin (m * m)} {hi lo : Fin m}
    (h1 : lastFin? (predClusterPred t x) = none)
    (h2 : lastFin? (predSummaryPred t x) = some hi)
    (h3 : lastFin? (t.clusters hi) = some lo) :
    t.predecessor x = some (combine hi lo) := by
  simp [predecessor, h1, h2, h3]

/-- A value returned by `predecessor` comes from one of its two searches. -/
private lemma predecessor_eq_some_cases {m : Nat} {t : VanEmdeBoas m}
    {x y : Fin (m * m)} (h : t.predecessor x = some y) :
    (∃ lo : Fin m, lastFin? (predClusterPred t x) = some lo ∧
        y = combine (high x) lo) ∨
      (lastFin? (predClusterPred t x) = none ∧
        ∃ hi lo : Fin m, lastFin? (predSummaryPred t x) = some hi ∧
          lastFin? (t.clusters hi) = some lo ∧ y = combine hi lo) := by
  cases h1 : lastFin? (predClusterPred t x) with
  | some lo =>
      refine Or.inl ⟨lo, rfl, ?_⟩
      rw [predecessor_eq_some_cluster h1] at h
      exact (Option.some.inj h).symm
  | none =>
      cases h2 : lastFin? (predSummaryPred t x) with
      | none => simp [predecessor, h1, h2] at h
      | some hi =>
          cases h3 : lastFin? (t.clusters hi) with
          | none => simp [predecessor, h1, h2, h3] at h
          | some lo =>
              refine Or.inr ⟨rfl, hi, lo, rfl, h3, ?_⟩
              rw [predecessor_eq_some_prev h1 h2 h3] at h
              exact (Option.some.inj h).symm

/-- **The van Emde Boas predecessor is stored.** Let $T$ be a two-level van Emde Boas tree over the
universe $\{0, \dots, m^2 - 1\}$, not necessarily valid, and let $x$ and $y$ be elements of the
universe. If the predecessor of $x$ in $T$ is $y$, then $y$ is a member of $T$. -/
public theorem predecessor_mem {m : Nat} {t : VanEmdeBoas m}
    {x y : Fin (m * m)} (h : t.predecessor x = some y) :
    t.member y = true := by
  rcases predecessor_eq_some_cases h with ⟨lo, h1, rfl⟩ |
    ⟨_, hi, lo, _, hc, rfl⟩
  · have hcl : t.clusters (high x) lo = true :=
      (predClusterPred_eq_true.mp (lastFin?_true h1)).2
    simp only [member, high_combine, low_combine]
    exact hcl
  · simp only [member, high_combine, low_combine]
    exact lastFin?_true hc

/-- **The van Emde Boas predecessor is strictly smaller than its argument.** Let $T$ be a two-level
van Emde Boas tree over the universe $\{0, \dots, m^2 - 1\}$, not necessarily valid, and let $x$
and $y$ be elements of the universe. If the predecessor of $x$ in $T$ is $y$, then $y < x$. -/
public theorem predecessor_lt {m : Nat} {t : VanEmdeBoas m}
    {x y : Fin (m * m)} (h : t.predecessor x = some y) :
    y.val < x.val := by
  rcases predecessor_eq_some_cases h with ⟨lo, h1, rfl⟩ |
    ⟨_, hi, lo, h2, _, rfl⟩
  · have hlt : lo.val < (low x).val :=
      (predClusterPred_eq_true.mp (lastFin?_true h1)).1
    rw [combine_val, val_eq_high_low x]
    omega
  · have hlt : hi.val < (high x).val :=
      (predSummaryPred_eq_true.mp (lastFin?_true h2)).1
    have hlt' := combine_val_lt_of_high_lt (lo₁ := lo) (lo₂ := low x) hlt
    rw [combine_high_low] at hlt'
    exact hlt'

/-- **Maximality of the van Emde Boas predecessor.** Let $t$ be a valid two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$, and let $x$, $y$ and $z$ be in the universe. If the
predecessor query for $x$ in $t$ returns $y$, and $z$ is stored in $t$ with $z < x$, then
$z \le y$. -/
public theorem predecessor_greatest {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) {x y z : Fin (m * m)} (h : t.predecessor x = some y)
    (hz : t.member z = true) (hxz : z.val < x.val) :
    z.val ≤ y.val := by
  have hmem : t.clusters (high z) (low z) = true := hz
  have hsum : t.summary (high z) = true := (hv (high z)).mpr ⟨low z, hmem⟩
  have hmono : (high z).val ≤ (high x).val := high_mono hxz.le
  rcases predecessor_eq_some_cases h with ⟨lo, h1, rfl⟩ |
    ⟨h1none, hi, lo, h2, hc, rfl⟩
  · rcases lt_or_eq_of_le hmono with hlt | heq
    · have hlt' := combine_val_lt_of_high_lt (lo₁ := low z) (lo₂ := lo) hlt
      rw [combine_high_low] at hlt'
      exact hlt'.le
    · have hh : high x = high z := Fin.ext heq.symm
      have hlowlt : (low z).val < (low x).val :=
        low_lt_of_lt_of_high_eq hxz heq
      have hclx : t.clusters (high x) (low z) = true := by
        rw [hh]
        exact hmem
      have hpred : predClusterPred t x (low z) = true :=
        predClusterPred_eq_true.mpr ⟨hlowlt, hclx⟩
      have hlole : (low z).val ≤ lo.val := lastFin?_ge h1 hpred
      have hle' := combine_val_le_of_low_le (hi := high x) hlole
      have hcy : combine (high x) (low z) = z := by
        rw [hh]
        exact combine_high_low z
      rw [hcy] at hle'
      exact hle'
  · have hhighlt : (high z).val < (high x).val := by
      rcases lt_or_eq_of_le hmono with hlt | heq
      · exact hlt
      · exfalso
        have hh : high x = high z := Fin.ext heq.symm
        have hlowlt : (low z).val < (low x).val :=
          low_lt_of_lt_of_high_eq hxz heq
        have hclx : t.clusters (high x) (low z) = true := by
          rw [hh]
          exact hmem
        have hpred : predClusterPred t x (low z) = true :=
          predClusterPred_eq_true.mpr ⟨hlowlt, hclx⟩
        have hfalse := lastFin?_none h1none (low z)
        rw [hpred] at hfalse
        simp at hfalse
    have hpredsum : predSummaryPred t x (high z) = true :=
      predSummaryPred_eq_true.mpr ⟨hhighlt, hsum⟩
    have hile : (high z).val ≤ hi.val := lastFin?_ge h2 hpredsum
    rcases lt_or_eq_of_le hile with hlt | heq
    · have hlt' := combine_val_lt_of_high_lt (lo₁ := low z) (lo₂ := lo) hlt
      rw [combine_high_low] at hlt'
      exact hlt'.le
    · have hhieq : hi = high z := Fin.ext heq.symm
      have hcl : t.clusters hi (low z) = true := hhieq ▸ hmem
      have hlole : (low z).val ≤ lo.val := lastFin?_ge hc hcl
      have hle' := combine_val_le_of_low_le (hi := hi) hlole
      have hcy : combine hi (low z) = z := by
        rw [hhieq]
        exact combine_high_low z
      rw [hcy] at hle'
      exact hle'

/-- **Empty predecessor query in a van Emde Boas tree.** Let $t$ be a valid two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$, and let $x$ be in the universe. The predecessor
query for $x$ in $t$ returns no element if and only if $x \le z$ for every $z$ stored in $t$. -/
public theorem predecessor_eq_none_iff {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) {x : Fin (m * m)} :
    t.predecessor x = none ↔
      ∀ z : Fin (m * m), t.member z = true → x.val ≤ z.val := by
  constructor
  · intro h z hz
    by_contra hnot
    have hxz : z.val < x.val := lt_of_not_ge hnot
    have hmem : t.clusters (high z) (low z) = true := hz
    have hsum : t.summary (high z) = true := (hv (high z)).mpr ⟨low z, hmem⟩
    have hmono : (high z).val ≤ (high x).val := high_mono hxz.le
    cases h1 : lastFin? (predClusterPred t x) with
    | some lo =>
        rw [predecessor_eq_some_cluster h1] at h
        simp at h
    | none =>
        have hhighlt : (high z).val < (high x).val := by
          rcases lt_or_eq_of_le hmono with hlt | heq
          · exact hlt
          · exfalso
            have hh : high x = high z := Fin.ext heq.symm
            have hlowlt : (low z).val < (low x).val :=
              low_lt_of_lt_of_high_eq hxz heq
            have hclx : t.clusters (high x) (low z) = true := by
              rw [hh]
              exact hmem
            have hpred : predClusterPred t x (low z) = true :=
              predClusterPred_eq_true.mpr ⟨hlowlt, hclx⟩
            have hfalse := lastFin?_none h1 (low z)
            rw [hpred] at hfalse
            simp at hfalse
        have hpredsum : predSummaryPred t x (high z) = true :=
          predSummaryPred_eq_true.mpr ⟨hhighlt, hsum⟩
        obtain ⟨hi, h2⟩ := lastFin?_some_of hpredsum
        have hsumhi : t.summary hi = true :=
          (predSummaryPred_eq_true.mp (lastFin?_true h2)).2
        obtain ⟨lo₀, hlo₀⟩ := (hv hi).mp hsumhi
        obtain ⟨lo, hc⟩ := lastFin?_some_of hlo₀
        rw [predecessor_eq_some_prev h1 h2 hc] at h
        simp at h
  · intro h
    cases h' : t.predecessor x with
    | none => rfl
    | some y =>
        have hlt : y.val < x.val := predecessor_lt h'
        have hle : x.val ≤ y.val := h y (predecessor_mem h')
        exact (Nat.lt_irrefl _ (lt_of_lt_of_le hlt hle)).elim

/-- **Characterization of the van Emde Boas predecessor.** Let $t$ be a valid two-level van Emde
Boas tree over the universe $\{0, \dots, m^2 - 1\}$, and let $x$ and $y$ be in the universe. The
predecessor query for $x$ in $t$ returns $y$ if and only if $y$ is stored in $t$, $y < x$, and
$z \le y$ for every $z$ stored in $t$ with $z < x$. -/
public theorem predecessor_eq_some_iff_of_valid {m : Nat} {t : VanEmdeBoas m}
    (hv : t.Valid) {x y : Fin (m * m)} :
    t.predecessor x = some y ↔
      t.member y = true ∧ y.val < x.val ∧
        ∀ z : Fin (m * m), t.member z = true → z.val < x.val →
          z.val ≤ y.val := by
  constructor
  · intro h
    exact ⟨predecessor_mem h, predecessor_lt h,
      fun z hz hxz => predecessor_greatest hv h hz hxz⟩
  · rintro ⟨hym, hlt, hgreatest⟩
    have hne : t.predecessor x ≠ none := by
      intro hnone
      rw [predecessor_eq_none_iff hv] at hnone
      have hle : x.val ≤ y.val := hnone y hym
      exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt hle)
    obtain ⟨y', hy'⟩ : ∃ y' : Fin (m * m), t.predecessor x = some y' := by
      cases h' : t.predecessor x with
      | none => exact (hne h').elim
      | some a => exact ⟨a, rfl⟩
    have h1 : y.val ≤ y'.val := predecessor_greatest hv hy' hym hlt
    have h2 : y'.val ≤ y.val :=
      hgreatest y' (predecessor_mem hy') (predecessor_lt hy')
    have heq : y = y' := Fin.ext (le_antisymm h1 h2)
    rw [heq]
    exact hy'

/-- **Predecessor queries in the empty van Emde Boas tree.** For every $x$ in the universe
$\{0, \dots, m^2 - 1\}$, the predecessor query for $x$ in the empty two-level van Emde Boas tree
returns no element. -/
public theorem predecessor_empty {m : Nat} (x : Fin (m * m)) :
    (empty : VanEmdeBoas m).predecessor x = none := by
  rw [predecessor_eq_none_iff valid_empty]
  intro z hz
  rw [member_empty] at hz
  simp at hz

end VanEmdeBoas

end Cslib.Algorithms.Lean
