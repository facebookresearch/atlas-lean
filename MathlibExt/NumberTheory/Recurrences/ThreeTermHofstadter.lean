/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.IntervalCases

/-! # A three-term Hofstadter-like recurrence

The recurrence `B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))`, run from a finite list
of initial conditions `B(1), …, B(m)`. With `pad = true` the sequence is also defined to be `0`
at every nonpositive index (the source's `⟨0̄; …⟩` convention). A term that would reference an
undefined index (a nonpositive index when `pad = false`, or an index not yet computed) cannot
be computed, and the sequence stops there: it "dies" (unpadded) or "ends" (padded).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Value of a partially computed sequence at an index.** Given computed terms
$B(1), \dots, B(m)$, a choice of whether the sequence is padded, and an integer $j$, the value
at index $j$ is $B(j)$ when $1 \le j \le m$, is $0$ when $j \le 0$ and the sequence is padded,
and is undefined otherwise (for $j \le 0$ in the unpadded case, and for $j > m$).

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1
(initial-condition and sequence-death conventions). -/
def threeTermHofstadterLookup (pad : Bool) (xs : Array ℤ) (j : ℤ) : Option ℤ :=
  if j ≤ 0 then (if pad then some 0 else none) else xs[(j - 1).toNat]?

/-- **Next term of the three-term Hofstadter-like recurrence.** Given computed terms
$B(1), \dots, B(m)$, padded with $0$ at nonpositive indices or not, the next term is
$B(m + 1) = B(m + 1 - B(m)) + B(m + 1 - B(m - 1)) + B(m + 1 - B(m - 2))$. It is undefined
when one of the values it uses, $B(m)$, $B(m - 1)$, $B(m - 2)$ or one of the three summands,
sits at an undefined index: a nonpositive index in the unpadded case, or an index above $m$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
def threeTermHofstadterNext (pad : Bool) (xs : Array ℤ) : Option ℤ :=
  let n : ℤ := xs.size + 1
  (threeTermHofstadterLookup pad xs (n - 1)).bind fun b₁ =>
  (threeTermHofstadterLookup pad xs (n - 2)).bind fun b₂ =>
  (threeTermHofstadterLookup pad xs (n - 3)).bind fun b₃ =>
  (threeTermHofstadterLookup pad xs (n - b₁)).bind fun v₁ =>
  (threeTermHofstadterLookup pad xs (n - b₂)).bind fun v₂ =>
  (threeTermHofstadterLookup pad xs (n - b₃)).map fun v₃ => v₁ + v₂ + v₃

/-- **Computing further terms of a three-term Hofstadter-like sequence.** Given terms
$B(1), \dots, B(m)$, padded with $0$ at nonpositive indices or not, and a natural number $k$,
this is the list $B(1), \dots, B(m + k)$ obtained by computing $B(m + 1), \dots, B(m + k)$ one
after another from $B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$. It is undefined if
one of these terms cannot be computed because the formula refers to an undefined index (a
nonpositive index in the unpadded case, or an index not yet computed).

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
def threeTermHofstadterExtend (pad : Bool) : ℕ → Array ℤ → Option (Array ℤ)
  | 0, xs => some xs
  | k + 1, xs =>
    match threeTermHofstadterNext pad xs with
    | none => none
    | some v => threeTermHofstadterExtend pad k (xs.push v)

/-- **Initial segment of a three-term Hofstadter-like sequence.** Let $x_1, \dots, x_m$ be
integers ($m \ge 0$) and let $B$ be the padded or the unpadded three-term Hofstadter-like sequence
with initial conditions $x_1, \dots, x_m$: $B(i) = x_i$ for $1 \le i \le m$, the padded sequence
has $B(i) = 0$ for every $i \le 0$ while the unpadded one is undefined there, and for $n > m$
$$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3)),$$
which is defined only when every value of $B$ on the right-hand side is defined and the indices
$n - B(n-1)$, $n - B(n-2)$, $n - B(n-3)$ are less than $n$. For a natural number $k$, the
initial segment is the list $B(1), \dots, B(m + k)$, the initial conditions followed by the next
$k$ terms; it is undefined when one of $B(m + 1), \dots, B(m + k)$ is undefined.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
def threeTermHofstadterPrefix (pad : Bool) (init : List ℤ) (k : ℕ) : Option (Array ℤ) :=
  threeTermHofstadterExtend pad k init.toArray

/-- **Three-term Hofstadter-like sequence.** Let $x_1, \dots, x_m$ be integers ($m \ge 0$), the
initial conditions, and choose whether the sequence is padded. The sequence $B$ has $B(i) = x_i$
for $1 \le i \le m$; the padded sequence has $B(i) = 0$ for every integer $i \le 0$, while the
unpadded one is undefined at every $i \le 0$. For $n > m$,
$$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3)),$$
which is defined only when every value of $B$ on the right-hand side is defined and the indices
$n - B(n-1)$, $n - B(n-2)$, $n - B(n-3)$ are less than $n$; once a term is undefined, the
sequence stops and every later term is undefined. The term at a natural number index $j$ is
$B(j)$ when this is defined and undefined otherwise; in particular the term at index $0$ is $0$
for the padded sequence and undefined for the unpadded one.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
def threeTermHofstadterTerm (pad : Bool) (init : List ℤ) (j : ℕ) : Option ℤ :=
  (threeTermHofstadterPrefix pad init (j - init.length)).bind fun xs =>
    threeTermHofstadterLookup pad xs j

/-- **Exact length of a three-term Hofstadter-like sequence.** Take integer initial conditions
$B(1), \dots, B(m)$, and either pad the sequence with $B(n) = 0$ for every $n \le 0$ or leave it
unpadded. Continue it by $B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$ for $n > m$,
where a term cannot be computed if this formula refers to an undefined index: a nonpositive
index in the unpadded case, or an index not yet computed. For a natural number $T$, the
sequence has exactly $T$ terms when $T \ge m$, the terms $B(1), \dots, B(T)$ can all be
computed, and $B(T + 1)$ cannot.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1
("dies after `n - 1` terms"; "ends" in the padded case). -/
def ThreeTermHofstadterEndsAfter (pad : Bool) (init : List ℤ) (T : ℕ) : Prop :=
  ∃ xs, threeTermHofstadterPrefix pad init (T - init.length) = some xs ∧ xs.size = T ∧
    threeTermHofstadterNext pad xs = none

/-- **The initial conditions are the first terms.** Let $x_1, \dots, x_m$ be integers and let $j$
be a natural number with $j \le m$. For the padded or the unpadded three-term Hofstadter-like
sequence with initial conditions $x_1, \dots, x_m$, the term at index $j$ equals the lookup of
index $j$ in $x_1, \dots, x_m$: it is $x_j$ if $j \ge 1$, and if $j = 0$ it is $0$ for the
padded sequence and undefined for the unpadded one.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
theorem threeTermHofstadterTerm_of_le_length (pad : Bool) (init : List ℤ) {j : ℕ}
    (hj : j ≤ init.length) :
    threeTermHofstadterTerm pad init j = threeTermHofstadterLookup pad init.toArray j := by
  simp [threeTermHofstadterTerm, threeTermHofstadterPrefix, Nat.sub_eq_zero_of_le hj,
    threeTermHofstadterExtend]

/-- **Index zero of the sequence started at 5.** For the three-term Hofstadter-like sequence with
the single initial condition $5$, the term at index $0$ is defined and equals $0$ when the
sequence is padded, and it is undefined when the sequence is unpadded.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
theorem threeTermHofstadterTerm_zero :
    threeTermHofstadterTerm true [5] 0 = some 0 ∧ threeTermHofstadterTerm false [5] 0 = none := by
  decide

/-- **Sixth and seventh terms of the sequence started at 1, 2, 3, 4, 5.** For the unpadded
three-term Hofstadter-like sequence $B$ with initial conditions $1, 2, 3, 4, 5$, the terms $B(6)$
and $B(7)$ are defined, with $B(6) = B(1) + B(2) + B(3) = 6$ and $B(7) = B(1) + B(2) + B(3) = 6$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
theorem threeTermHofstadterTerm_bSequence_six_seven :
    threeTermHofstadterTerm false [1, 2, 3, 4, 5] 6 = some 6 ∧
      threeTermHofstadterTerm false [1, 2, 3, 4, 5] 7 = some 6 := by
  decide

/-- **The sequence from $1, 2, 3$ dies after four terms.** Run the recurrence
$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$ from the initial conditions
$B(1) = 1$, $B(2) = 2$, $B(3) = 3$ without padding, so that a term whose recurrence refers to a
nonpositive index, or to an index not yet computed, cannot be computed. Then the sequence has
exactly four terms: $B(4)$ can be computed and $B(5)$ cannot.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, proof of
Theorem 1 (`B_3(4) = 6`). -/
theorem threeTermHofstadterEndsAfter_one_two_three :
    ThreeTermHofstadterEndsAfter false [1, 2, 3] 4 :=
  ⟨#[1, 2, 3, 6], rfl, rfl, by decide⟩

namespace threeTermHofstadter_linear_length

/-- Candidate value at index `N + d`. Nonpositive offsets select the initial value `N + d`.
Offsets 1 through 24 select the terms in the proof of Fox's Theorem 1. -/
private def value (N d : ℤ) : ℤ :=
  [N + d, 6, N + 1, N + 2, N + 3, 9, N + 4, N + 5, N + 6, 12, N + 7, N + 8, N + 9,
    15, N + 10, N + 11, 17, N + 13, 18, N + 13, N + 15, N + 16, 22, 21,
    2 * N + 11].getD d.toNat 0

private theorem value_of_nonpos (N : ℤ) {d : ℤ} (hd : d ≤ 0) : value N d = N + d := by
  unfold value
  rw [show d.toNat = 0 by omega, List.getD_cons_zero]

/-- The candidate prefix through index `N + k`. -/
private def candidate (N k : ℕ) : Array ℤ :=
  ((List.range (N + k)).map fun i : ℕ => value N ((i : ℤ) + 1 - N)).toArray

private theorem size_candidate (N k : ℕ) : (candidate N k).size = N + k := by
  simp [candidate]

private theorem candidate_zero (N : ℕ) :
    candidate N 0 = ((List.range N).map fun i : ℕ => (i : ℤ) + 1).toArray := by
  simp only [candidate, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := List.mem_range.mp hi
  rw [value_of_nonpos _ (by omega)]
  omega

private theorem candidate_succ (N k : ℕ) :
    candidate N (k + 1) = (candidate N k).push (value N (k + 1)) := by
  unfold candidate
  rw [Nat.add_succ, List.range_succ, List.map_append]
  simp +arith

private theorem lookup_candidate (N k : ℕ) (j : ℤ) :
    threeTermHofstadterLookup false (candidate N k) j =
      if 0 < j ∧ j ≤ (N : ℤ) + k then some (value N (j - N)) else none := by
  by_cases hj : 0 < j
  · by_cases h : j ≤ (N : ℤ) + k
    · have hi : (j - 1).toNat < (candidate N k).size := by rw [size_candidate]; omega
      simp only [threeTermHofstadterLookup, show ¬j ≤ 0 by omega, ite_false, hj, h,
        and_self, ite_true]
      rw [getElem?_pos (candidate N k) (j - 1).toNat hi]
      simp only [candidate, List.getElem_toArray,
        List.getElem_map, List.getElem_range, Option.some.injEq]
      congr 1
      omega
    · have hi : ¬ (j - 1).toNat < (candidate N k).size := by rw [size_candidate]; omega
      simp only [threeTermHofstadterLookup, show ¬j ≤ 0 by omega, ite_false, hj, h, and_false,
        getElem?_neg (candidate N k) (j - 1).toNat hi]
  · simp [threeTermHofstadterLookup, hj, show j ≤ 0 by omega]

/-- Read by offset, checking both endpoints of the computed prefix. -/
private def readOffset (N k : ℕ) (d : ℤ) : Option ℤ :=
  if 0 < N + d ∧ d ≤ k then some (value N d) else none

private theorem lookup_offset (N k : ℕ) (j : ℤ) :
    threeTermHofstadterLookup false (candidate N k) j = readOffset N k (j - N) := by
  rw [lookup_candidate, readOffset]
  split <;> split <;> first | rfl | omega

private theorem readOffset_some {N k : ℕ} {d : ℤ} (h : 0 < N + d) (h' : d ≤ k) :
    readOffset N k d = some (value N d) := by
  simp [readOffset, h, h']

private theorem next_candidate {N : ℕ} (hN : 14 ≤ N) (k : ℕ) :
    threeTermHofstadterNext false (candidate N k) =
      (readOffset N k (k + 1 - value N k)).bind fun a =>
      (readOffset N k (k + 1 - value N (k - 1))).bind fun b =>
      (readOffset N k (k + 1 - value N (k - 2))).map fun c => a + b + c := by
  simp +arith only [threeTermHofstadterNext, size_candidate, Nat.cast_add, lookup_offset]
  simp (disch := omega) only [readOffset_some, Option.bind_some]

private theorem next_of_lt {N k : ℕ} (hN : 14 ≤ N) (hk : k < 24) :
    threeTermHofstadterNext false (candidate N k) = some (value N (k + 1)) := by
  rw [next_candidate hN]
  -- Reduce the previous three terms, check their lookup bounds, then add the resulting entries.
  interval_cases k <;> dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some] <;>
    simp (disch := omega) only [readOffset_some, value_of_nonpos, Option.bind_some,
      Option.map_some, Option.some.injEq] <;>
    (try dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some]) <;> omega

private theorem extend_candidate {N : ℕ} (hN : 14 ≤ N) (m k : ℕ) (h : k + m ≤ 24) :
    threeTermHofstadterExtend false m (candidate N k) = some (candidate N (k + m)) := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    rw [threeTermHofstadterExtend, next_of_lt hN (by omega)]
    change threeTermHofstadterExtend false m ((candidate N k).push _) = _
    rw [← candidate_succ, ih (k + 1) (by omega), Nat.add_right_comm k 1 m, Nat.add_assoc]

private theorem next_last {N : ℕ} (hN : 14 ≤ N) :
    threeTermHofstadterNext false (candidate N 24) = none := by
  rw [next_candidate hN]
  -- The first summand would read index `N + 25 - (2 * N + 11) = 14 - N`.
  have h : readOffset N 24 (25 - (2 * (N : ℤ) + 11)) = none := by
    unfold readOffset
    rw [ite_eq_right_iff.mpr (by omega)]
  dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some]
  rw [h]
  rfl

end threeTermHofstadter_linear_length

open threeTermHofstadter_linear_length

/-- **Length of the unpadded sequence from $1, \dots, N$.** For every natural number $N \ge 14$,
the sequence $B_N$ with initial conditions $B_N(i) = i$ for $1 \le i \le N$, continued without
padding by the recurrence $B_N(n) = B_N(n - B_N(n-1)) + B_N(n - B_N(n-2)) + B_N(n - B_N(n-3))$,
has exactly $N + 24$ terms: $B_N(1), \dots, B_N(N + 24)$ can be computed and $B_N(N + 25)$
cannot, because the recurrence refers to a nonpositive index or to an index not yet computed.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 1
(`jis-2024-24.7.4-thm-1`). -/
theorem threeTermHofstadter_linear_length {N : ℕ} (hN : 14 ≤ N) :
    ThreeTermHofstadterEndsAfter false ((List.range N).map fun i : ℕ => (i : ℤ) + 1) (N + 24) := by
  refine ⟨candidate N 24, ?_, size_candidate N 24, next_last hN⟩
  simp only [threeTermHofstadterPrefix, List.length_map, List.length_range,
    Nat.add_sub_cancel_left, ← candidate_zero]
  exact extend_candidate hN 24 0 (by decide)

end

end MetaMathlibExt
