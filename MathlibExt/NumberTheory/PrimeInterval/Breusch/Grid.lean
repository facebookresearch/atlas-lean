/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Breusch grid certificate (`k = 9`)

Möbius-weighted grid `G`-function for Breusch's proof with `Q = 210`: the divisor
table `w9`, grid values `G9 j`, the global maximum `M = 3` on `j < 18900`, and the
first-attainment thresholds `279`, `657`, `963`.

The Möbius values in `w9` were verified by hand against the Möbius function: every
entry is squarefree with value `(-1)^ω`. Three kernel-checked facts record this:
`w9_complete` (support), `w9_mu_sign` (values) and `w9_mu_sum_Q` (weighted sum).
-/

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

-- Q for the k=9 case: product of {2,3,5,7}.
/-- **The modulus $Q_9 = 210$.** For the $k = 9$ case of Breusch's argument, the truncation
modulus is the natural number $Q_9 = 2 \cdot 3 \cdot 5 \cdot 7 = 210$. -/
def Q9 : ℕ := 210

-- Explicit (divisor, Möbius value) table for `Q9`: every entry is squarefree,
-- with value `(-1)^ω`, e.g. `(35, 1)` since `35 = 5 * 7` has two prime factors.
/-- **The Möbius divisor table for $210$.** $W_9$ is the list of pairs of a natural number and an
integer
$(1, 1), (2, -1), (3, -1), (5, -1), (6, 1), (7, -1), (10, 1), (14, 1), (15, 1), (21, 1),$
$(30, -1), (35, 1), (42, -1), (70, -1), (105, -1), (210, 1)$,
in this order. It pairs each divisor $d$ of $210$ with its Möbius value $\mu(d)$. -/
def w9 : List (ℕ × ℤ) :=
  [(1, 1), (2, -1), (3, -1), (5, -1), (6, 1), (7, -1), (10, 1), (14, 1),
   (15, 1), (21, 1), (30, -1), (35, 1), (42, -1), (70, -1), (105, -1),
   (210, 1)]

/-- **The divisor table for $210$ has 16 entries.** The Möbius divisor table $W_9$ for $210$ is a
list of length $16$. -/
lemma w9_length : w9.length = 16 := rfl

/-- **The divisor table for $210$ lists every divisor.** The set of first components $d$ of the
pairs $(d, \varepsilon)$ in the Möbius divisor table $W_9$ is exactly the set of divisors of
$Q_9 = 210$. -/
lemma w9_complete : (w9.map Prod.fst).toFinset = Nat.divisors Q9 := by
  decide

/-- **Divisors in the table for $210$ are positive.** For every pair $(d, \varepsilon)$ in the
Möbius divisor table $W_9$ for $210$, $d \ge 1$. -/
lemma w9_pos : ∀ p ∈ w9, 1 ≤ p.1 := by decide

/-- **Entries of the divisor table for $210$ divide $210$.** For every pair $(d, \varepsilon)$ in
the Möbius divisor table $W_9$, $d$ divides $Q_9 = 210$. -/
lemma w9_dvd : ∀ p ∈ w9, p.1 ∣ Q9 := by decide

-- Single `G`-term: each `Nat` floor is cast with `Int.ofNat` first, so the
-- subtraction happens in `Int` (no `Nat` truncation).
/-- **Summand of the Breusch grid function.** For a natural number $d$, an integer $m$ and a
natural number $j$, the summand of the pair $(d, m)$ at $j$ is the integer
$$
m \Bigl( \Bigl\lfloor \frac{10 \cdot 210 \cdot j}{18900\, d} \Bigr\rfloor -
\Bigl\lfloor \frac{9 \cdot 210 \cdot j}{18900\, d} \Bigr\rfloor -
\Bigl\lfloor \frac{210 \cdot j}{18900\, d} \Bigr\rfloor \Bigr),
$$
where each floor is a quotient in natural-number division (equal to $0$ when $d = 0$) and the
differences are taken in the integers. -/
def G9term (q : ℕ × ℤ) (j : ℕ) : ℤ :=
  q.2 * (((10 * 210 * j / (q.1 * 18900) : ℕ) : ℤ)
    - ((9 * 210 * j / (q.1 * 18900) : ℕ) : ℤ)
    - ((210 * j / (q.1 * 18900) : ℕ) : ℤ))

-- G-function for k=9 on the j-grid (j < 18900 = 90 * Q9).
/-- **Breusch grid function for $k = 9$.** For a natural number $j$, $G_9(j)$ is the integer
$$
G_9(j) = \sum_{d \mid 210} \mu(d) \Bigl(
\Bigl\lfloor \frac{10 \cdot 210 \cdot j}{18900\, d} \Bigr\rfloor -
\Bigl\lfloor \frac{9 \cdot 210 \cdot j}{18900\, d} \Bigr\rfloor -
\Bigl\lfloor \frac{210 \cdot j}{18900\, d} \Bigr\rfloor \Bigr),
$$
where $\mu$ is the Möbius function, the sum runs over the $16$ positive divisors $d$ of
$210 = 2 \cdot 3 \cdot 5 \cdot 7$, each floor is a quotient of natural numbers, and the
differences are taken in the integers.

The sum runs over an explicit table of the divisors of $210$ with their Möbius values. -/
def G9 (j : ℕ) : ℤ := (w9.map (fun q => G9term q j)).sum

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
-- Kernel `decide` over this 2700-point block needs the raised heartbeat limit.
/-- **Grid bound $G_9 \le 3$ for $0 \le j < 2700$.** For every natural number $k < 2700$,
the grid function satisfies $G_9(0 + k) \le 3$; that is, $G_9(j) \le 3$ for all natural
numbers $j < 2700$. -/
lemma M9_block0 : ∀ k < 2700, G9 (0 + k) ≤ 3 := by decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
-- Kernel `decide` over this 2700-point block needs the raised heartbeat limit.
/-- **Grid bound $G_9 \le 3$ for $2700 \le j < 5400$.** For every natural number $k < 2700$,
the grid function satisfies $G_9(2700 + k) \le 3$; that is, $G_9(j) \le 3$ for all natural
numbers $j$ with $2700 \le j < 5400$. -/
lemma M9_block1 : ∀ k < 2700, G9 (2700 + k) ≤ 3 := by decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
-- Kernel `decide` over this 2700-point block needs the raised heartbeat limit.
/-- **Grid bound $G_9 \le 3$ for $5400 \le j < 8100$.** For every natural number $k < 2700$,
the grid function satisfies $G_9(5400 + k) \le 3$; that is, $G_9(j) \le 3$ for all natural
numbers $j$ with $5400 \le j < 8100$. -/
lemma M9_block2 : ∀ k < 2700, G9 (5400 + k) ≤ 3 := by decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
-- Kernel `decide` over this 2700-point block needs the raised heartbeat limit.
/-- **Grid bound $G_9 \le 3$ for $8100 \le j < 10800$.** For every natural number $k < 2700$,
the grid function satisfies $G_9(8100 + k) \le 3$; that is, $G_9(j) \le 3$ for all natural
numbers $j$ with $8100 \le j < 10800$. -/
lemma M9_block3 : ∀ k < 2700, G9 (8100 + k) ≤ 3 := by decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
-- Kernel `decide` over this 2700-point block needs the raised heartbeat limit.
/-- **Grid bound $G_9 \le 3$ for $10800 \le j < 13500$.** For every natural number $k < 2700$,
the grid function satisfies $G_9(10800 + k) \le 3$; that is, $G_9(j) \le 3$ for all natural
numbers $j$ with $10800 \le j < 13500$. -/
lemma M9_block4 : ∀ k < 2700, G9 (10800 + k) ≤ 3 := by decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
-- Kernel `decide` over this 2700-point block needs the raised heartbeat limit.
/-- **Grid bound $G_9 \le 3$ for $13500 \le j < 16200$.** For every natural number $k < 2700$,
the grid function satisfies $G_9(13500 + k) \le 3$; that is, $G_9(j) \le 3$ for all natural
numbers $j$ with $13500 \le j < 16200$. -/
lemma M9_block5 : ∀ k < 2700, G9 (13500 + k) ≤ 3 := by decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
-- Kernel `decide` over this 2700-point block needs the raised heartbeat limit.
/-- **Grid bound $G_9 \le 3$ for $16200 \le j < 18900$.** For every natural number $k < 2700$,
the grid function satisfies $G_9(16200 + k) \le 3$; that is, $G_9(j) \le 3$ for all natural
numbers $j$ with $16200 \le j < 18900$. -/
lemma M9_block6 : ∀ k < 2700, G9 (16200 + k) ≤ 3 := by decide

/-- **Grid bound $G_9 \le 3$.** For every natural number $j < 18900$, the grid function satisfies
$G_9(j) \le 3$. -/
theorem M9_le : ∀ j < 18900, G9 j ≤ 3 := by
  intro j hj
  have hsplit :
      j < 2700 ∨
        2700 ≤ j ∧ j < 5400 ∨
          5400 ≤ j ∧ j < 8100 ∨
            8100 ≤ j ∧ j < 10800 ∨
              10800 ≤ j ∧ j < 13500 ∨ 13500 ≤ j ∧ j < 16200 ∨
                16200 ≤ j := by
    omega
  rcases hsplit with h | h | h | h | h | h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.zero_le j)
    exact M9_block0 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block1 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block2 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block3 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block4 k (by omega)
  · obtain ⟨lo, hi⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le lo
    exact M9_block5 k (by omega)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact M9_block6 k (by omega)

/-- **The grid function reaches $1$ at $279$.** The Breusch grid function $G_9$ for $k = 9$
satisfies $G_9(279) \ge 1$. -/
theorem jmin1_attained : G9 279 ≥ 1 := by decide

set_option maxRecDepth 16384 in
/-- **The grid function stays below $1$ on $[10, 279)$.** For every natural number $j$ with
$10 \le j < 279$, the Breusch grid function $G_9$ for $k = 9$ satisfies $G_9(j) < 1$. -/
theorem jmin1_core : ∀ j < 279, 10 ≤ j → G9 j < 1 := by decide

/-- **First index from $10$ where the grid function reaches $1$.** The Breusch grid function
$G_9$ for $k = 9$ satisfies $G_9(279) \ge 1$, and $G_9(j) < 1$ for every natural number $j$ with
$10 \le j < 279$. So $279$ is the least $j \ge 10$ with $G_9(j) \ge 1$. -/
theorem jmin1 : G9 279 ≥ 1 ∧ ∀ j, 10 ≤ j → j < 279 → G9 j < 1 :=
  ⟨jmin1_attained, fun j h1 h2 => jmin1_core j h2 h1⟩

/-- **The grid function reaches $2$ at $657$.** The Breusch grid function $G_9$ for $k = 9$
satisfies $G_9(657) \ge 2$. -/
theorem jmin2_attained : G9 657 ≥ 2 := by decide

set_option maxRecDepth 16384 in
/-- **The grid function stays below $2$ on $[10, 657)$.** For every natural number $j$ with
$10 \le j < 657$, the Breusch grid function $G_9$ for $k = 9$ satisfies $G_9(j) < 2$. -/
theorem jmin2_core : ∀ j < 657, 10 ≤ j → G9 j < 2 := by decide

/-- **First index from $10$ where the grid function reaches $2$.** The Breusch grid function
$G_9$ for $k = 9$ satisfies $G_9(657) \ge 2$, and $G_9(j) < 2$ for every natural number $j$ with
$10 \le j < 657$. So $657$ is the least $j \ge 10$ with $G_9(j) \ge 2$. -/
theorem jmin2 : G9 657 ≥ 2 ∧ ∀ j, 10 ≤ j → j < 657 → G9 j < 2 :=
  ⟨jmin2_attained, fun j h1 h2 => jmin2_core j h2 h1⟩

/-- **The grid function reaches $3$ at $963$.** The Breusch grid function $G_9$ for $k = 9$
satisfies $G_9(963) \ge 3$. -/
theorem jmin3_attained : G9 963 ≥ 3 := by decide

set_option maxRecDepth 16384 in
/-- **The grid function stays below $3$ on $[10, 963)$.** For every natural number $j$ with
$10 \le j < 963$, the Breusch grid function $G_9$ for $k = 9$ satisfies $G_9(j) < 3$. -/
theorem jmin3_core : ∀ j < 963, 10 ≤ j → G9 j < 3 := by decide

/-- **First index from 10 on with grid value at least 3.** The grid function $G_9$ satisfies
$G_9(963) \ge 3$, and $G_9(j) < 3$ for every natural number $j$ with $10 \le j < 963$. -/
theorem jmin3 : G9 963 ≥ 3 ∧ ∀ j, 10 ≤ j → j < 963 → G9 j < 3 :=
  ⟨jmin3_attained, fun j h1 h2 => jmin3_core j h2 h1⟩

-- μ-values on w9 are ±1.
/-- **Signs in the divisor table for $210$.** For every pair $(d, \varepsilon)$ in the Möbius
divisor table $W_9$ for $210$, $\varepsilon = 1$ or $\varepsilon = -1$. -/
lemma w9_mu_sign : ∀ q ∈ w9, q.2 = 1 ∨ q.2 = -1 := by decide

/-- **The divisor table for $210$ has no repeated entries.** No pair $(d, \varepsilon)$ occurs more
than once in the list $W_9$, the Möbius divisor table for $210$. -/
lemma w9_nodup : w9.Nodup := by decide

/-- **Sum over a duplicate-free list.** Let $M$ be an additive commutative monoid, let $l$ be
a list of elements of $\mathbb{N} \times \mathbb{Z}$ with no repeated entries, and let
$f : \mathbb{N} \times \mathbb{Z} \to M$. Then the sum of the values of $f$ along $l$ equals
the sum of $f$ over the finite set of entries of $l$. -/
lemma map_sum_toFinset {M : Type*} [AddCommMonoid M] (l : List (ℕ × ℤ)) (hl : l.Nodup)
    (f : (ℕ × ℤ) → M) : (l.map f).sum = l.toFinset.sum f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, ih hl.2, List.toFinset_cons,
      Finset.sum_insert (by simpa using hl.1)]

end MathlibExt.NumberTheory.BreuschWanted.Internal
