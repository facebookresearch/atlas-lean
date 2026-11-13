/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.List.GetD

namespace MetaMathlibExt

@[expose] public section

/-! # A three-term Hofstadter-like recurrence

The recurrence `B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))`, run from a finite list
of initial conditions `B(1), …, B(m)`. With `pad = true` the sequence is also defined to be `0`
at every nonpositive index (the source's `⟨0̄; …⟩` convention). A term that would reference an
undefined index (a nonpositive index when `pad = false`, or an index not yet computed) cannot
be computed, and the sequence stops there: it "dies" (unpadded) or "ends" (padded).
-/

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

/-- **Death of the unpadded sequence from $1, \dots, N$ for $N = 3$, $4$ or $N \ge 10$.** Let
$N$ be a natural number with $N = 3$, $N = 4$ or $N \ge 10$, and let $B_N$ be the sequence with
initial conditions $B_N(i) = i$ for $1 \le i \le N$, continued without padding by the recurrence
$B_N(n) = B_N(n - B_N(n-1)) + B_N(n - B_N(n-2)) + B_N(n - B_N(n-3))$. Then $B_N$ dies: there is
a natural number $T$ such that $B_N(1), \dots, B_N(T)$ can be computed and $B_N(T + 1)$ cannot,
because the recurrence refers to a nonpositive index or to an index not yet computed.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 1
(`jis-2024-24.7.4-thm-1`). -/
public theorem_wanted threeTermHofstadter_linear_dies {N : ℕ} (hN : N = 3 ∨ N = 4 ∨ 10 ≤ N) :
    ∃ T, ThreeTermHofstadterEndsAfter false ((List.range N).map fun i : ℕ => (i : ℤ) + 1) T

/-- **Length of the unpadded sequence from $1, \dots, N$.** For every natural number $N \ge 14$,
the sequence $B_N$ with initial conditions $B_N(i) = i$ for $1 \le i \le N$, continued without
padding by the recurrence $B_N(n) = B_N(n - B_N(n-1)) + B_N(n - B_N(n-2)) + B_N(n - B_N(n-3))$,
has exactly $N + 24$ terms: $B_N(1), \dots, B_N(N + 24)$ can be computed and $B_N(N + 25)$
cannot, because the recurrence refers to a nonpositive index or to an index not yet computed.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 1
(`jis-2024-24.7.4-thm-1`). -/
public theorem_wanted threeTermHofstadter_linear_length {N : ℕ} (hN : 14 ≤ N) :
    ThreeTermHofstadterEndsAfter false ((List.range N).map fun i : ℕ => (i : ℤ) + 1) (N + 24)

/-- **Period-seven pattern of the padded sequence from $1, \dots, N$.** Let $N \ge 72$ be a
natural number, and let $B$ be the sequence with $B(n) = 0$ for $n \le 0$ and $B(i) = i$ for
$1 \le i \le N$, continued by the recurrence $B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$.
Let $\nu = -1, -2, -2, -2, 2, 1, 0$ according as $N \equiv 0, 1, 2, 3, 4, 5, 6 \pmod 7$. Then
for all natural numbers $k \ge 1$ and $r < 7$ with $N + 67 \le N + 7k + r \le 2N + \nu$, the
term $B(N + 7k + r)$ can be computed, and it equals $7k + 2$, $N + 7k + 2$, $N + 7k + 4$, $7$,
$2N + 2k + 45$, $2N + k - 7$ or $N - 2$ according as $r = 0, 1, 2, 3, 4, 5$ or $6$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 2
(`jis-2024-24.7.4-thm-2`). -/
public theorem_wanted threeTermHofstadter_padded_linear_period_seven {N : ℕ} (hN : 72 ≤ N)
    (k r : ℕ) (hk : 1 ≤ k) (hr : r < 7) (hlo : N + 67 ≤ N + 7 * k + r)
    (hhi : ((N + 7 * k + r : ℕ) : ℤ) ≤ 2 * N + [-1, -2, -2, -2, 2, 1, 0].getD (N % 7) 0) :
    threeTermHofstadterTerm true ((List.range N).map fun i : ℕ => (i : ℤ) + 1) (N + 7 * k + r) =
      some ([7 * k + 2, N + 7 * k + 2, N + 7 * k + 4, 7, 2 * N + 2 * k + 45, 2 * N + k - 7,
        N - 2].getD r 0 : ℤ)

/-- **Length of the padded sequence from $1, \dots, N$.** Let $N$ be a natural number, and let
$t = 196, 2087, 3201, 4315, 200, 32478, 118$ and $e = 27, 254, 524, 560, 20, 4547, 9$
according as $N \equiv 0, 1, 2, 3, 4, 5, 6 \pmod 7$. Let $B$ be the sequence with $B(n) = 0$
for $n \le 0$ and $B(i) = i$ for $1 \le i \le N$, continued by the recurrence
$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$. If $N \ge t$, then $B$ ends after
exactly $2N + e$ terms: $B(1), \dots, B(2N + e)$ can be computed and $B(2N + e + 1)$ cannot,
because the recurrence refers to an index not yet computed.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 2
(`jis-2024-24.7.4-thm-2`). -/
public theorem_wanted threeTermHofstadter_padded_linear_endsAfter {N : ℕ}
    (hN : [196, 2087, 3201, 4315, 200, 32478, 118].getD (N % 7) 0 ≤ N) :
    ThreeTermHofstadterEndsAfter true ((List.range N).map fun i : ℕ => (i : ℤ) + 1)
      (2 * N + [27, 254, 524, 560, 20, 4547, 9].getD (N % 7) 0)

/-- **Seven-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K$, $c$ and
$\gamma$ be natural numbers with $K \ge 7$, $c \ge 1$, $\gamma \le 6$ and $7c + \gamma \le K$, and
put $L = K - 7c - \gamma$ and $M = K + L + 5$. For a tuple $(t_0, \dots, t_6)$ write
$(t_0, \dots, t_6)_\gamma$ for its entry $t_\gamma$. Let $\lambda$ and $\mu$ be integers with
$\lambda \ge -2c + (2, 1, 4, 3, 2, 1, 0)_\gamma$ and $\mu \ge -c + (0, 0, 3, 2, 1, 0, -1)_\gamma$,
and put $\nu = (-2, -2, 2, 1, 0, -1, -2)_\gamma$. Let $a_1, \dots, a_L$ be arbitrary integers and
let $B$ be the padded three-term Hofstadter-like sequence with initial conditions
$1, 2, \dots, K, 6, a_1, \dots, a_L, 2K + \lambda - 2, 2K + \mu - 1, K - 2$. Then for every
integer $k$ and every $r \in \{0, 1, \dots, 6\}$ with $M - 3 \le M + 7k + r \le 2K + \nu$, the
term $B(M + 7k + r)$ is defined, and these terms are $B(M + 7k) = L + 7k + 7$,
$B(M + 7k + 1) = M + 7k + 2$, $B(M + 7k + 2) = M + 7k + 4$, $B(M + 7k + 3) = 7$,
$B(M + 7k + 4) = 2K + 2k + \lambda$, $B(M + 7k + 5) = 2K + k + \mu$ and $B(M + 7k + 6) = K - 2$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 3
(`jis-2024-24.7.4-lem-3`). -/
public theorem_wanted threeTermHofstadter_sevenCycle {K c γ : ℕ} (hK : 7 ≤ K) (hc : 1 ≤ c)
    (hγ : γ ≤ 6) (hL : 7 * c + γ ≤ K) {lam mu : ℤ}
    (hlam : -2 * (c : ℤ) + [2, 1, 4, 3, 2, 1, 0].getD γ 0 ≤ lam)
    (hmu : -(c : ℤ) + [0, 0, 3, 2, 1, 0, -1].getD γ 0 ≤ mu)
    (a : List ℤ) (ha : a.length = K - 7 * c - γ) (k : ℤ) (r : ℕ) (hr : r < 7)
    (hlo : ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) - 3 ≤ (2 * K - 7 * c - γ + 5 : ℕ) + 7 * k + r)
    (hhi : ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + r ≤
      2 * K + [-2, -2, 2, 1, 0, -1, -2].getD γ 0) :
    threeTermHofstadterTerm true
        ((List.range K).map (fun i : ℕ => (i : ℤ) + 1) ++ [6] ++ a ++
          [2 * K + lam - 2, 2 * K + mu - 1, K - 2])
        (((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + r).toNat =
      some ([((K - 7 * c - γ : ℕ) : ℤ) + 7 * k + 7, ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + 2,
        ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + 4, 7, 2 * K + 2 * k + lam, 2 * K + k + mu,
        K - 2].getD r 0)

/-- **Two-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 1$ be a natural
number, let $M$ be an integer with $M \ge K + 5$, let $a_1, \dots, a_K$ be arbitrary integers,
and let $B$ be the padded three-term Hofstadter-like sequence with initial conditions
$a_1, \dots, a_K, 2, M, 2$. Then for every natural number $k$ the term $B(K + 2k + 1)$ is defined
and equals $2$, and for every $k \ge 1$ the term $B(K + 2k)$ is defined and equals $2^{k-1} M$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 4,
citing the author's thesis, Proposition 9.9 (`jis-2024-24.7.4-lem-4`). -/
public theorem_wanted threeTermHofstadter_twoCycle {K : ℕ} (hK : 1 ≤ K) {M : ℤ}
    (hM : (K : ℤ) + 5 ≤ M) (a : List ℤ) (ha : a.length = K) (k : ℕ) :
    threeTermHofstadterTerm true (a ++ [2, M, 2]) (K + 2 * k + 1) = some 2 ∧
      (1 ≤ k → threeTermHofstadterTerm true (a ++ [2, M, 2]) (K + 2 * k) =
        some (2 ^ (k - 1) * M))

/-- **Five-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 3$ be a
natural number, $\mu \ge 1$ an integer, and $a_4, \dots, a_K$ arbitrary integers. Let $B$ be
the sequence given by $B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$, padded with
$B(n) = 0$ for $n \le 0$, with initial conditions
$1, 2, 3, a_4, \dots, a_K, K + \mu, 3, K + 3, K + \mu + 1, 5$ at the indices $1, \dots, K + 5$.
Then for all natural numbers $k$ and $r < 5$ with
$K + 1 \le K + 5k + r \le K + \lfloor (5\mu - 15)/2 \rfloor$, the term $B(K + 5k + r)$ can be
computed, and it equals $5$, $K + 3k + \mu$, $3$, $K + 5k + 3$ or $K + 3k + \mu + 1$ according
as $r = 0, 1, 2, 3$ or $4$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 5,
citing the author's thesis, Proposition 9.10 (`jis-2024-24.7.4-lem-5`). -/
public theorem_wanted threeTermHofstadter_fiveCycle {K : ℕ} (hK : 3 ≤ K) {mu : ℤ} (hmu : 1 ≤ mu)
    (a : List ℤ) (ha : a.length = K - 3) (k r : ℕ) (hr : r < 5) (hlo : K + 1 ≤ K + 5 * k + r)
    (hhi : ((K + 5 * k + r : ℕ) : ℤ) ≤ K + (5 * mu - 15) / 2) :
    threeTermHofstadterTerm true ([1, 2, 3] ++ a ++ [K + mu, 3, K + 3, K + mu + 1, 5])
        (K + 5 * k + r) =
      some ([5, K + 3 * k + mu, 3, K + 5 * k + 3, K + 3 * k + mu + 1].getD r 0 : ℤ)

/-- **Second sixteen-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 1$
be a natural number and let $\lambda$, $\mu_1$, $\mu_2$, $\gamma_1$, $\gamma_2$, $\gamma_3$ be
integers with $\lambda > 31 + K$ and $\mu_1, \mu_2, \gamma_1, \gamma_2, \gamma_3 > \lambda$. Let
$a_1, \dots, a_K$ be arbitrary integers and let $B$ be the padded three-term Hofstadter-like
sequence with initial conditions $a_1, \dots, a_K, 16, \mu_2, 7, \gamma_2, \lambda, 16, \lambda,
16, \mu_1, 10, \gamma_3, \mu_2, 7, \lambda, 16, \gamma_1$. Then for all natural numbers $k$ and
$r \le 15$ with $K + 1 \le K + 16k + r \le \lambda$, the term $B(K + 16k + r)$ is defined, and
these terms are $B(K + 16k) = \mu_1 2^k + \gamma_1 - 2\mu_1$, $B(K + 16k + 1) = 16$,
$B(K + 16k + 2) = \mu_2 2^k$, $B(K + 16k + 3) = 7$, $B(K + 16k + 4) = 7k + \gamma_2$,
$B(K + 16k + 5) = \lambda$, $B(K + 16k + 6) = 16$, $B(K + 16k + 7) = \lambda$,
$B(K + 16k + 8) = 16$, $B(K + 16k + 9) = \mu_1 2^k$, $B(K + 16k + 10) = 10$,
$B(K + 16k + 11) = 16k + \gamma_3$, $B(K + 16k + 12) = \mu_2 2^k$, $B(K + 16k + 13) = 7$,
$B(K + 16k + 14) = \lambda$ and $B(K + 16k + 15) = 16$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 7,
citing the author's thesis, Proposition 9.16 (`jis-2024-24.7.4-lem-7`). -/
public theorem_wanted threeTermHofstadter_sixteenCycle_two {K : ℕ} (hK : 1 ≤ K)
    {lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ} (hlam : 31 + (K : ℤ) < lam) (hmu₁ : lam < mu₁)
    (hmu₂ : lam < mu₂) (hga₁ : lam < ga₁) (hga₂ : lam < ga₂) (hga₃ : lam < ga₃)
    (a : List ℤ) (ha : a.length = K) (k r : ℕ) (hr : r < 16) (hlo : K + 1 ≤ K + 16 * k + r)
    (hhi : ((K + 16 * k + r : ℕ) : ℤ) ≤ lam) :
    threeTermHofstadterTerm true
        (a ++ [16, mu₂, 7, ga₂, lam, 16, lam, 16, mu₁, 10, ga₃, mu₂, 7, lam, 16, ga₁])
        (K + 16 * k + r) =
      some ([mu₁ * 2 ^ k + ga₁ - 2 * mu₁, 16, mu₂ * 2 ^ k, 7, 7 * k + ga₂, lam, 16, lam, 16,
        mu₁ * 2 ^ k, 10, 16 * k + ga₃, mu₂ * 2 ^ k, 7, lam, 16].getD r 0)

/-- **First sixteen-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 1$ be
a natural number and let $\lambda$, $\mu_1$, $\mu_2$, $\gamma$ be integers with $\lambda > 31 + K$
and $\mu_1, \mu_2, \gamma > \lambda$. Let $a_1, \dots, a_K$ be arbitrary integers and let $B$ be
the padded three-term Hofstadter-like sequence with initial conditions
$a_1, \dots, a_K, \lambda, 7, \mu_2, 16, \mu_2, 16, \mu_1, \lambda, 7, \mu_2, 16, 2\mu_2, 16,
\mu_2, 25, \gamma, \lambda, 7$. Then for all natural numbers $k$ and $r \le 15$ with
$K + 1 \le K + 16k + r \le \lambda$, the term $B(K + 16k + r)$ is defined, and these terms are
$B(K + 16k) = \mu_1 2^{k-1} + \gamma - \mu_1$, $B(K + 16k + 1) = \lambda$, $B(K + 16k + 2) = 7$,
$B(K + 16k + 3) = \mu_2 2^k$, $B(K + 16k + 4) = 16$, $B(K + 16k + 5) = \mu_2 2^k$,
$B(K + 16k + 6) = 16$, $B(K + 16k + 7) = \mu_1 2^k$, $B(K + 16k + 8) = \lambda$,
$B(K + 16k + 9) = 7$, $B(K + 16k + 10) = \mu_2 2^k$, $B(K + 16k + 11) = 16$,
$B(K + 16k + 12) = \mu_2 2^{k+1}$, $B(K + 16k + 13) = 16$, $B(K + 16k + 14) = \mu_2 2^k$ and
$B(K + 16k + 15) = 25$.

Corrected: the paper prints $B(K + 16k + 12) = \mu_2 2^k$, which contradicts its own initial
value $B(K + 12) = 2\mu_2$; the exponent $k + 1$ matches the initial conditions and every later
term.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 6,
citing the author's thesis, Proposition 9.13 (`jis-2024-24.7.4-lem-6`). -/
public theorem_wanted threeTermHofstadter_sixteenCycle_one {K : ℕ} (hK : 1 ≤ K)
    {lam mu₁ mu₂ ga : ℤ} (hlam : 31 + (K : ℤ) < lam) (hmu₁ : lam < mu₁) (hmu₂ : lam < mu₂)
    (hga : lam < ga) (a : List ℤ) (ha : a.length = K) (k r : ℕ) (hr : r < 16)
    (hlo : K + 1 ≤ K + 16 * k + r) (hhi : ((K + 16 * k + r : ℕ) : ℤ) ≤ lam) :
    threeTermHofstadterTerm true
        (a ++ [lam, 7, mu₂, 16, mu₂, 16, mu₁, lam, 7, mu₂, 16, 2 * mu₂, 16, mu₂, 25, ga, lam, 7])
        (K + 16 * k + r) =
      some ([mu₁ * 2 ^ (k - 1) + ga - mu₁, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ k, 16,
        mu₁ * 2 ^ k, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ (k + 1), 16, mu₂ * 2 ^ k, 25].getD r 0)

end

end MetaMathlibExt
