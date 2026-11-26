/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.GameTheory.SlowANim
public import MathlibExt.GameTheory.SlowANimGeneralReduction
public import MathlibExt.GameTheory.SlowANimParity
public import MathlibExt.GameTheory.SlowANimThreeStacks
public import MathlibExt.Combinatorics.SlowANimIsPPositionSetExtend

/-!
# P-positions of Slow`A`-Nim

Statements from Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite
Families of Slow`A`-Nim*, INTEGERS 26 (2026), Article G3 (arXiv:2404.06608v3).

`SN(n, A)` is played on `n` stacks (a position is `p : Fin n → ℕ`); a move selects a nonempty
set `S` of `|S| ∈ A` nonempty stacks and removes exactly one token from each. The paper takes
`A ⊆ {1, …, n}`; every statement below carries that hypothesis. P-positions are the existing
`MetaMathlibExt.SpragueGrundy.IsP` of the game `slowANimGame n A`. The paper writes positions
in canonical (non-decreasing) form; here stacks are labelled and canonical form is imposed
only where a statement refers to it (Theorem 3).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Partial structure of the P-positions of Slow $A$-Nim.** Let $A \subseteq \{1, \dots, n\}$
and let $p$ be a position of Slow $A$-Nim on $n$ stacks. If every stack height of $p$ is even,
then $p$ is a P-position. If the number of stacks of $p$ with odd height lies in $A$, then $p$
is not a P-position.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Proposition 1. -/
public theorem_wanted slowANim_partialStructure (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (p : Fin n → ℕ) :
    ((∀ i, Even (p i)) → SpragueGrundy.IsP (slowANimGame n A) p) ∧
      ((Finset.univ.filter fun i => Odd (p i)).card ∈ A →
        ¬ SpragueGrundy.IsP (slowANimGame n A) p)

/-- **P-positions of Slow A-Nim with A = {1, n}, n even.** Let $n \ge 1$ be even and let
$A = \{1, n\}$. A position $p = (p_1, \dots, p_n)$ of Slow$A$-Nim on $n$ stacks is a P-position
if and only if its total number of tokens $p_1 + \dots + p_n$ and its smallest stack
$\min_i p_i$ are both even.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 2. -/
public theorem_wanted slowANim_one_n_even_isP_iff (n : ℕ) (hn : 0 < n) (hne : Even n)
    (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n {1, n}) p ↔
      Even (∑ i, p i) ∧ ∃ i, (∀ j, p i ≤ p j) ∧ Even (p i)

/-- **P-positions of Slow $\{1,2\}$-Nim on four stacks.** In Slow $A$-Nim with $A = \{1, 2\}$
on four stacks, let $p = (p_0, p_1, p_2, p_3)$ be a position with
$p_0 \le p_1 \le p_2 \le p_3$. Then $p$ is a P-position if and only if either all four stack
heights are even, or $p_0$ is even and $p_1$, $p_2$, $p_3$ are odd.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 3. -/
public theorem_wanted slowANim_one_two_four_isP_iff (p : Fin 4 → ℕ) (hp : Monotone p) :
    SpragueGrundy.IsP (slowANimGame 4 {1, 2}) p ↔
      (∀ i, Even (p i)) ∨ (Even (p 0) ∧ Odd (p 1) ∧ Odd (p 2) ∧ Odd (p 3))

/-- **P-positions of Slow A-Nim with A = {1, 2} on five stacks.** Let $A = \{1, 2\}$ and let
$p = (p_1, \dots, p_5)$ be a position of Slow$A$-Nim on five stacks in canonical form, that is,
$p_1 \le p_2 \le \dots \le p_5$. Then $p$ is a P-position if and only if all five stacks are
even, or $p_1, p_2$ are even and $p_3, p_4, p_5$ are odd, or $p_1, p_2, p_5$ are odd and
$p_3, p_4$ are even, or $p_1, p_2, p_3, p_4$ are odd and $p_5$ is even.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 3. -/
public theorem_wanted slowANim_one_two_five_isP_iff (p : Fin 5 → ℕ) (hp : Monotone p) :
    SpragueGrundy.IsP (slowANimGame 5 {1, 2}) p ↔
      (∀ i, Even (p i)) ∨
      (Even (p 0) ∧ Even (p 1) ∧ Odd (p 2) ∧ Odd (p 3) ∧ Odd (p 4)) ∨
      (Odd (p 0) ∧ Odd (p 1) ∧ Even (p 2) ∧ Even (p 3) ∧ Odd (p 4)) ∨
      (Odd (p 0) ∧ Odd (p 1) ∧ Odd (p 2) ∧ Odd (p 3) ∧ Even (p 4))

/-- **NIRB criterion for reduced positions.** Let $A \subseteq \{1, \dots, n\}$ be nonempty with
least element $a$, and let $p$ be a position of Slow $A$-Nim on $n$ stacks. Then $p$ is reduced
if and only if $a \cdot M \le \sum_i p_i$, where $M$ is the largest stack height of $p$ (taken
to be $0$ when $n = 0$).

The source assumes $n \ge 3$; the statement here is made for every $n$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 4. -/
public theorem_wanted slowANimReduced_iff_nirb (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hAne : A.Nonempty) (p : Fin n → ℕ) :
    SlowANimReduced A p ↔ A.min' hAne * Finset.univ.sup p ≤ ∑ i, p i

/-- **Legal move sequences depend only on the reduction.** Let $A \subseteq \{1, \dots, n\}$ and
let $p$ be a position of Slow$A$-Nim on $n$ stacks, with reduction $r(p)$. A finite sequence of
moves, each given by its set of stacks, is legal from $r(p)$ if and only if it is legal from $p$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 1. -/
public theorem_wanted slowANimLegalSeq_reduction_iff (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (p : Fin n → ℕ) (ss : List (Finset (Fin n))) :
    SlowANimLegalSeq A (slowANimReduction A p) ss ↔ SlowANimLegalSeq A p ss

/-- **Positions with the same reduction have the same outcome.** Let
$A \subseteq \{1, \dots, n\}$. If two positions $p$ and $q$ of Slow$A$-Nim $\mathrm{SN}(n, A)$
have the same reduction, $r(p) = r(q)$, then $p$ is a P-position if and only if $q$ is a
P-position.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Corollary 1. -/
public theorem_wanted slowANim_isP_iff_of_reduction_eq (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (p q : Fin n → ℕ)
    (h : slowANimReduction A p = slowANimReduction A q) :
    SpragueGrundy.IsP (slowANimGame n A) p ↔ SpragueGrundy.IsP (slowANimGame n A) q

/-- **Chopping a reduced position keeps it reduced.** Let $A \subseteq \{1, \dots, n\}$ and let
$p$ be a reduced position of Slow $A$-Nim on $n$ stacks. Then for every $m \in \mathbb{N}$ the
position $\mathrm{ctt}(p, m)$ with stack heights $\mathrm{ctt}(p, m)_i = \min(p_i, m)$ is
reduced.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 2. -/
public theorem_wanted slowANimReduced_min (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (p : Fin n → ℕ) (hp : SlowANimReduced A p) (m : ℕ) :
    SlowANimReduced A fun i => min (p i) m

/-- **The reduction chops at the largest reduced height.** Let $A \subseteq \{1, \dots, n\}$ and
let $p$ be a position of Slow$A$-Nim on $n$ stacks, with largest stack height $M = \max_i p_i$
($M = 0$ when $n = 0$). For $m \in \mathbb{N}$ write $\mathrm{ctt}(p, m)$ for the position whose
stack $i$ has height $\min(p_i, m)$. If $m \le M$, the position $\mathrm{ctt}(p, m)$ is reduced,
and $\mathrm{ctt}(p, m')$ is not reduced for any $m'$ with $m < m' \le M$, then the reduction of
$p$ is $r(p) = \mathrm{ctt}(p, m)$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 3. -/
public theorem_wanted slowANimReduction_eq_min (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (p : Fin n → ℕ) (m : ℕ) (hm : m ≤ Finset.univ.sup p)
    (hred : SlowANimReduced A fun i => min (p i) m)
    (hmax : ∀ m', m < m' → m' ≤ Finset.univ.sup p → ¬ SlowANimReduced A fun i => min (p i) m') :
    slowANimReduction A p = fun i => min (p i) m

/-- **P-positions of Slow $A$-Nim via the playable game graph.** Let $n \in \mathbb{N}$ and
$A \subseteq \{1, \dots, n\}$. Let $\tilde P$ be a set of P-positions for the moves of the
playable game graph of Slow$A$-Nim $\mathrm{SN}(n, A)$, whose positions are the reduced
positions: no position in $\tilde P$ has a move to a position in $\tilde P$, and every reduced
position outside $\tilde P$ has a move to a position in $\tilde P$. Then a position $p$ of
$\mathrm{SN}(n, A)$ is a P-position if and only if its reduction $r(p)$ lies in $\tilde P$.

This combines the source's two statements, one for P-positions and one for N-positions.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 5. -/
public theorem_wanted slowANim_isP_iff_reduction_mem (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) {P : Set {p : Fin n → ℕ // SlowANimReduced A p}}
    (hP : IsPPositionSet (SlowANimReducedGraphMove A) P) (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n A) p ↔ ∃ q ∈ P, q.1 = slowANimReduction A p

/-- **Options with reduction in Slow {n - 1}-Nim.** Let $n \ge 2$, $k = n - 1$ and $A = \{k\}$.
Let $p$ be a reduced position of Slow$A$-Nim on $n$ stacks, with $s = (p_1 + \dots + p_n) \bmod 2k$,
$o$ odd stacks, and maximum $M = \max_i p_i$ attained by $\alpha$ stacks. Let $p'$ be obtained
from $p$ by playing on a set $S$ of $k$ stacks, each holding at least one token in $p$, and
suppose that $p'$ is not reduced. Write $r = r(p')$ for its reduction,
$s' = (r_1 + \dots + r_n) \bmod 2k$ and $o'$ for the number of odd stacks of $r$. Then $M$ is
even if $s < k$ and odd if $s \ge k$. If $s \not\equiv 0 \pmod k$, then $r_i = \max(p_i - 1, 0)$
for every stack $i$, $o' = n - o$, and $s' = s + k - 1$ if $s < k$, $s' = s - (k + 1)$ if
$s > k$. If $s \equiv 0 \pmod k$, then $r_i = \max(p_i - 2, 0)$ for the stacks with $p_i = M$
and $r_i = \max(p_i - 1, 0)$ for the others; moreover, if $s = 0$ then
$\alpha \le \min(n - o, n - 2)$, $s' = k - 1 - \alpha$ and $o' = n - o - \alpha$, and if $s = k$
then $\alpha \le \min(o, n - 2)$, $s' = 2k - 1 - \alpha$ and $o' = n - o + \alpha$.

Stacks are labelled, so the paper's canonical-form display of $r(p')$ is written stackwise.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 6. -/
public theorem_wanted slowANim_n_sub_one_option_of_not_reduced (n : ℕ) (hn : 2 ≤ n)
    (p : Fin n → ℕ) (hp : SlowANimReduced {n - 1} p) (S : Finset (Fin n))
    (hS : S.card = n - 1) (hSp : ∀ i ∈ S, 1 ≤ p i)
    (hred : ¬ SlowANimReduced {n - 1} (slowANimAfter p S)) :
    let k := n - 1
    let s := (∑ i, p i) % (2 * k)
    let o := (Finset.univ.filter fun i => Odd (p i)).card
    let M := Finset.univ.sup p
    let α := (Finset.univ.filter fun i => p i = M).card
    let r := slowANimReduction {n - 1} (slowANimAfter p S)
    let s' := (∑ i, r i) % (2 * k)
    let o' := (Finset.univ.filter fun i => Odd (r i)).card
    (s < k → Even M) ∧ (k ≤ s → Odd M) ∧
      (s % k ≠ 0 → r = (fun i => p i - 1) ∧ o' = n - o ∧
        s' = if s < k then s + k - 1 else s - (k + 1)) ∧
      (s % k = 0 → r = (fun i => if p i = M then p i - 2 else p i - 1) ∧
        (s = 0 → α ≤ n - o ∧ α ≤ n - 2 ∧ s' = k - 1 - α ∧ o' = n - o - α) ∧
        (s = k → α ≤ o ∧ α ≤ n - 2 ∧ s' = 2 * k - 1 - α ∧ o' = n - o + α))

/-- **P-positions of the reduced game of Slow $\{n-1\}$-Nim.** Let $n \ge 2$ and $A = \{n - 1\}$,
and let $\tilde P$ be a set of P-positions of the playable game graph of Slow $A$-Nim on $n$
stacks: no move of that graph joins two elements of $\tilde P$, and every reduced position
outside $\tilde P$ has a move into $\tilde P$. For a reduced position $q$, let $s$ be the
remainder of $\sum_i q_i$ modulo $2(n - 1)$ and let $o$ be the number of stacks of $q$ of odd
height. Then $s$ and $o$ have the same parity, and $q \in \tilde P$ if and only if $s < n - 2$
and $o \le s$, or $s = n - 2$ and $o \equiv n \pmod 2$, or $n - 2 < s < 2n - 3$ and
$o \le 2(n - 2) - s$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 6. -/
public theorem_wanted slowANimReduced_mem_pPositions_n_sub_one_iff (n : ℕ) (hn : 2 ≤ n)
    {P : Set {p : Fin n → ℕ // SlowANimReduced {n - 1} p}}
    (hP : IsPPositionSet (SlowANimReducedGraphMove {n - 1}) P)
    (q : {p : Fin n → ℕ // SlowANimReduced {n - 1} p}) :
    let s := (∑ i, q.1 i) % (2 * (n - 1))
    let o := (Finset.univ.filter fun i => Odd (q.1 i)).card
    s % 2 = o % 2 ∧
      (q ∈ P ↔ (s < n - 2 ∧ o ≤ s) ∨ (s = n - 2 ∧ o % 2 = n % 2) ∨
        (n - 2 < s ∧ s < 2 * (n - 1) - 1 ∧ o ≤ 2 * (n - 2) - s))

/-- **P-positions of the reduced game of Slow $\{n-1, n\}$-Nim.** Let $n \ge 2$ and
$A = \{n - 1, n\}$, and let $\tilde P$ be a set of P-positions of the playable game graph of
Slow $A$-Nim on $n$ stacks: no move of that graph joins two elements of $\tilde P$, and every
reduced position outside $\tilde P$ has a move into $\tilde P$. For a reduced position $q$, let
$s$ be the remainder of $\sum_i q_i$ modulo $2n - 2$ and let $o$ be the number of stacks of $q$
of odd height. Then $s$ and $o$ have the same parity, and $q \in \tilde P$ if and only if
$s < n - 2$ and $o \le s$, or $s = n - 2$, $o \equiv n \pmod 2$ and $o \ne n$, or
$n - 2 < s < 2n - 3$ and $o \le 2(n - 2) - s$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 8. -/
public theorem_wanted slowANimReduced_mem_pPositions_n_sub_one_n_iff (n : ℕ) (hn : 2 ≤ n)
    {P : Set {p : Fin n → ℕ // SlowANimReduced {n - 1, n} p}}
    (hP : IsPPositionSet (SlowANimReducedGraphMove {n - 1, n}) P)
    (q : {p : Fin n → ℕ // SlowANimReduced {n - 1, n} p}) :
    let s := (∑ i, q.1 i) % (2 * n - 2)
    let o := (Finset.univ.filter fun i => Odd (q.1 i)).card
    s % 2 = o % 2 ∧
      (q ∈ P ↔ (s < n - 2 ∧ o ≤ s) ∨ (s = n - 2 ∧ o % 2 = n % 2 ∧ o ≠ n) ∨
        (n - 2 < s ∧ s < 2 * n - 3 ∧ o ≤ 2 * (n - 2) - s))

end

end MetaMathlibExt
