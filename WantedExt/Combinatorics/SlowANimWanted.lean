/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Logic.Relation
public import MathlibExt.GameTheory.ImpartialAcyclicGame
public import MathlibExt.GameTheory.SpragueGrundy

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

/-- **Playing on a set of stacks.** Let $p$ be a position of Slow$A$-Nim on $n$ stacks, with
$p_i$ tokens on stack $i$, and let $S$ be a set of stacks. The position after playing on $S$ is
obtained by removing one token from each stack of $S$: its stack $i$ holds $p_i - 1$ if
$i \in S$ and $p_i$ otherwise, where an empty stack of $S$ stays empty.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 1. -/
public def slowANimAfter {n : ℕ} (p : Fin n → ℕ) (S : Finset (Fin n)) : Fin n → ℕ :=
  fun i => if i ∈ S then p i - 1 else p i

/-- **Options in Slow A-Nim.** Let $A$ be a finite set of natural numbers and $p$ a position on
$n$ stacks. The options of $p$ in Slow$A$-Nim are the positions obtained from $p$ by choosing a
nonempty set $S$ of stacks with $|S| \in A$, each holding at least one token, and removing one
token from each stack of $S$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 1. -/
public def slowANimMoves {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
      fun S => S.Nonempty ∧ S.card ∈ A ∧ ∀ i ∈ S, 1 ≤ p i).image (slowANimAfter p)

/-- **Moves in Slow$A$-Nim decrease the token count.** For every finite set $A$ of natural numbers
and all positions $p$, $q$ of Slow$A$-Nim on $n$ stacks, if $q$ is reached from $p$ by one move,
then the total number of tokens strictly decreases: $\sum_i q_i < \sum_i p_i$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 1. -/
public theorem sum_lt_of_mem_slowANimMoves {n : ℕ} (A : Finset ℕ) (p q : Fin n → ℕ)
    (h : q ∈ slowANimMoves A p) : ∑ i, q i < ∑ i, p i := by
  simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter] at h
  obtain ⟨S, ⟨-, hne, -, hp⟩, rfl⟩ := h
  obtain ⟨j, hj⟩ := hne
  apply Finset.sum_lt_sum
  · intro i _
    unfold slowANimAfter
    split_ifs <;> omega
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    have := hp j hj
    simp only [slowANimAfter, hj, ite_true]
    omega

/-- **Slow$A$-Nim.** For $n \in \mathbb{N}$ and a finite set $A$ of natural numbers, Slow$A$-Nim
$\mathrm{SN}(n, A)$ is the impartial game whose positions assign a number $p_i$ of tokens to
each of $n$ labelled stacks $i$, and whose options from $p$ are obtained by choosing a nonempty
set $S$ of stacks with $|S| \in A$, each holding at least one token, and removing one token from
each stack of $S$. Its rank is the total number of tokens $\sum_i p_i$, which every move lowers,
and its start position is the empty position.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 1. -/
public def slowANimGame (n : ℕ) (A : Finset ℕ) : SpragueGrundy.ImpartialGame where
  Pos := Fin n → ℕ
  eqDec := inferInstance
  moves := slowANimMoves A
  rank := fun p => ∑ i, p i
  rank_lt := sum_lt_of_mem_slowANimMoves A
  start := fun _ => 0

/-- **The empty position has no options.** For every finite set $A$ of natural numbers, the
position of Slow$A$-Nim on $n$ stacks in which every stack is empty has no options.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Section 2. -/
public theorem slowANimMoves_zero {n : ℕ} (A : Finset ℕ) :
    slowANimMoves A (fun _ : Fin n => 0) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rw [slowANimMoves, Finset.mem_image] at hq
  obtain ⟨S, hS, -⟩ := hq
  rw [Finset.mem_filter] at hS
  obtain ⟨-, ⟨j, hj⟩, -, hp⟩ := hS
  have := hp j hj
  omega

/-- **The empty position is a P-position.** For every $n$ and every finite set $A$ of natural
numbers, the position of Slow$A$-Nim $\mathrm{SN}(n, A)$ with all $n$ stacks empty is a
P-position, since it has no options.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Section 2. -/
public theorem slowANim_isP_zero (n : ℕ) (A : Finset ℕ) :
    SpragueGrundy.IsP (slowANimGame n A) (fun _ => 0) := by
  refine (SpragueGrundy.isP_iff (slowANimGame n A) (fun _ => 0)).2 ?_
  intro q hq
  have h0 : (slowANimGame n A).moves (fun _ => 0) = ∅ := slowANimMoves_zero A
  rw [h0] at hq
  simp at hq

/-- **Reduced positions of Slow $A$-Nim.** A position $p$ of Slow $A$-Nim on $n$ stacks is
reduced when for every stack $i$ there is a terminal position $t$ (one with no options) that is
reachable from $p$ by a sequence of zero or more moves and has $t_i = 0$.

In the source's notation, $u_i(p) = \min_j t^{(j)}_i(p)$, the minimum over the terminal
positions $t^{(j)}(p)$ reachable from $p$, counts the unplayable tokens of stack $i$, and $p$ is
reduced exactly when $u_i(p) = 0$ for every $i$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 3.1. -/
public def SlowANimReduced {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) : Prop :=
  ∀ i, ∃ t, Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p t ∧
    slowANimMoves A t = ∅ ∧ t i = 0

/-- **Reduction of a Slow$A$-Nim position.** Let $A$ be a finite set of natural numbers and let $p$
be a position of Slow$A$-Nim on $n$ stacks. For each stack $i$, let $u_i(p)$ be the least height
of stack $i$ over all terminal positions (positions with no moves) reachable from $p$ by a sequence
of zero or more moves. The reduction of $p$ is the position $r(p)$ with $r(p)_i = p_i - u_i(p)$
for every stack $i$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 3.1. -/
public noncomputable def slowANimReduction {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) :
    Fin n → ℕ :=
  fun i => p i - sInf ((fun t : Fin n → ℕ => t i) ''
    {t | Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p t ∧
      slowANimMoves A t = ∅})

/-- **The empty position is reduced.** For every finite set $A$ of natural numbers and every
$n$, the position of Slow $A$-Nim on $n$ stacks in which every stack is empty is reduced.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 3.1. -/
public theorem slowANimReduced_zero {n : ℕ} (A : Finset ℕ) :
    SlowANimReduced A (fun _ : Fin n => 0) := by
  intro i
  exact ⟨fun _ => 0, Relation.ReflTransGen.refl, slowANimMoves_zero A, rfl⟩

/-- **The reduction never adds tokens.** For every finite set $A$ of natural numbers, every
position $p$ of Slow$A$-Nim on $n$ stacks and every stack $i$, the reduction $r(p)$ of $p$
satisfies $r(p)_i \le p_i$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 3.1. -/
public theorem slowANimReduction_le {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) (i : Fin n) :
    slowANimReduction A p i ≤ p i :=
  Nat.sub_le _ _

/-- **Legal move sequences in Slow A-Nim.** Let $A$ be a finite set of natural numbers and $p$ a
position of Slow$A$-Nim on $n$ stacks. A finite sequence $S_1, \dots, S_m$ of sets of stacks is
legal from $p$ when it is empty, or when $S_1$ is nonempty, $|S_1| \in A$, every stack in $S_1$
holds at least one token in $p$, and $S_2, \dots, S_m$ is legal from the position obtained from
$p$ by removing one token from each stack of $S_1$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 1 and its proof. -/
public def SlowANimLegalSeq {n : ℕ} (A : Finset ℕ) : (Fin n → ℕ) → List (Finset (Fin n)) → Prop
  | _, [] => True
  | p, S :: ss =>
    S.Nonempty ∧ S.card ∈ A ∧ (∀ i ∈ S, 1 ≤ p i) ∧ SlowANimLegalSeq A (slowANimAfter p S) ss

/-- **The empty move sequence is legal.** For every finite set $A$ of natural numbers and every
position $p$ of Slow$A$-Nim on $n$ stacks, the empty sequence of moves is legal from $p$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 1 and its proof. -/
public theorem slowANimLegalSeq_nil {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) :
    SlowANimLegalSeq A p [] :=
  trivial

/-- **Set of P-positions.** Let $R$ be a move relation on a type of positions, where $R\,x\,y$
means that $y$ is an option of $x$. A set $P$ of positions is a set of P-positions for $R$ when
no position of $P$ has an option in $P$, and every position outside $P$ has an option in $P$.

When there is no infinite sequence of moves, there is at most one such set.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Section 1 (characterization of P-positions). -/
public def IsPPositionSet {α : Type*} (R : α → α → Prop) (P : Set α) : Prop :=
  (∀ x y, x ∈ P → R x y → y ∉ P) ∧ ∀ x, x ∉ P → ∃ y, R x y ∧ y ∈ P

/-- **Uniqueness of the set of P-positions.** Let $R$ be a move relation on a type of positions,
where $R\,x\,y$ means that $y$ is an option of $x$, and suppose that there is no infinite
sequence of moves (the relation "$y$ is an option of $x$" is well-founded). If $P$ and $Q$ are
both sets of P-positions for $R$, then $P = Q$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Section 1 (characterization of P-positions). -/
public theorem IsPPositionSet.eq {α : Type*} {R : α → α → Prop}
    (hR : WellFounded fun y x => R x y) {P Q : Set α} (hP : IsPPositionSet R P)
    (hQ : IsPPositionSet R Q) : P = Q :=
  pPositions_unique R hR P Q hP.1 hP.2 hQ.1 hQ.2

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

/-- **P-positions of Slow A-Nim with A = {1, k}, k odd.** Let $k$ be odd with $1 \le k \le n$
and let $A = \{1, k\}$. A position $p = (p_1, \dots, p_n)$ of Slow$A$-Nim on $n$ stacks is a
P-position if and only if its total number of tokens $p_1 + \dots + p_n$ is even.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 2. -/
public theorem_wanted slowANim_one_odd_isP_iff (n k : ℕ) (hA : ({1, k} : Finset ℕ) ⊆ Finset.Icc 1 n)
    (hk : Odd k) (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n {1, k}) p ↔ Even (∑ i, p i)

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

/-- **P-positions of Slow $\{1,2\}$-Nim on three stacks.** In Slow $A$-Nim with $A = \{1, 2\}$
on three stacks, let $p = (p_0, p_1, p_2)$ be a position with $p_0 \le p_1 \le p_2$. Then $p$
is a P-position if and only if its three stack heights are all even or all odd.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 3. -/
public theorem_wanted slowANim_one_two_three_isP_iff (p : Fin 3 → ℕ) (hp : Monotone p) :
    SpragueGrundy.IsP (slowANimGame 3 {1, 2}) p ↔ (∀ i, Even (p i)) ∨ ∀ i, Odd (p i)

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

/-- **General reduction lemma.** Let $A \subseteq \{1, \dots, n\}$ be nonempty with least element
$a$, and let $p$ be a reduced position of Slow$A$-Nim $\mathrm{SN}(n, A)$ with largest stack
height $M$ and total $\Sigma(p) = \sum_i p_i$. Let $S$ be a set of $\ell \in A$ stacks, each
holding at least one token, and suppose that the position obtained from $p$ by removing one token
from each stack of $S$ is not reduced. Then $a M \le \Sigma(p)$ and, writing
$r = \Sigma(p) - a M$, either (R1) $\ell > a$, every stack of height $M$ lies in $S$, and
$r < \ell - a$; or (R2) some stack of height $M$ is not in $S$, and $r < \ell$.

The hypothesis that $p$ is reduced is implicit in the source, whose proof uses $r \ge 0$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 4. -/
public theorem_wanted slowANim_generalReduction (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hAne : A.Nonempty) (p : Fin n → ℕ) (hp : SlowANimReduced A p)
    (S : Finset (Fin n)) (hS : S.card ∈ A) (hSp : ∀ i ∈ S, 1 ≤ p i)
    (hnot : ¬ SlowANimReduced A (slowANimAfter p S)) :
    (A.min' hAne < S.card ∧ (∀ i, p i = Finset.univ.sup p → i ∈ S) ∧
        A.min' hAne * Finset.univ.sup p ≤ ∑ i, p i ∧
        ∑ i, p i < A.min' hAne * Finset.univ.sup p + (S.card - A.min' hAne)) ∨
      ((∃ i, p i = Finset.univ.sup p ∧ i ∉ S) ∧
        A.min' hAne * Finset.univ.sup p ≤ ∑ i, p i ∧
        ∑ i, p i < A.min' hAne * Finset.univ.sup p + S.card)

/-- **P-positions after adding moves.** Let $M$ and $E$ be move relations on a type of positions,
let $P$ be a set of P-positions for $M$, and let $Q \subseteq P$. Suppose that (1) no element of
$P \setminus Q$ has an $E$-move to an element of $P \setminus Q$, (2) every position outside $P$
that has an $M$-move into $Q$ has an $M$-move or an $E$-move into $P \setminus Q$, and (3) every
position of $Q$ has an $E$-move into $P \setminus Q$. Then $P \setminus Q$ is a set of
P-positions for the move relation "$M$ or $E$".

The relations $M$ and $E$ need not be disjoint.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Proposition 7. -/
public theorem_wanted isPPositionSet_extend {α : Type*} (M E : α → α → Prop) (P Q : Set α)
    (hP : IsPPositionSet M P) (hQP : Q ⊆ P)
    (h1 : ∀ x y, x ∈ P \ Q → y ∈ P \ Q → ¬ E x y)
    (h2 : ∀ x, x ∉ P → (∃ y ∈ Q, M x y) → ∃ y ∈ P \ Q, M x y ∨ E x y)
    (h3 : ∀ x ∈ Q, ∃ y ∈ P \ Q, E x y) :
    IsPPositionSet (fun x y => M x y ∨ E x y) (P \ Q)

/-- **Moves of the playable game graph of Slow $A$-Nim.** The playable (reduced) game graph of
Slow $A$-Nim on $n$ stacks has the reduced positions as its positions. For reduced positions
$x$ and $y$, there is a move from $x$ to $y$ when $y$ is the reduction $r(q)$ of some option
$q$ of $x$ in Slow $A$-Nim, that is, of some position reached from $x$ by one legal move.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition 3. -/
public def SlowANimReducedGraphMove {n : ℕ} (A : Finset ℕ)
    (x y : {p : Fin n → ℕ // SlowANimReduced A p}) : Prop :=
  ∃ q ∈ slowANimMoves A x.1, y.1 = slowANimReduction A q

/-- **The empty position is terminal in the playable game graph.** For every $n$ and every finite
set $A$ of natural numbers, the position of Slow$A$-Nim $\mathrm{SN}(n, A)$ with all $n$ stacks
empty has no move to any position in the playable game graph of $\mathrm{SN}(n, A)$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition 3. -/
public theorem not_slowANimReducedGraphMove_zero {n : ℕ} (A : Finset ℕ)
    (y : {p : Fin n → ℕ // SlowANimReduced A p}) :
    ¬ SlowANimReducedGraphMove A ⟨fun _ => 0, slowANimReduced_zero A⟩ y := by
  rintro ⟨q, hq, -⟩
  rw [slowANimMoves_zero] at hq
  simp at hq

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

/-- **Options without reduction in Slow {n - 1}-Nim.** Let $n \ge 2$, $k = n - 1$ and $A = \{k\}$,
so that a move removes one token from each of exactly $k$ nonempty stacks. Let $p$ be a reduced
position of Slow$A$-Nim on $n$ stacks, with $s = (p_1 + \dots + p_n) \bmod 2k$ and $o$ odd stacks.
Let $p'$ be obtained from $p$ by playing on a set $S$ of $k$ stacks, each holding at least one
token in $p$, and let $j$ be the stack not in $S$. If $p'$ is reduced, then
$s' = (p'_1 + \dots + p'_n) \bmod 2k$ equals $s + k$ when $s < k$ and $s - k$ when $s \ge k$, and
the number $o'$ of odd stacks of $p'$ is $n - o + 1$ if $p_j$ is odd and $n - o - 1$ if $p_j$ is
even.

The closing remark of Lemma 5 that both values of $o'$ are legal when $0 < o < n$ is omitted: it
fails for $n = 3$ at $p = (0, 1, 1)$, whose only move omits the empty stack.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 5. -/
public theorem_wanted slowANim_n_sub_one_option_of_reduced (n : ℕ) (hn : 2 ≤ n)
    (p : Fin n → ℕ) (hp : SlowANimReduced {n - 1} p) (S : Finset (Fin n))
    (hS : S.card = n - 1) (hSp : ∀ i ∈ S, 1 ≤ p i)
    (hred : SlowANimReduced {n - 1} (slowANimAfter p S)) (j : Fin n) (hj : j ∉ S) :
    (∑ i, slowANimAfter p S i) % (2 * (n - 1)) =
        (if (∑ i, p i) % (2 * (n - 1)) < n - 1 then (∑ i, p i) % (2 * (n - 1)) + (n - 1)
          else (∑ i, p i) % (2 * (n - 1)) - (n - 1)) ∧
      (Finset.univ.filter fun i => Odd (slowANimAfter p S i)).card =
        if Odd (p j) then n - (Finset.univ.filter fun i => Odd (p i)).card + 1
        else n - (Finset.univ.filter fun i => Odd (p i)).card - 1

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
