/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Logic.Relation
public import MathlibExt.GameTheory.ImpartialAcyclicGame
public import MathlibExt.GameTheory.SpragueGrundy

/-!
# Slow A-Nim

A move removes one token from each selected stack. When all but one stack are played,
the change in the total token count and the parity of the omitted stack determine the
new residue and the number of odd stacks.
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

set_option linter.unusedVariables false in
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
public theorem slowANim_n_sub_one_option_of_reduced (n : ℕ) (hn : 2 ≤ n)
    (p : Fin n → ℕ) (hp : SlowANimReduced {n - 1} p) (S : Finset (Fin n))
    (hS : S.card = n - 1) (hSp : ∀ i ∈ S, 1 ≤ p i)
    (hred : SlowANimReduced {n - 1} (slowANimAfter p S)) (j : Fin n) (hj : j ∉ S) :
    (∑ i, slowANimAfter p S i) % (2 * (n - 1)) =
        (if (∑ i, p i) % (2 * (n - 1)) < n - 1 then (∑ i, p i) % (2 * (n - 1)) + (n - 1)
          else (∑ i, p i) % (2 * (n - 1)) - (n - 1)) ∧
      (Finset.univ.filter fun i => Odd (slowANimAfter p S i)).card =
        if Odd (p j) then n - (Finset.univ.filter fun i => Odd (p i)).card + 1
        else n - (Finset.univ.filter fun i => Odd (p i)).card - 1 := by
  have hsum : (∑ i, slowANimAfter p S i) + (n - 1) = ∑ i, p i := by
    calc
      _ = ∑ i, (slowANimAfter p S i + if i ∈ S then 1 else 0) := by
        simp [Finset.sum_add_distrib, ← Finset.sum_filter, hS]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [slowANimAfter, hi, Nat.sub_add_cancel (hSp i hi)]
        · simp [slowANimAfter, hi]
  constructor
  · set k := n - 1
    have hk : 0 < k := by dsimp [k]; omega
    have hshift : (∑ i, slowANimAfter p S i) + 2 * k = (∑ i, p i) + k := by
      omega
    rw [← Nat.add_mod_right (∑ i, slowANimAfter p S i) (2 * k), hshift, ← Nat.mod_add_mod]
    have hlt := Nat.mod_lt (∑ i, p i) (show 0 < 2 * k by omega)
    split_ifs with h
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · have hall : insert j S = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simp [hj, hS]
      omega
    have hflip : (S.filter fun i => Odd (slowANimAfter p S i)) =
        S.filter fun i => ¬ Odd (p i) := by
      apply Finset.filter_congr
      intro i hi
      have := hSp i hi
      simp only [slowANimAfter, hi, ite_true, Nat.odd_iff]
      omega
    have hcount := Finset.card_filter_add_card_filter_not (s := S) (fun i => Odd (p i))
    have hj' : slowANimAfter p S j = p j := by simp [slowANimAfter, hj]
    rw [← hall]
    simp only [Finset.filter_insert, hj', hflip]
    simp only [Nat.not_odd_iff_even] at hcount
    by_cases hodd : Odd (p j) <;> simp [hodd, hj] <;> omega

end

end MetaMathlibExt
