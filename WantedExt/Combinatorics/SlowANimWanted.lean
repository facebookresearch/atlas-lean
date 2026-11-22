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

/-- The position after playing on the stacks in `S`: one token is removed from each stack of
`S`.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 1. -/
public def slowANimAfter {n : ℕ} (p : Fin n → ℕ) (S : Finset (Fin n)) : Fin n → ℕ :=
  fun i => if i ∈ S then p i - 1 else p i

/-- The options of `p` in Slow`A`-Nim: play on a nonempty set `S` of `|S| ∈ A` stacks, each
holding at least one token.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 1. -/
public def slowANimMoves {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
      fun S => S.Nonempty ∧ S.card ∈ A ∧ ∀ i ∈ S, 1 ≤ p i).image (slowANimAfter p)

/-- A move removes tokens, so the total number of tokens strictly decreases.

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

/-- Slow`A`-Nim `SN(n, A)` as an `ImpartialGame` (ranked by the token count; the `start`
field is unused here and set to the empty position).

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 1. -/
public def slowANimGame (n : ℕ) (A : Finset ℕ) : SpragueGrundy.ImpartialGame where
  Pos := Fin n → ℕ
  eqDec := inferInstance
  moves := slowANimMoves A
  rank := fun p => ∑ i, p i
  rank_lt := sum_lt_of_mem_slowANimMoves A
  start := fun _ => 0

/-- The empty position has no options.

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

/-- The empty position is a P-position (it has no options).

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Section 2. -/
public theorem slowANim_isP_zero (n : ℕ) (A : Finset ℕ) :
    SpragueGrundy.IsP (slowANimGame n A) (fun _ => 0) := by
  refine (SpragueGrundy.isP_iff (slowANimGame n A) (fun _ => 0)).2 ?_
  intro q hq
  have h0 : (slowANimGame n A).moves (fun _ => 0) = ∅ := slowANimMoves_zero A
  rw [h0] at hq
  simp at hq

/-- A position `p` is reduced (has no unplayable tokens): for every stack `i` some terminal
position reachable from `p` has stack `i` empty, i.e. `u_i(p) = 0` for all `i` in the paper's
notation `u_i(p) = min_j t^{(j)}_i(p)` over the terminal positions `t^{(j)}(p)` of `p`.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 3.1. -/
public def SlowANimReduced {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) : Prop :=
  ∀ i, ∃ t, Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p t ∧
    slowANimMoves A t = ∅ ∧ t i = 0

/-- The reduction `r(p) = p - u(p)`, where `u_i(p)` is the least height of stack `i` over the
terminal positions reachable from `p`.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 3.1. -/
public noncomputable def slowANimReduction {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) :
    Fin n → ℕ :=
  fun i => p i - sInf ((fun t : Fin n → ℕ => t i) ''
    {t | Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p t ∧
      slowANimMoves A t = ∅})

/-- The empty position is reduced.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 3.1. -/
public theorem slowANimReduced_zero {n : ℕ} (A : Finset ℕ) :
    SlowANimReduced A (fun _ : Fin n => 0) := by
  intro i
  exact ⟨fun _ => 0, Relation.ReflTransGen.refl, slowANimMoves_zero A, rfl⟩

/-- The reduction never adds tokens: `r(p)_i ≤ p_i`.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition in Section 3.1. -/
public theorem slowANimReduction_le {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) (i : Fin n) :
    slowANimReduction A p i ≤ p i :=
  Nat.sub_le _ _

/-- Legality of a sequence of Slow`A`-Nim moves (each move given by its set of stacks) from a
position.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 1 and its proof. -/
public def SlowANimLegalSeq {n : ℕ} (A : Finset ℕ) : (Fin n → ℕ) → List (Finset (Fin n)) → Prop
  | _, [] => True
  | p, S :: ss =>
    S.Nonempty ∧ S.card ∈ A ∧ (∀ i ∈ S, 1 ≤ p i) ∧ SlowANimLegalSeq A (slowANimAfter p S) ss

/-- The empty move sequence is legal from every position.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 1 and its proof. -/
public theorem slowANimLegalSeq_nil {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) :
    SlowANimLegalSeq A p [] :=
  trivial

/-- A set `P` of positions is the set of P-positions of the game with move relation `R`
(`R x y`: `y` is an option of `x`) when no move joins two elements of `P` and every position
outside `P` has a move into `P`; for a terminating game this set is unique
(`IsPPositionSet.eq`).

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Section 1 (characterization of P-positions). -/
public def IsPPositionSet {α : Type*} (R : α → α → Prop) (P : Set α) : Prop :=
  (∀ x y, x ∈ P → R x y → y ∉ P) ∧ ∀ x, x ∉ P → ∃ y, R x y ∧ y ∈ P

/-- For a terminating game, the set of P-positions is unique.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Section 1 (characterization of P-positions). -/
public theorem IsPPositionSet.eq {α : Type*} {R : α → α → Prop}
    (hR : WellFounded fun y x => R x y) {P Q : Set α} (hP : IsPPositionSet R P)
    (hQ : IsPPositionSet R Q) : P = Q :=
  pPositions_unique R hR P Q hP.1 hP.2 hQ.1 hQ.2

/-- Proposition 1 (Partial Structure Result): in `SN(n, A)`, a position with no odd stack is
a P-position, and a position whose number of odd stacks lies in `A` is an N-position.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Proposition 1. -/
public theorem_wanted slowANim_partialStructure (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (p : Fin n → ℕ) :
    ((∀ i, Even (p i)) → SpragueGrundy.IsP (slowANimGame n A) p) ∧
      ((Finset.univ.filter fun i => Odd (p i)).card ∈ A →
        ¬ SpragueGrundy.IsP (slowANimGame n A) p)

/-- Theorem 2 (1): for `A = {1, k}` with `k` odd, the P-positions of `SN(n, A)` are the
positions with an even number of tokens.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 2. -/
public theorem_wanted slowANim_one_odd_isP_iff (n k : ℕ) (hA : ({1, k} : Finset ℕ) ⊆ Finset.Icc 1 n)
    (hk : Odd k) (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n {1, k}) p ↔ Even (∑ i, p i)

/-- Theorem 2 (2): for `A = {1, n}` with `n` even, the P-positions of `SN(n, A)` are the
positions whose token count and minimal stack are both even.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 2. -/
public theorem_wanted slowANim_one_n_even_isP_iff (n : ℕ) (hn : 0 < n) (hne : Even n)
    (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n {1, n}) p ↔
      Even (∑ i, p i) ∧ ∃ i, (∀ j, p i ≤ p j) ∧ Even (p i)

/-- Theorem 3 (1): for `A = {1, 2}` and `n = 3`, a position in canonical (non-decreasing)
form is a P-position iff its parity pattern is `(e,e,e)` or `(o,o,o)`.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 3. -/
public theorem_wanted slowANim_one_two_three_isP_iff (p : Fin 3 → ℕ) (hp : Monotone p) :
    SpragueGrundy.IsP (slowANimGame 3 {1, 2}) p ↔ (∀ i, Even (p i)) ∨ ∀ i, Odd (p i)

/-- Theorem 3 (2): for `A = {1, 2}` and `n = 4`, a position in canonical form is a
P-position iff its parity pattern is `(e,e,e,e)` or `(e,o,o,o)`.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 3. -/
public theorem_wanted slowANim_one_two_four_isP_iff (p : Fin 4 → ℕ) (hp : Monotone p) :
    SpragueGrundy.IsP (slowANimGame 4 {1, 2}) p ↔
      (∀ i, Even (p i)) ∨ (Even (p 0) ∧ Odd (p 1) ∧ Odd (p 2) ∧ Odd (p 3))

/-- Theorem 3 (3): for `A = {1, 2}` and `n = 5`, a position in canonical form is a
P-position iff its parity pattern is `(e,e,e,e,e)`, `(e,e,o,o,o)`, `(o,o,e,e,o)` or
`(o,o,o,o,e)`.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 3. -/
public theorem_wanted slowANim_one_two_five_isP_iff (p : Fin 5 → ℕ) (hp : Monotone p) :
    SpragueGrundy.IsP (slowANimGame 5 {1, 2}) p ↔
      (∀ i, Even (p i)) ∨
      (Even (p 0) ∧ Even (p 1) ∧ Odd (p 2) ∧ Odd (p 3) ∧ Odd (p 4)) ∨
      (Odd (p 0) ∧ Odd (p 1) ∧ Even (p 2) ∧ Even (p 3) ∧ Odd (p 4)) ∨
      (Odd (p 0) ∧ Odd (p 1) ∧ Odd (p 2) ∧ Odd (p 3) ∧ Even (p 4))

/-- Theorem 4 (NIRB condition): for `a = min A`, a position `p` of `SN(n, A)` is
reduced iff `a · max(p) ≤ Σ(p)`. The paper assumes `n ≥ 3`; the statement is kept for all `n`
(exhaustive checks for `n = 1, 2` agree).

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 4. -/
public theorem_wanted slowANimReduced_iff_nirb (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hAne : A.Nonempty) (p : Fin n → ℕ) :
    SlowANimReduced A p ↔ A.min' hAne * Finset.univ.sup p ≤ ∑ i, p i

/-- Lemma 1: a sequence of moves is legal from `p` iff it is legal from its reduction `r(p)`.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 1. -/
public theorem_wanted slowANimLegalSeq_reduction_iff (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (p : Fin n → ℕ) (ss : List (Finset (Fin n))) :
    SlowANimLegalSeq A (slowANimReduction A p) ss ↔ SlowANimLegalSeq A p ss

/-- Corollary 1: positions with the same reduction are in the same outcome class.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Corollary 1. -/
public theorem_wanted slowANim_isP_iff_of_reduction_eq (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (p q : Fin n → ℕ)
    (h : slowANimReduction A p = slowANimReduction A q) :
    SpragueGrundy.IsP (slowANimGame n A) p ↔ SpragueGrundy.IsP (slowANimGame n A) q

/-- Lemma 2: chopping a reduced position at any height `m` (`ctt(p, m)_i = min(p_i, m)`) gives
a reduced position.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 2. -/
public theorem_wanted slowANimReduced_min (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (p : Fin n → ℕ) (hp : SlowANimReduced A p) (m : ℕ) :
    SlowANimReduced A fun i => min (p i) m

/-- Lemma 3: `r(p) = ctt(p, m)` for the largest `m ≤ max(p)` with `ctt(p, m)` reduced.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 3. -/
public theorem_wanted slowANimReduction_eq_min (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (p : Fin n → ℕ) (m : ℕ) (hm : m ≤ Finset.univ.sup p)
    (hred : SlowANimReduced A fun i => min (p i) m)
    (hmax : ∀ m', m < m' → m' ≤ Finset.univ.sup p → ¬ SlowANimReduced A fun i => min (p i) m') :
    slowANimReduction A p = fun i => min (p i) m

/-- Lemma 4 (General Reduction Lemma): if a move on a set `S` of `ℓ = |S| ∈ A` stacks from a
reduced position `p` leads to a position that is not reduced, then, with `a = min A`,
`M = max(p)` and `Σ(p) = a M + r`, either (R1) `ℓ > a`, all maximal stacks are played on and
`0 ≤ r < ℓ - a`, or (R2) some maximal stack is omitted and `0 ≤ r < ℓ`. The hypothesis that
`p` is reduced is implicit in the paper (its proof uses `r ≥ 0`, the NIRB condition for `p`).

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

/-- Proposition 7: let `P` be the P-positions of a game with move relation `M`, and extend the
moves by `E`. If `Q ⊆ P` is such that (1) no move in `E` joins two elements of `P \ Q`, (2)
every N-position with an `M`-move into `Q` has an `M ∪ E`-move into `P \ Q`, and (3) every
position of `Q` has an `E`-move into `P \ Q`, then `P \ Q` is the set of P-positions of the
extended game (so its N-positions are `N ∪ Q`). The paper's disjointness `M ∩ E = ∅` is not
needed and is omitted.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Proposition 7. -/
public theorem_wanted isPPositionSet_extend {α : Type*} (M E : α → α → Prop) (P Q : Set α)
    (hP : IsPPositionSet M P) (hQP : Q ⊆ P)
    (h1 : ∀ x y, x ∈ P \ Q → y ∈ P \ Q → ¬ E x y)
    (h2 : ∀ x, x ∉ P → (∃ y ∈ Q, M x y) → ∃ y ∈ P \ Q, M x y ∨ E x y)
    (h3 : ∀ x ∈ Q, ∃ y ∈ P \ Q, E x y) :
    IsPPositionSet (fun x y => M x y ∨ E x y) (P \ Q)

/-- The move relation of the playable (reduced) game graph `G̃` of `SN(n, A)`: its positions are
the reduced positions, and a move from `p` goes to the reduction `r(p')` of an option `p'` of `p`
in `SN(n, A)` (the paper's adjusted move `m̃ = m + Δu(p')`).

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition 3. -/
public def SlowANimReducedGraphMove {n : ℕ} (A : Finset ℕ)
    (x y : {p : Fin n → ℕ // SlowANimReduced A p}) : Prop :=
  ∃ q ∈ slowANimMoves A x.1, y.1 = slowANimReduction A q

/-- The empty position has no moves in the playable game graph.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Definition 3. -/
public theorem not_slowANimReducedGraphMove_zero {n : ℕ} (A : Finset ℕ)
    (y : {p : Fin n → ℕ // SlowANimReduced A p}) :
    ¬ SlowANimReducedGraphMove A ⟨fun _ => 0, slowANimReduced_zero A⟩ y := by
  rintro ⟨q, hq, -⟩
  rw [slowANimMoves_zero] at hq
  simp at hq

/-- Game graph correspondence: if `P̃` is the set of P-positions of the playable game graph `G̃`
of `SN(n, A)`, then a position `p` of `SN(n, A)` is a P-position exactly when its reduction
`r(p)` lies in `P̃` (the paper's two "only if" statements, for `P` and for `N = Pᶜ`, together).

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 5. -/
public theorem_wanted slowANim_isP_iff_reduction_mem (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) {P : Set {p : Fin n → ℕ // SlowANimReduced A p}}
    (hP : IsPPositionSet (SlowANimReducedGraphMove A) P) (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n A) p ↔ ∃ q ∈ P, q.1 = slowANimReduction A p

/-- Options without reduction in `SN(n, k)`, `k = n - 1` (`n ≥ 2`). Let `p` be reduced with
`s = Σ(p) mod 2k` and `o` odd stacks, and let `p'` be obtained by playing on a set `S` of `k`
nonempty stacks, omitting stack `j`. If `p'` is reduced, then `s' = s + k` for `s < k` and
`s' = s - k` for `s ≥ k`, and `o' = n - o + 1` if stack `j` is odd, `o' = n - o - 1` if it is
even. The record's closing remark that both values of `o'` are legal when `0 < o < n` is
omitted: it fails in `SN(3, 2)` at `p = (0, 1, 1)`, whose only move omits the empty stack.

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

/-- Options with reduction in `SN(n, n - 1)` (`n ≥ 2`, `k = n - 1`). Let `p` be reduced with
`s = Σ(p) mod 2k`, `o` odd stacks, maximum `M` attained by `α` stacks, and let `p'` (a move on
`k` stacks) need reduction. Then `M` is even if `s < k` and odd otherwise, and:
if `s ≢ 0 (mod k)`, `r(p') = p - 1` (every stack lowered by one), `o' = n - o` and
`s' = s + k - 1` for `s < k`, `s' = s - (k + 1)` for `s > k`; if `s ≡ 0 (mod k)`, `r(p')` lowers
the maximal stacks by two and the others by one, and for `s = 0`, `α ≤ min(n - o, n - 2)` and
`(s', o') = (k - 1 - α, n - o - α)`, while for `s = k`, `α ≤ min(o, n - 2)` and
`(s', o') = (2k - 1 - α, n - o + α)`. Stacks are labelled, so the paper's canonical-form display
of `r(p')` is written stackwise.

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

/-- P-positions of the reduced game `SNG̃(n, k)`, `k = n - 1` (`n ≥ 2`). For a reduced position
`p` with `s = Σ(p) mod 2k` and `o` odd stacks, `s` and `o` have the same parity, and `p` is a
P-position of the playable game graph exactly when `(s, o)` lies in
`S₁ = {0 ≤ s < k - 1, o ≤ s}`, `S₂ = {s = n - 2, o ≡ n (mod 2)}` or
`S₃ = {k - 1 < s < 2k - 1, o ≤ 2(k - 1) - s}`; the paper's "same parity" clauses in `S₁` and
`S₃` follow from the first assertion and are not repeated.

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

/-- P-positions of the reduced game `SNG̃(n, {n - 1, n})` (`n ≥ 2`). For a reduced position `p`
with `s = Σ(p) mod (2n - 2)` and `o` odd stacks, `s` and `o` have the same parity, and `p` is a
P-position of the playable game graph exactly when `(s, o)` lies in `S₁ = {s < n - 2, o ≤ s}`,
`S₂ = {s = n - 2, o ≡ n (mod 2), o ≠ n}` or `S₃ = {n - 2 < s < 2n - 3, o ≤ 2(n - 2) - s}`; the
"same parity" clauses of `S₁` and `S₃` follow from the first assertion and are not repeated.

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
