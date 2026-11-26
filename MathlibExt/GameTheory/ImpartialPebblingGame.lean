/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Nat.ModEq
public import MathlibExt.GameTheory.SpragueGrundy
import Mathlib.Tactic.FinCases

/-!
# Impartial two-player `(k+1:k)`-pebbling games on `K_3` and `C_4`

Based on Kayla Barker, Mia DeStefano, Eugene Fiorini, Michael Gohn, Joe Miller,
Jacob Roeder, and Tony W. H. Wong, *Generalized Impartial Two-player Pebbling Games on `K_3`
and `C_4`*, Journal of Integer Sequences 27 (2024), Article 24.5.8.

A legal move removes `k+1` pebbles from one vertex and adds `k` to an adjacent vertex.
The total decreases by one, so it ranks the positions in the normal-play game.
On the triangle we construct a reply that lowers the common bound on the three piles.
On the four-cycle, moves preserve two unions of mod-three patterns, and symmetric replies
preserve each of the five patterns.
-/

namespace MetaMathlibExt

@[expose] public section

open SpragueGrundy

/-- **A $(k+1:k)$-pebbling move.** Let $a = (a_0, \dots, a_{n-1})$ be a distribution of pebbles on
the vertices $0, \dots, n-1$, let $k$ be a natural number and let $i$ and $j$ be vertices. The
position after the $(k+1:k)$-pebbling move from $i$ to $j$ is the distribution $b$ with
$b_j = a_j + k$, $b_i = a_i - (k + 1)$ if $i \ne j$, and $b_x = a_x$ for every other vertex $x$.
When $i \ne j$ and $a_i \ge k + 1$, this removes $k + 1$ pebbles from $i$ and adds $k$ pebbles
to $j$.

Subtraction is truncated at $0$, so $b_i = 0$ when $i \ne j$ and $a_i < k + 1$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (definition of a `(k+1:k)`-pebbling move). -/
public def pebblingStep {n : ℕ} (k : ℕ) (a : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  Function.update (Function.update a i (a i - (k + 1))) j (a j + k)

/-- **A pebbling move removes exactly one pebble.** Let $n, k \in \mathbb{N}$, let $a$ assign
$a(x) \in \mathbb{N}$ pebbles to each vertex $x \in \{0, \dots, n-1\}$, and let $i \ne j$ be
vertices with $a(i) \ge k + 1$. Then the pebbling step from $i$ to $j$, which removes $k + 1$
pebbles from $i$ and adds $k$ pebbles to $j$, gives a position $b$ with
$\sum_x b(x) + 1 = \sum_x a(x)$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (definition of a `(k+1:k)`-pebbling move). -/
public theorem sum_pebblingStep_add_one {n : ℕ} (k : ℕ) (a : Fin n → ℕ) {i j : Fin n}
    (hij : i ≠ j) (hi : k + 1 ≤ a i) :
    ∑ x, pebblingStep k a i j x + 1 = ∑ x, a x := by
  have hj : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have hi' : i ∈ (Finset.univ : Finset (Fin n)).erase j := by simp [hij]
  unfold pebblingStep
  rw [← Finset.add_sum_erase _ _ hj, ← Finset.add_sum_erase _ _ hj,
    ← Finset.add_sum_erase _ _ hi', ← Finset.add_sum_erase _ _ hi']
  have hrest : ∑ x ∈ ((Finset.univ : Finset (Fin n)).erase j).erase i,
      Function.update (Function.update a i (a i - (k + 1))) j (a j + k) x =
      ∑ x ∈ ((Finset.univ : Finset (Fin n)).erase j).erase i, a x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxi : x ≠ i := Finset.ne_of_mem_erase hx
    have hxj : x ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
    simp [Function.update_of_ne hxi, Function.update_of_ne hxj]
  rw [hrest]
  simp only [Function.update_self, Function.update_of_ne hij]
  omega

/-- **Moves of the $(k+1:k)$-pebbling game.** Let $G$ be a simple graph on the vertices
$0, \dots, n-1$, let $k$ be a natural number and let $a = (a_0, \dots, a_{n-1})$ be a distribution
of pebbles on the vertices. This is the finite set of distributions reachable from $a$ by one
$(k+1:k)$-pebbling move on $G$: for adjacent vertices $i$ and $j$ with $a_i \ge k + 1$, remove
$k + 1$ pebbles from $i$ and add $k$ pebbles to $j$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (successors of a game). -/
public def pebblingMoves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (a : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
      fun p => G.Adj p.1 p.2 ∧ k + 1 ≤ a p.1).image fun p => pebblingStep k a p.1 p.2

/-- **Successors of a pebbling position.** Let $G$ be a simple graph on the vertices
$0, \dots, n-1$, let $k$ be a natural number, and let $a$ and $b$ be distributions of pebbles on
the vertices of $G$. Then $b$ is reachable from $a$ by one $(k+1:k)$-pebbling move on $G$ if and
only if there are adjacent vertices $i$ and $j$ of $G$ such that $i$ holds at least $k + 1$
pebbles in $a$ and $b$ is obtained from $a$ by removing $k + 1$ pebbles from $i$ and adding $k$
pebbles to $j$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (successors of a game). -/
public theorem mem_pebblingMoves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (a b : Fin n → ℕ) :
    b ∈ pebblingMoves G k a ↔ ∃ i j, G.Adj i j ∧ k + 1 ≤ a i ∧ pebblingStep k a i j = b := by
  simp [pebblingMoves, and_assoc]

/-- **The $(k+1:k)$-pebbling game.** Let $G$ be a simple graph on the vertices $0, \dots, n-1$ and
let $k$ be a natural number. The impartial two-player $(k+1:k)$-pebbling game
$\Gamma^{(k+1:k)}_G$ has as positions all distributions $a = (a_0, \dots, a_{n-1})$ of pebbles on
the vertices, with $a_i \in \mathbb{N}$. A move from $a$ chooses adjacent vertices $i$ and $j$
with $a_i \ge k + 1$, removes $k + 1$ pebbles from $i$ and adds $k$ pebbles to $j$. The game is
ranked by the total number of pebbles $a_0 + \dots + a_{n-1}$, which every move decreases.

Its designated start position, which is not used, is the empty distribution.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1. -/
public def pebblingGame {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    ImpartialGame where
  Pos := Fin n → ℕ
  eqDec := inferInstance
  moves := pebblingMoves G k
  rank := fun a => ∑ i, a i
  rank_lt := by
    intro a b h
    obtain ⟨i, j, hadj, hi, rfl⟩ := (mem_pebblingMoves G k a b).1 h
    have := sum_pebblingStep_add_one k a hadj.ne hi
    omega
  start := fun _ => 0

/-- **Positions with at most $k$ pebbles on every vertex are P-positions.** Let $G$ be a simple
graph on the vertices $0, \dots, n-1$ and let $k$ be a natural number. In the
$(k+1:k)$-pebbling game on $G$, every position with at most $k$ pebbles on each vertex is a
P-position.

Such a position is terminating: no move is possible from it.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (terminating games are P-games). -/
public theorem pebblingGame_isP_of_forall_le {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) (a : Fin n → ℕ) (ha : ∀ i, a i ≤ k) :
    IsP (pebblingGame G k) a := by
  refine (isP_iff (pebblingGame G k) a).2 fun b hb => ?_
  obtain ⟨i, j, -, hi, -⟩ := (mem_pebblingMoves G k a b).1 hb
  have := ha i
  omega

/-- **Totals at which every pebbling game is an N-game.** Let $G$ be a simple graph on the
vertices $0, \dots, n-1$ and let $k$ be a natural number. In the $(k+1:k)$-pebbling game on $G$,
a move removes $k+1$ pebbles from a vertex and adds $k$ pebbles to an adjacent vertex. This is
the set of natural numbers $m$ such that every position with $m$ pebbles in total (a number of
pebbles on each vertex, summing to $m$) is an N-position, that is, not a P-position.

The paper's $m^{(k+1:k)}(G)$ is the least element of this set when the set is nonempty, and
"$m^{(k+1:k)}(G)$ does not exist" means the set is empty. The paper takes $m$ positive; $0$ never
lies in the set, because the empty position is a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (definition of `m^{(k+1:k)}(G)`). -/
public def pebblingAllNTotals {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Set ℕ :=
  {m | ∀ a : Fin n → ℕ, ∑ i, a i = m → ¬ IsP (pebblingGame G k) a}

/-- **The total zero is never an all-N total.** For every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ and every $k \in \mathbb{N}$, the number $0$ does not belong to the set of
totals $m$ such that every $(k+1:k)$-pebbling game on $G$ with $m$ pebbles is an N-game. Indeed,
the empty position admits no move, so it is a P-game.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (definition of `m^{(k+1:k)}(G)`). -/
public theorem zero_not_mem_pebblingAllNTotals {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) : 0 ∉ pebblingAllNTotals G k := fun h =>
  h (fun _ => 0) (by simp) (pebblingGame_isP_of_forall_le G k _ fun _ => Nat.zero_le k)

/-- **Pebbling on the triangle: a reply that brings every pile below the bound.** Let $k$ be a
positive integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a
move removes $k+1$ pebbles from one vertex and adds $k$ pebbles to another. Let $\ell$ be a
natural number with $\ell \le 2k - 1$, and let $a$ be a position with $6k - 2\ell$ pebbles in
total in which some pile has at least $k + 1$ pebbles and every pile has at most $3k - \ell$
pebbles. Then for every position $b$ reachable from $a$ by one move there is a position $c$
reachable from $b$ by one move in which every pile has at most $3k - \ell - 1$ pebbles.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 7. -/
public theorem pebbling_completeThree_response_lowersMax (k ℓ : ℕ) (hk : 0 < k)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ)
    (hbig : ∃ i, k + 1 ≤ a i) (hmax : ∀ i, a i ≤ 3 * k - ℓ) :
    ∀ b ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) k a,
      ∃ c ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) k b, ∀ i, c i ≤ 3 * k - ℓ - 1 := by
  intro b hb
  obtain ⟨i, j, hadj, hi, hab⟩ := (mem_pebblingMoves _ k a b).1 hb
  have hij := hadj.ne
  -- Name the untouched vertex and express the total using these three piles.
  have third : ∀ i j : Fin 3, i ≠ j → ∃ t, t ≠ i ∧ t ≠ j ∧ Finset.univ = {i, j, t} := by
    decide
  obtain ⟨t, hti, htj, huniv⟩ := third i j hij
  have cover (v : Fin 3) : v = i ∨ v = j ∨ v = t := by
    simpa [huniv] using Finset.mem_univ v
  have total : a i + (a j + a t) = 6 * k - 2 * ℓ := by
    simpa [huniv, hij, hti.symm, htj.symm] using hsum
  have hbi : b i = a i - (k + 1) := by simp [← hab, pebblingStep, hij]
  have hbj : b j = a j + k := by simp [← hab, pebblingStep]
  have hbt : b t = a t := by simp [← hab, pebblingStep, hti, htj]
  have hmi := hmax i
  have hmj := hmax j
  have hmt := hmax t
  -- The first move made room at i to receive k pebbles from either other pile.
  have reply (s : Fin 3) (hsi : s ≠ i) (hs : k + 1 ≤ b s) (hcap : b s ≤ 3 * k - ℓ + k)
      (hrest : ∀ v, v ≠ i → v ≠ s → b v < 3 * k - ℓ) :
      ∃ c ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) k b, ∀ v, c v ≤ 3 * k - ℓ - 1 := by
    refine ⟨pebblingStep k b s i, (mem_pebblingMoves _ _ _ _).2 ⟨s, i, hsi, hs, rfl⟩, ?_⟩
    intro v
    by_cases hvi : v = i
    · subst v
      simp only [pebblingStep, Function.update_self]
      omega
    by_cases hvs : v = s
    · subst v
      simp only [pebblingStep, Function.update_of_ne hvi, Function.update_self]
      omega
    simp only [pebblingStep, Function.update_of_ne hvi, Function.update_of_ne hvs]
    have := hrest v hvi hvs
    omega
  by_cases ht : a t = 3 * k - ℓ
  · -- The untouched pile is at the bound, so take the reply from it.
    apply reply t hti (by omega) (by omega)
    intro v hvi hvt
    obtain rfl : v = j := ((cover v).resolve_left hvi).resolve_right hvt
    omega
  · -- The untouched pile is below the bound, so reverse the first move.
    apply reply j hij.symm (by omega) (by omega)
    intro v hvi hvj
    obtain rfl : v = t := ((cover v).resolve_left hvi).resolve_left hvj
    omega

/-! ### `(2:1)`-pebbling on `C_4` -/

/-- **The set $X_{aaab}$ of $C_4$ positions.** A position $a = (a_0, a_1, a_2, a_3)$ of
natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$ of $C_4$, with indices read
modulo $4$, lies in $X_{aaab}$ when there is an index $i$ such that
$a_i \equiv a_{i+1} \equiv a_{i+2} \pmod 3$ and $a_{i-1} \not\equiv a_i \pmod 3$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `X_{aaab}`). -/
public def C4PatternAAAB (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, a i ≡ a (i + 1) [MOD 3] ∧ a i ≡ a (i + 2) [MOD 3] ∧ ¬ a i ≡ a (i - 1) [MOD 3]

/-- **The set $X_{abab}$ of $C_4$ positions.** A position $a = (a_0, a_1, a_2, a_3)$ of
natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$ of $C_4$ lies in $X_{abab}$
when $a_0 \equiv a_2 \pmod 3$, $a_1 \equiv a_3 \pmod 3$ and $a_0 \not\equiv a_1 \pmod 3$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `X_{abab}`). -/
public def C4PatternABAB (a : Fin 4 → ℕ) : Prop :=
  a 0 ≡ a 2 [MOD 3] ∧ a 1 ≡ a 3 [MOD 3] ∧ ¬ a 0 ≡ a 1 [MOD 3]

/-- **The set $X_{aabc}$ of $C_4$ positions.** A position $a = (a_0, a_1, a_2, a_3)$ of
natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$ of $C_4$, with indices read
modulo $4$, lies in $X_{aabc}$ when there is an index $i$ with $a_i \equiv a_{i+1} \pmod 3$ such
that $a_i$, $a_{i+2}$ and $a_{i-1}$ are pairwise incongruent modulo $3$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `X_{aabc}`). -/
public def C4PatternAABC (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, a i ≡ a (i + 1) [MOD 3] ∧ ¬ a i ≡ a (i + 2) [MOD 3] ∧
    ¬ a i ≡ a (i - 1) [MOD 3] ∧ ¬ a (i + 2) ≡ a (i - 1) [MOD 3]

/-- **The set $X_{abac}$ of $C_4$ positions.** A position $a = (a_0, a_1, a_2, a_3)$ of
natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$ of $C_4$, with indices read
modulo $4$, lies in $X_{abac}$ when there is $i \in \{0, 1\}$ with $a_i \equiv a_{i+2} \pmod 3$
such that $a_i$, $a_{i+1}$ and $a_{i-1}$ are pairwise incongruent modulo $3$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `X_{abac}`). -/
public def C4PatternABAC (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, (i = 0 ∨ i = 1) ∧ a i ≡ a (i + 2) [MOD 3] ∧ ¬ a i ≡ a (i + 1) [MOD 3] ∧
    ¬ a i ≡ a (i - 1) [MOD 3] ∧ ¬ a (i + 1) ≡ a (i - 1) [MOD 3]

/-- **The set $\hat X_{aabb}$ of $C_4$ positions.** A position $a = (a_0, a_1, a_2, a_3)$ of
natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$ of $C_4$, with indices read
modulo $4$, lies in $\hat X_{aabb}$ when there is $i \in \{0, 1\}$ with
$a_i \equiv a_{i+1} \pmod 3$ and $a_{i+2} \equiv a_{i-1} \pmod 3$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `\hat X_{aabb}`). -/
public def C4PatternAABBHat (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, (i = 0 ∨ i = 1) ∧ a i ≡ a (i + 1) [MOD 3] ∧ a (i + 2) ≡ a (i - 1) [MOD 3]

/-- **Invariance of the mod-$3$ pattern classes under symmetric replies on $C_4$.** Consider the
$(2:1)$-pebbling game on the cycle $C_4$ with vertices $v_0, v_1, v_2, v_3$, indices read modulo
$4$, and let $a = (a_0, a_1, a_2, a_3)$ be a position with $a_i$ pebbles on $v_i$. Let $j$ be an
index with $a_j \ge 2$, let $\varepsilon \in \{1, -1\}$, and let $b$ be the position obtained from
$a$ by the move from $v_j$ to $v_{j+\varepsilon}$, which removes two pebbles from $v_j$ and adds
one pebble to $v_{j+\varepsilon}$. Let $c$ be obtained from $b$ either by the move from $v_{j+2}$
to $v_{j-\varepsilon}$, where $b_{j+2} \ge 2$, or by the move from $v_{j-\varepsilon}$ to
$v_{j+2}$, where $b_{j-\varepsilon} \ge 2$. Then for each of the sets $X_{aaab}$, $X_{abab}$,
$X_{aabc}$, $X_{abac}$ and $\hat X_{aabb}$, if $a$ lies in the set, then so does $c$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 14. -/
public theorem c4Pattern_invariant_rotationalSymmetric_reflectional (a : Fin 4 → ℕ)
    (j ε : Fin 4) (hε : ε = 1 ∨ ε = -1) (hj : 2 ≤ a j) (c : Fin 4 → ℕ)
    (hc : (2 ≤ pebblingStep 1 a j (j + ε) (j + 2) ∧
        c = pebblingStep 1 (pebblingStep 1 a j (j + ε)) (j + 2) (j - ε)) ∨
      (2 ≤ pebblingStep 1 a j (j + ε) (j - ε) ∧
        c = pebblingStep 1 (pebblingStep 1 a j (j + ε)) (j - ε) (j + 2))) :
    (C4PatternAAAB a → C4PatternAAAB c) ∧ (C4PatternABAB a → C4PatternABAB c) ∧
      (C4PatternAABC a → C4PatternAABC c) ∧ (C4PatternABAC a → C4PatternABAC c) ∧
      (C4PatternAABBHat a → C4PatternAABBHat c) := by
  -- A legal step adds one modulo three at each endpoint.
  let bump (s t i : Fin 4) : ℕ := if i = s ∨ i = t then 1 else 0
  have step (p : Fin 4 → ℕ) (s t i : Fin 4) (hs : 2 ≤ p s) :
      pebblingStep 1 p s t i ≡ p i + bump s t i [MOD 3] := by
    by_cases ht : i = t
    · subst i
      simp [pebblingStep, bump, Nat.ModEq]
    by_cases hi : i = s
    · subst i
      simp [pebblingStep, bump, ht, Nat.ModEq]
      omega
    simp [pebblingStep, bump, ht, hi, Nat.ModEq]
  -- The opposite edges cover every vertex exactly once in either reply direction.
  have cover : ∀ j ε i : Fin 4, ε = 1 ∨ ε = -1 →
      bump j (j + ε) i + bump (j + 2) (j - ε) i = 1 := by decide
  let b := pebblingStep 1 a j (j + ε)
  have shift (i : Fin 4) : c i ≡ a i + 1 [MOD 3] := by
    have reply (s t : Fin 4) (hs : 2 ≤ b s)
        (hcover : bump j (j + ε) i + bump s t i = 1) :
        pebblingStep 1 b s t i ≡ a i + 1 [MOD 3] := by
      simpa only [Nat.add_assoc, hcover] using
        (step b s t i hs).trans ((step a j (j + ε) i hj).add_right (bump s t i))
    obtain ⟨hs, rfl⟩ | ⟨hs, rfl⟩ := hc
    · exact reply _ _ hs (cover j ε i hε)
    · apply reply _ _ hs
      simpa only [bump, or_comm] using cover j ε i hε
  have pair (i k : Fin 4) : c i ≡ c k [MOD 3] ↔ a i ≡ a k [MOD 3] :=
    ⟨fun h => ((shift i).symm.trans (h.trans (shift k))).add_right_cancel' 1,
      fun h => (shift i).trans ((h.add_right 1).trans (shift k).symm)⟩
  simp only [C4PatternAAAB, C4PatternABAB, C4PatternAABC, C4PatternABAC, C4PatternAABBHat,
    pair, imp_self, and_self]

/-- **Closure of the mod-$3$ pattern classes under moves on $C_4$.** Let $a$ and $b$ be
distributions of pebbles on the vertices of the $4$-cycle $C_4$ such that $b$ is obtained from $a$
by one $(2:1)$-pebbling move, that is, by removing two pebbles from a vertex holding at least two
pebbles and adding one pebble to an adjacent vertex. If $a \in \hat X_{aabb} \cup X_{abac}$, then
$b \in \hat X_{aabb} \cup X_{abac}$; and if $a \in X_{aaab} \cup X_{abab} \cup X_{aabc}$, then
$b \in X_{aaab} \cup X_{abab} \cup X_{aabc}$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 15. -/
public theorem c4Pattern_closed_under_moves (a b : Fin 4 → ℕ)
    (hb : b ∈ pebblingMoves (SimpleGraph.cycleGraph 4) 1 a) :
    ((C4PatternAABBHat a ∨ C4PatternABAC a) → (C4PatternAABBHat b ∨ C4PatternABAC b)) ∧
      ((C4PatternAAAB a ∨ C4PatternABAB a ∨ C4PatternAABC a) →
        (C4PatternAAAB b ∨ C4PatternABAB b ∨ C4PatternAABC b)) := by
  let balanced (p : Fin 4 → ℕ) := p 0 + p 2 ≡ p 1 + p 3 [MOD 3]
  let classes (p : Fin 4 → ℕ) :=
    ((C4PatternAABBHat p ∨ C4PatternABAC p) ↔ balanced p) ∧
      ((C4PatternAAAB p ∨ C4PatternABAB p ∨ C4PatternAABC p) ↔ ¬ balanced p)
  -- Classify the 81 possible residue vectors by the sums on the two opposite pairs.
  have finiteClasses : ∀ r : Fin 4 → Fin 3, classes (fun i => (r i).val) := by
    dsimp only [classes, balanced, C4PatternAABBHat, C4PatternABAC, C4PatternAAAB,
      C4PatternABAB, C4PatternAABC]
    decide
  have classify (p : Fin 4 → ℕ) : classes p := by
    have h := finiteClasses (fun i => Fin.ofNat 3 (p i))
    simpa only [classes, balanced, C4PatternAABBHat, C4PatternABAC, C4PatternAAAB,
      C4PatternABAB, C4PatternAABC, Fin.val_ofNat, Nat.ModEq, Nat.mod_mod, ← Nat.add_mod]
      using h
  -- Each edge meets both pairs, and subtracting two or adding one has the same effect mod 3.
  have preserved : balanced b ↔ balanced a := by
    obtain ⟨s, t, hadj, hs, rfl⟩ := (mem_pebblingMoves _ _ _ _).1 hb
    fin_cases s <;> fin_cases t <;> try exact absurd hadj (by decide)
    all_goals
      simp [balanced, pebblingStep, Function.update, Nat.ModEq] at hs ⊢
      omega
  rw [(classify a).1, (classify b).1, (classify a).2, (classify b).2, preserved]
  exact ⟨id, id⟩

/-- **The set $Y_{aabc}$ of $C_4$ positions.** A position $a = (a_0, a_1, a_2, a_3)$ of
natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$ of $C_4$, with indices read
modulo $4$, lies in $Y_{aabc}$ when there is an index $i$ with $a_{i+2} \equiv a_i + 2 \pmod 4$
and $a_{i+1} \equiv a_{i-1} + 1 \pmod 4$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `Y_{aabc}`). -/
public def C4ModFourAABC (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, a (i + 2) ≡ a i + 2 [MOD 4] ∧ a (i + 1) ≡ a (i - 1) + 1 [MOD 4]

/-- **The set $\hat Y_{abac}$ of $C_4$ positions.** A position $a = (a_0, a_1, a_2, a_3)$ of
natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$ of $C_4$, with indices read
modulo $4$, lies in $\hat Y_{abac}$ when there is an index $i$ with $a_i \equiv a_{i+2} \pmod 4$
and $a_{i+1} \equiv a_{i-1} + 1 \pmod 4$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `\hat Y_{abac}`). -/
public def C4ModFourABACHat (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, a i ≡ a (i + 2) [MOD 4] ∧ a (i + 1) ≡ a (i - 1) + 1 [MOD 4]

/-- **The set $\hat Y_{abab}$ of $C_4$ positions.** A position $a = (a_0, a_1, a_2, a_3)$ of
natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$ of $C_4$ lies in
$\hat Y_{abab}$ when $a_0 \equiv a_2 \pmod 4$ and $a_1 \equiv a_3 \pmod 4$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `\hat Y_{abab}`). -/
public def C4ModFourABABHat (a : Fin 4 → ℕ) : Prop :=
  a 0 ≡ a 2 [MOD 4] ∧ a 1 ≡ a 3 [MOD 4]

/-- **The complement set $(\hat Y_{abab})^c$ of $C_4$ positions.** A position
$a = (a_0, a_1, a_2, a_3)$ of natural-number pebble counts on the vertices $v_0, v_1, v_2, v_3$
of $C_4$ lies in $(\hat Y_{abab})^c$ when its total $a_0 + a_1 + a_2 + a_3$ is even and $a$ does
not lie in $\hat Y_{abab}$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `(\hat Y_{abab})^c`). -/
public def C4ModFourABABHatCompl (a : Fin 4 → ℕ) : Prop :=
  Even (∑ i, a i) ∧ ¬ C4ModFourABABHat a

/-- **Examples of the mod-$3$ pattern classes on $C_4$.** Writing a distribution of pebbles on the
vertices $v_0, v_1, v_2, v_3$ of $C_4$ as $(a_0, a_1, a_2, a_3)$, we have
$(0,0,0,0) \in \hat X_{aabb}$, $(1,0,0,0) \in X_{aaab}$, $(0,1,0,1) \in X_{abab}$,
$(0,0,1,2) \in X_{aabc}$, $(0,1,0,2) \in X_{abac}$, and $(0,0,0,0) \notin X_{aaab}$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definitions of the sets `X`). -/
public theorem c4Pattern_examples :
    C4PatternAABBHat ![0, 0, 0, 0] ∧ C4PatternAAAB ![1, 0, 0, 0] ∧
      C4PatternABAB ![0, 1, 0, 1] ∧ C4PatternAABC ![0, 0, 1, 2] ∧
      C4PatternABAC ![0, 1, 0, 2] ∧ ¬ C4PatternAAAB ![0, 0, 0, 0] := by
  unfold C4PatternAABBHat C4PatternAAAB C4PatternABAB C4PatternAABC C4PatternABAC
  decide

/-- **Examples of positions in the sets $Y$ for $C_4$.** Writing $(a_0, a_1, a_2, a_3)$ for the
position with $a_j$ pebbles on vertex $v_j$ of $C_4$: the position $(2, 0, 0, 1)$ lies in
$Y_{aabc}$, the position $(0, 1, 0, 0)$ lies in $\hat Y_{abac}$, the position $(0, 0, 0, 0)$ lies
in $\hat Y_{abab}$, and the position $(1, 1, 0, 0)$ lies in $(\hat Y_{abab})^c$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definitions of the sets `Y`). -/
public theorem c4ModFour_examples :
    C4ModFourAABC ![2, 0, 0, 1] ∧ C4ModFourABACHat ![0, 1, 0, 0] ∧
      C4ModFourABABHat ![0, 0, 0, 0] ∧ C4ModFourABABHatCompl ![1, 1, 0, 0] := by
  unfold C4ModFourAABC C4ModFourABACHat C4ModFourABABHatCompl C4ModFourABABHat
  decide

end

end MetaMathlibExt
