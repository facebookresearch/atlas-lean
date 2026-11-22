/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.GameTheory.SpragueGrundy

/-!
# Impartial two-player `(k+1:k)`-pebbling games on `K_3` and `C_4`

Statements from Kayla Barker, Mia DeStefano, Eugene Fiorini, Michael Gohn, Joe Miller,
Jacob Roeder, and Tony W. H. Wong, *Generalized Impartial Two-player Pebbling Games on `K_3`
and `C_4`*, Journal of Integer Sequences 27 (2024), Article 24.5.8.

A position on a simple graph `G` on `Fin n` is a pebble count `a : Fin n → ℕ`. A
`(k+1:k)`-pebbling move removes `k+1` pebbles from a vertex and adds `k` pebbles to an
adjacent vertex; the last player to move wins (normal play). P-games are the existing
`MetaMathlibExt.SpragueGrundy.IsP` of `pebblingGame G k`. The complete graph `K_n` is
`(⊤ : SimpleGraph (Fin n))`; the cycle `C_4` is Mathlib's `SimpleGraph.cycleGraph 4`, whose
vertex `v_i` is adjacent to `v_{i ± 1}` with indices in `Fin 4` (addition mod `4`, as in the
paper). The paper's equivalence class `Γ{a₁,a₂,a₃}` of `K_3` games is written as the
positions `![a₁, a₂, a₃] ∘ σ` for permutations `σ` of `Fin 3`.
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

/-! ### Theorem 1 (Fiorini, Lind, Woldar, and Wong), quoted -/

/-- **Winning positions of $(2:1)$-pebbling on $K_2$.** Let $a = (a_0, a_1)$ be a position of the
$(2:1)$-pebbling game on the complete graph $K_2$, with $a_0$ and $a_1$ pebbles on its two
vertices. If $a_0 + a_1$ is even, then $a$ is an N-position (that is, not a P-position) if and
only if $a_0 \not\equiv a_1 \pmod 3$. If $a_0 + a_1$ is odd, then $a$ is an N-position if and
only if $a_0 \equiv a_1 \pmod 3$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(a), quoting E. Fiorini, M. Lind, A. Woldar, and T. W. H. Wong,
J. Integer Sequences 24 (2021), Article 21.6.4. -/
public theorem_wanted pebbling_completeTwo_isN_iff (a : Fin 2 → ℕ) :
    (Even (a 0 + a 1) →
      (¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) a ↔ ¬ a 0 ≡ a 1 [MOD 3])) ∧
    (Odd (a 0 + a 1) →
      (¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) a ↔ a 0 ≡ a 1 [MOD 3]))

/-- **No all-N threshold for $(2:1)$-pebbling on $K_2$.** For every natural number $m$, some
$(2:1)$-pebbling game on the complete graph $K_2$ with $m$ pebbles in total is a P-game; that is,
$m^{(2:1)}(K_2)$, the least total at which every game is an N-game, does not exist.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(a), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted pebblingAllNTotals_completeTwo_eq_empty :
    pebblingAllNTotals (⊤ : SimpleGraph (Fin 2)) 1 = ∅

/-- **All-N threshold of $(2:1)$-pebbling on $K_3$.** The least number $m$ such that every
$(2:1)$-pebbling game on the complete graph $K_3$ with $m$ pebbles in total is an N-game, written
$m^{(2:1)}(K_3)$, exists and equals $7$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(b), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted isLeast_pebblingAllNTotals_completeThree_one :
    IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin 3)) 1) 7

/-- **All-N threshold of $(2:1)$-pebbling on $K_4$.** The least number $m$ such that every
$(2:1)$-pebbling game on the complete graph $K_4$ with $m$ pebbles in total is an N-game, written
$m^{(2:1)}(K_4)$, exists and equals $23$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(c), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted isLeast_pebblingAllNTotals_completeFour_one :
    IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin 4)) 1) 23

/-- **All-N threshold of $(2:1)$-pebbling on $K_n$ for odd $n$.** For every odd $n \ge 5$, the
least number $m$ such that every $(2:1)$-pebbling game on the complete graph $K_n$ with $m$
pebbles in total is an N-game, written $m^{(2:1)}(K_n)$, exists and equals $n + 2$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(d), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted isLeast_pebblingAllNTotals_complete_odd (n : ℕ) (hn : 5 ≤ n)
    (hodd : Odd n) : IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin n)) 1) (n + 2)

/-- **All-N threshold of $(2:1)$-pebbling on $K_n$ for even $n$.** For every even $n \ge 6$, the
least number $m$ such that every $(2:1)$-pebbling game on the complete graph $K_n$ with $m$
pebbles in total is an N-game, written $m^{(2:1)}(K_n)$, exists and equals $n + 7$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(e), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted isLeast_pebblingAllNTotals_complete_even (n : ℕ) (hn : 6 ≤ n)
    (heven : Even n) : IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin n)) 1) (n + 7)

/-! ### `(k+1:k)`-pebbling on `K_3` -/

/-- **All-N threshold of $(k+1:k)$-pebbling on $K_3$.** For every positive integer $k$, the least
number $m$ such that every $(k+1:k)$-pebbling game on the complete graph $K_3$ with $m$ pebbles in
total is an N-game, written $m^{(k+1:k)}(K_3)$, exists and equals $6k + 1$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 2. -/
public theorem_wanted isLeast_pebblingAllNTotals_completeThree (k : ℕ) (hk : 0 < k) :
    IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin 3)) k) (6 * k + 1)

/-- **Pebbling on the triangle: a single pile of 2k+3 pebbles is a P-position.** Let $k$ be a
positive integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a
move removes $k+1$ pebbles from one vertex and adds $k$ pebbles to another. Every position with
$2k + 3$ pebbles on one vertex and none on the other two is a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 4. -/
public theorem_wanted pebbling_completeThree_isP_twoKAddThree (k : ℕ) (hk : 0 < k)
    (σ : Equiv.Perm (Fin 3)) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) (![2 * k + 3, 0, 0] ∘ σ)

/-- **Pebbling on the triangle: a two-parameter family of P-positions.** Let $k$ be a positive
integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a move removes
$k+1$ pebbles from one vertex and adds $k$ pebbles to another. Let $\ell_1 \le \ell_2$ be
natural numbers with $\ell_1 + \ell_2 \le k - 1$. Every position whose three piles are
$2k - 1 - \ell_1 - \ell_2$, $k - \ell_1$ and $k - \ell_2$ in some order is a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 5. -/
public theorem_wanted pebbling_completeThree_isP_twoKSubOne (k ℓ₁ ℓ₂ : ℕ) (hk : 0 < k)
    (hℓ : ℓ₁ + ℓ₂ ≤ k - 1) (h₁₂ : ℓ₁ ≤ ℓ₂) (σ : Equiv.Perm (Fin 3)) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k)
      (![2 * k - 1 - (ℓ₁ + ℓ₂), k - ℓ₁, k - ℓ₂] ∘ σ)

/-- **Pebbling on the triangle: piles 4k+1, k-1, k-1 form a P-position.** Let $k$ be a positive
integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a move removes
$k+1$ pebbles from one vertex and adds $k$ pebbles to another. Every position whose three piles
are $4k + 1$, $k - 1$ and $k - 1$ in some order is a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 6. -/
public theorem_wanted pebbling_completeThree_isP_fourKAddOne (k : ℕ) (hk : 0 < k)
    (σ : Equiv.Perm (Fin 3)) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) (![4 * k + 1, k - 1, k - 1] ∘ σ)

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
public theorem_wanted pebbling_completeThree_response_lowersMax (k ℓ : ℕ) (hk : 0 < k)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ)
    (hbig : ∃ i, k + 1 ≤ a i) (hmax : ∀ i, a i ≤ 3 * k - ℓ) :
    ∀ b ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) k a,
      ∃ c ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) k b, ∀ i, c i ≤ 3 * k - ℓ - 1

/-- **Pebbling on the triangle: total 6k-2ℓ with no pile above half is a P-position.** Let $k$ be
a positive integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a
move removes $k+1$ pebbles from one vertex and adds $k$ pebbles to another. Let $\ell$ be a
natural number with $\ell \le 2k - 1$. Every position with $6k - 2\ell$ pebbles in total in which
every pile is at most $3k - \ell$ is a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 8. -/
public theorem_wanted pebbling_completeThree_isP_of_le (k ℓ : ℕ) (hk : 0 < k)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ)
    (hmax : ∀ i, a i ≤ 3 * k - ℓ) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a

/-- **Pebbling on the triangle: N-positions with total 6k-2ℓ+1 and a small pile.** Let $k$ be a
positive integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a
move removes $k+1$ pebbles from one vertex and adds $k$ pebbles to another. Let $\ell$ be an
integer with $1 \le \ell \le 2k - 1$. Every position with $6k - 2\ell + 1$ pebbles in total in
which every pile is at most $4k - \ell + 1$ and some pile is at most $2k - \ell$ is an
N-position, that is, not a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 9. -/
public theorem_wanted pebbling_completeThree_isN_of_le (k ℓ : ℕ) (hk : 0 < k) (hℓ₁ : 1 ≤ ℓ)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ + 1)
    (hmax : ∀ i, a i ≤ 4 * k - ℓ + 1) (hmin : ∃ i, a i ≤ 2 * k - ℓ) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a

/-- **Pebbling on the triangle: total 6k-1 with every pile at most 4k.** Let $k$ be a positive
integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a move removes
$k+1$ pebbles from one vertex and adds $k$ pebbles to another. Every position with $6k - 1$
pebbles in total in which every pile is at most $4k$ is an N-position, that is, not a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Corollary 10. -/
public theorem_wanted pebbling_completeThree_isN_of_le_fourK (k : ℕ) (hk : 0 < k)
    (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 1) (hmax : ∀ i, a i ≤ 4 * k) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a

/-- **Pebbling on the triangle: N-positions with an empty vertex.** Let $k$ be a natural number
and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a move removes $k+1$
pebbles from one vertex and adds $k$ pebbles to another. Let $\ell$ be an integer with
$1 \le \ell \le k - 1$, and let $a_1, a_2$ be natural numbers with $a_1 + a_2 = 6k - 2\ell + 1$
and $a_2 \le k$. Every position whose three piles are $a_1$, $a_2$ and $0$ in some order is an
N-position, that is, not a P-position.

The paper's ordering $a_1 \ge a_2$ follows from these hypotheses.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 11. -/
public theorem_wanted pebbling_completeThree_isN_of_zero (k ℓ a₁ a₂ : ℕ) (hℓ₁ : 1 ≤ ℓ)
    (hℓ : ℓ + 1 ≤ k) (hsum : a₁ + a₂ = 6 * k - 2 * ℓ + 1) (ha₂ : a₂ ≤ k)
    (σ : Equiv.Perm (Fin 3)) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) (![a₁, a₂, 0] ∘ σ)

/-- **Pebbling on the triangle: total 6k-1 with a pile of at least 4k+1.** Let $k$ be a positive
integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a move removes
$k+1$ pebbles from one vertex and adds $k$ pebbles to another. Every position with $6k - 1$
pebbles in total in which some pile is at least $4k + 1$, other than the positions whose three
piles are $4k + 1$, $k - 1$ and $k - 1$ in some order, is an N-position, that is, not a
P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 12. -/
public theorem_wanted pebbling_completeThree_isN_of_ge_fourKAddOne (k : ℕ) (hk : 0 < k)
    (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 1) (hbig : ∃ i, 4 * k + 1 ≤ a i)
    (hne : ∀ σ : Equiv.Perm (Fin 3), a ≠ ![4 * k + 1, k - 1, k - 1] ∘ σ) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a

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
public theorem_wanted c4Pattern_invariant_rotationalSymmetric_reflectional (a : Fin 4 → ℕ)
    (j ε : Fin 4) (hε : ε = 1 ∨ ε = -1) (hj : 2 ≤ a j) (c : Fin 4 → ℕ)
    (hc : (2 ≤ pebblingStep 1 a j (j + ε) (j + 2) ∧
        c = pebblingStep 1 (pebblingStep 1 a j (j + ε)) (j + 2) (j - ε)) ∨
      (2 ≤ pebblingStep 1 a j (j + ε) (j - ε) ∧
        c = pebblingStep 1 (pebblingStep 1 a j (j + ε)) (j - ε) (j + 2))) :
    (C4PatternAAAB a → C4PatternAAAB c) ∧ (C4PatternABAB a → C4PatternABAB c) ∧
      (C4PatternAABC a → C4PatternAABC c) ∧ (C4PatternABAC a → C4PatternABAC c) ∧
      (C4PatternAABBHat a → C4PatternAABBHat c)

/-- **Closure of the mod-$3$ pattern classes under moves on $C_4$.** Let $a$ and $b$ be
distributions of pebbles on the vertices of the $4$-cycle $C_4$ such that $b$ is obtained from $a$
by one $(2:1)$-pebbling move, that is, by removing two pebbles from a vertex holding at least two
pebbles and adding one pebble to an adjacent vertex. If $a \in \hat X_{aabb} \cup X_{abac}$, then
$b \in \hat X_{aabb} \cup X_{abac}$; and if $a \in X_{aaab} \cup X_{abab} \cup X_{aabc}$, then
$b \in X_{aaab} \cup X_{abab} \cup X_{aabc}$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 15. -/
public theorem_wanted c4Pattern_closed_under_moves (a b : Fin 4 → ℕ)
    (hb : b ∈ pebblingMoves (SimpleGraph.cycleGraph 4) 1 a) :
    ((C4PatternAABBHat a ∨ C4PatternABAC a) → (C4PatternAABBHat b ∨ C4PatternABAC b)) ∧
      ((C4PatternAAAB a ∨ C4PatternABAB a ∨ C4PatternAABC a) →
        (C4PatternAAAB b ∨ C4PatternABAB b ∨ C4PatternAABC b))

/-- **Parity decides $(2:1)$-pebbling on $C_4$ in $\hat X_{aabb} \cup X_{abac}$.** Consider the
$(2:1)$-pebbling game on the cycle $C_4$ with vertices $v_0, v_1, v_2, v_3$, where $v_i$ is
adjacent to $v_{i \pm 1}$ (indices mod $4$), and let $a = (a_0, a_1, a_2, a_3)$ be a position
with $a_i$ pebbles on $v_i$. Suppose that $a$ lies in $\hat X_{aabb} \cup X_{abac}$, where
$\hat X_{aabb}$ means that for some $i \in \{0, 1\}$, $a_i \equiv a_{i+1}$ and
$a_{i+2} \equiv a_{i-1} \pmod 3$, and $X_{abac}$ means that for some $i \in \{0, 1\}$,
$a_i \equiv a_{i+2} \pmod 3$ and $a_i$, $a_{i+1}$, $a_{i-1}$ are pairwise incongruent mod $3$.
Then $a$ is a P-position if and only if $a_0 + a_1 + a_2 + a_3$ is even.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 16. -/
public theorem_wanted pebbling_cycleFour_isP_iff_even (a : Fin 4 → ℕ)
    (ha : C4PatternAABBHat a ∨ C4PatternABAC a) :
    IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a ↔ Even (∑ i, a i)

/-- **Positions in $\hat Y_{abab}$ are P-positions of $(2:1)$-pebbling on $C_4$.** Consider the
$(2:1)$-pebbling game on the cycle $C_4$ with vertices $v_0, v_1, v_2, v_3$, where $v_i$ is
adjacent to $v_{i \pm 1}$ (indices mod $4$). Every position $a = (a_0, a_1, a_2, a_3)$, with
$a_i$ pebbles on $v_i$, that lies in $\hat Y_{abab}$, that is, with $a_0 \equiv a_2$ and
$a_1 \equiv a_3 \pmod 4$, is a P-position.

The paper's sets range over positive totals; this statement also covers the empty position,
which lies in $\hat Y_{abab}$ and is a P-position because no move is possible from it.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 17. -/
public theorem_wanted pebbling_cycleFour_isP_of_modFourABABHat (a : Fin 4 → ℕ)
    (ha : C4ModFourABABHat a) : IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a

/-- **Positions in $(X_{abab} \cup X_{aabc} \cup X_{aaab}) \cap \hat Y_{abac}$ are P-positions
of $(2:1)$-pebbling on $C_4$.** Consider the
$(2:1)$-pebbling game on the cycle $C_4$ with vertices $v_0, v_1, v_2, v_3$, where $v_i$ is
adjacent to $v_{i \pm 1}$ (indices mod $4$), and let $a = (a_0, a_1, a_2, a_3)$ be a position
with $a_i$ pebbles on $v_i$. Suppose that $a$ lies in $X_{abab} \cup X_{aabc} \cup X_{aaab}$,
where $X_{abab}$ means $a_0 \equiv a_2$, $a_1 \equiv a_3$ and $a_0 \not\equiv a_1 \pmod 3$;
$X_{aabc}$ means that for some $i$, $a_i \equiv a_{i+1} \pmod 3$ and $a_i$, $a_{i+2}$, $a_{i-1}$
are pairwise incongruent mod $3$; and $X_{aaab}$ means that for some $i$,
$a_i \equiv a_{i+1} \equiv a_{i+2} \not\equiv a_{i-1} \pmod 3$. Suppose also that $a$ lies in
$\hat Y_{abac}$: for some $i$, $a_i \equiv a_{i+2}$ and $a_{i+1} \equiv a_{i-1} + 1 \pmod 4$.
Then $a$ is a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 18. -/
public theorem_wanted pebbling_cycleFour_isP_of_modFourABACHat (a : Fin 4 → ℕ)
    (hX : C4PatternABAB a ∨ C4PatternAABC a ∨ C4PatternAAAB a) (hY : C4ModFourABACHat a) :
    IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a

/-- **Positions in $Y_{aabc}$ are N-positions of $(2:1)$-pebbling on $C_4$.** Consider the
$(2:1)$-pebbling game on the cycle $C_4$ with vertices $v_0, v_1, v_2, v_3$, where $v_i$ is
adjacent to $v_{i \pm 1}$ (indices mod $4$). Let $a = (a_0, a_1, a_2, a_3)$ be a position, with
$a_i$ pebbles on $v_i$, that lies in $Y_{aabc}$: for some $i$, $a_{i+2} \equiv a_i + 2$ and
$a_{i+1} \equiv a_{i-1} + 1 \pmod 4$. Then $a$ is an N-position, that is, not a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 19. -/
public theorem_wanted pebbling_cycleFour_isN_of_modFourAABC (a : Fin 4 → ℕ)
    (ha : C4ModFourAABC a) : ¬ IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a

/-- **Positions in $(X_{abab} \cup X_{aabc} \cup X_{aaab}) \cap (\hat Y_{abab})^c$ are
N-positions of $(2:1)$-pebbling on $C_4$.** Consider the
$(2:1)$-pebbling game on the cycle $C_4$ with vertices $v_0, v_1, v_2, v_3$, where $v_i$ is
adjacent to $v_{i \pm 1}$ (indices mod $4$), and let $a = (a_0, a_1, a_2, a_3)$ be a position
with $a_i$ pebbles on $v_i$. Suppose that $a$ lies in $X_{abab} \cup X_{aabc} \cup X_{aaab}$,
where $X_{abab}$ means $a_0 \equiv a_2$, $a_1 \equiv a_3$ and $a_0 \not\equiv a_1 \pmod 3$;
$X_{aabc}$ means that for some $i$, $a_i \equiv a_{i+1} \pmod 3$ and $a_i$, $a_{i+2}$, $a_{i-1}$
are pairwise incongruent mod $3$; and $X_{aaab}$ means that for some $i$,
$a_i \equiv a_{i+1} \equiv a_{i+2} \not\equiv a_{i-1} \pmod 3$. Suppose also that $a$ lies in
$(\hat Y_{abab})^c$: the total $a_0 + a_1 + a_2 + a_3$ is even, and it is not the case that both
$a_0 \equiv a_2$ and $a_1 \equiv a_3 \pmod 4$. Then $a$ is an N-position, that is, not a
P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 20. -/
public theorem_wanted pebbling_cycleFour_isN_of_modFourABABHatCompl (a : Fin 4 → ℕ)
    (hX : C4PatternABAB a ∨ C4PatternAABC a ∨ C4PatternAAAB a)
    (hY : C4ModFourABABHatCompl a) : ¬ IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a

end

end MetaMathlibExt
