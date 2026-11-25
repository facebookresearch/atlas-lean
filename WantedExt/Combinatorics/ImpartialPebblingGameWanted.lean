/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.GameTheory.ImpartialPebblingGame
public import MathlibExt.GameTheory.PebblingCompleteThree
public import MathlibExt.GameTheory.PebblingCompleteTwo

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

/-! ### Theorem 1 (Fiorini, Lind, Woldar, and Wong), quoted -/

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
