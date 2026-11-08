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

/-- The position after a `(k+1:k)`-pebbling move from vertex `i` to vertex `j`: `k+1`
pebbles are removed from `i` and `k` pebbles are added to `j`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (definition of a `(k+1:k)`-pebbling move). -/
public def pebblingStep {n : ℕ} (k : ℕ) (a : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  Function.update (Function.update a i (a i - (k + 1))) j (a j + k)

/-- A legal `(k+1:k)`-pebbling move (`i ≠ j`, `k + 1 ≤ a i`) lowers the total number of
pebbles by exactly one.

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

/-- The finite set of positions reachable from `a` by one `(k+1:k)`-pebbling move on `G`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (successors of a game). -/
public def pebblingMoves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (a : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
      fun p => G.Adj p.1 p.2 ∧ k + 1 ≤ a p.1).image fun p => pebblingStep k a p.1 p.2

/-- Membership in `pebblingMoves`: `b` is a successor of `a` iff it arises from a pebbling
move along an edge from a vertex holding at least `k + 1` pebbles.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (successors of a game). -/
public theorem mem_pebblingMoves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (a b : Fin n → ℕ) :
    b ∈ pebblingMoves G k a ↔ ∃ i j, G.Adj i j ∧ k + 1 ≤ a i ∧ pebblingStep k a i j = b := by
  simp [pebblingMoves, and_assoc]

/-- The impartial two-player `(k+1:k)`-pebbling game `Γ^{(k+1:k)}_G` as an
`ImpartialGame`, ranked by the total number of pebbles (the `start` field is unused and set
to the empty position).

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

/-- A position with at most `k` pebbles on every vertex is terminating, hence a P-game.

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

/-- The set of totals `m` for which every `(k+1:k)`-pebbling game on `G` with `m` pebbles is
an N-game; the paper's `m^{(k+1:k)}(G)` is its least element when the set is nonempty, and
"`m^{(k+1:k)}(G)` does not exist" means the set is empty. The paper takes `m` positive;
`0` never lies in the set (`zero_not_mem_pebblingAllNTotals`).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (definition of `m^{(k+1:k)}(G)`). -/
public def pebblingAllNTotals {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Set ℕ :=
  {m | ∀ a : Fin n → ℕ, ∑ i, a i = m → ¬ IsP (pebblingGame G k) a}

/-- The empty position is a P-game, so `0` is never a total at which every game is an
N-game.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 1 (definition of `m^{(k+1:k)}(G)`). -/
public theorem zero_not_mem_pebblingAllNTotals {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) : 0 ∉ pebblingAllNTotals G k := fun h =>
  h (fun _ => 0) (by simp) (pebblingGame_isP_of_forall_le G k _ fun _ => Nat.zero_le k)

/-! ### Theorem 1 (Fiorini, Lind, Woldar, and Wong), quoted -/

/-- Theorem 1(a) (quoting Fiorini, Lind, Woldar, and Wong): on `K_2` with `(2:1)`-moves, a game
`Γ(a₁, a₂)` with an even total is an N-game iff `a₁ ≢ a₂ (mod 3)`, and with an odd total iff
`a₁ ≡ a₂ (mod 3)`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(a), quoting E. Fiorini, M. Lind, A. Woldar, and T. W. H. Wong,
J. Integer Sequences 24 (2021), Article 21.6.4. -/
public theorem_wanted pebbling_completeTwo_isN_iff (a : Fin 2 → ℕ) :
    (Even (a 0 + a 1) →
      (¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) a ↔ ¬ a 0 ≡ a 1 [MOD 3])) ∧
    (Odd (a 0 + a 1) →
      (¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) a ↔ a 0 ≡ a 1 [MOD 3]))

/-- Theorem 1(a), last sentence: `m^{(2:1)}(K_2)` does not exist.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(a), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted pebblingAllNTotals_completeTwo_eq_empty :
    pebblingAllNTotals (⊤ : SimpleGraph (Fin 2)) 1 = ∅

/-- Theorem 1(b): `m^{(2:1)}(K_3) = 7`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(b), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted isLeast_pebblingAllNTotals_completeThree_one :
    IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin 3)) 1) 7

/-- Theorem 1(c): `m^{(2:1)}(K_4) = 23`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(c), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted isLeast_pebblingAllNTotals_completeFour_one :
    IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin 4)) 1) 23

/-- Theorem 1(d): for odd `n ≥ 5`, `m^{(2:1)}(K_n) = n + 2`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(d), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted isLeast_pebblingAllNTotals_complete_odd (n : ℕ) (hn : 5 ≤ n)
    (hodd : Odd n) : IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin n)) 1) (n + 2)

/-- Theorem 1(e): for even `n ≥ 6`, `m^{(2:1)}(K_n) = n + 7`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(e), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem_wanted isLeast_pebblingAllNTotals_complete_even (n : ℕ) (hn : 6 ≤ n)
    (heven : Even n) : IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin n)) 1) (n + 7)

/-! ### `(k+1:k)`-pebbling on `K_3` -/

/-- Theorem 2: for every positive integer `k`, `m^{(k+1:k)}(K_3) = 6k + 1`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 2. -/
public theorem_wanted isLeast_pebblingAllNTotals_completeThree (k : ℕ) (hk : 0 < k) :
    IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin 3)) k) (6 * k + 1)

/-- Lemma 4: every game in `Γ{2k+3, 0, 0}` on `K_3` is a P-game (`k` positive).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 4. -/
public theorem_wanted pebbling_completeThree_isP_twoKAddThree (k : ℕ) (hk : 0 < k)
    (σ : Equiv.Perm (Fin 3)) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) (![2 * k + 3, 0, 0] ∘ σ)

/-- Lemma 5: for `0 ≤ ℓ ≤ k - 1` and `ℓ₁ ≤ ℓ₂` with `ℓ₁ + ℓ₂ = ℓ`, every game in
`Γ{2k-1-ℓ, k-ℓ₁, k-ℓ₂}` on `K_3` is a P-game (`k` positive).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 5. -/
public theorem_wanted pebbling_completeThree_isP_twoKSubOne (k ℓ₁ ℓ₂ : ℕ) (hk : 0 < k)
    (hℓ : ℓ₁ + ℓ₂ ≤ k - 1) (h₁₂ : ℓ₁ ≤ ℓ₂) (σ : Equiv.Perm (Fin 3)) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k)
      (![2 * k - 1 - (ℓ₁ + ℓ₂), k - ℓ₁, k - ℓ₂] ∘ σ)

/-- Lemma 6: every game in `Γ{4k+1, k-1, k-1}` on `K_3` is a P-game (`k` positive).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 6. -/
public theorem_wanted pebbling_completeThree_isP_fourKAddOne (k : ℕ) (hk : 0 < k)
    (σ : Equiv.Perm (Fin 3)) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) (![4 * k + 1, k - 1, k - 1] ∘ σ)

/-- Lemma 7: let `0 ≤ ℓ ≤ 2k - 1` and let a `K_3` game have `6k - 2ℓ` pebbles with largest pile
`a₁` satisfying `k + 1 ≤ a₁ ≤ 3k - ℓ`. Then after any move by player `A`, player `B` has a
move to a game whose largest pile is at most `3k - ℓ - 1` (`k` positive).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 7. -/
public theorem_wanted pebbling_completeThree_response_lowersMax (k ℓ : ℕ) (hk : 0 < k)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ)
    (hbig : ∃ i, k + 1 ≤ a i) (hmax : ∀ i, a i ≤ 3 * k - ℓ) :
    ∀ b ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) k a,
      ∃ c ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) k b, ∀ i, c i ≤ 3 * k - ℓ - 1

/-- Lemma 8: for `0 ≤ ℓ ≤ 2k - 1`, a `K_3` game with `6k - 2ℓ` pebbles and every pile at most
`3k - ℓ` is a P-game (`k` positive).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 8. -/
public theorem_wanted pebbling_completeThree_isP_of_le (k ℓ : ℕ) (hk : 0 < k)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ)
    (hmax : ∀ i, a i ≤ 3 * k - ℓ) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a

/-- Lemma 9: for `1 ≤ ℓ ≤ 2k - 1`, a `K_3` game with `6k - 2ℓ + 1` pebbles, largest pile at
most `4k - ℓ + 1` and smallest pile at most `2k - ℓ` is an N-game (`k` positive).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 9. -/
public theorem_wanted pebbling_completeThree_isN_of_le (k ℓ : ℕ) (hk : 0 < k) (hℓ₁ : 1 ≤ ℓ)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ + 1)
    (hmax : ∀ i, a i ≤ 4 * k - ℓ + 1) (hmin : ∃ i, a i ≤ 2 * k - ℓ) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a

/-- Corollary 10: a `K_3` game with `6k - 1` pebbles and every pile at most `4k` is an
N-game (`k` positive).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Corollary 10. -/
public theorem_wanted pebbling_completeThree_isN_of_le_fourK (k : ℕ) (hk : 0 < k)
    (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 1) (hmax : ∀ i, a i ≤ 4 * k) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a

/-- Lemma 11: for `1 ≤ ℓ ≤ k - 1`, every game in `Γ{a₁, a₂, 0}` on `K_3` with
`a₁ + a₂ = 6k - 2ℓ + 1` and `a₂ ≤ k` is an N-game (the paper's ordering `a₁ ≥ a₂` follows from
these hypotheses).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 11. -/
public theorem_wanted pebbling_completeThree_isN_of_zero (k ℓ a₁ a₂ : ℕ) (hℓ₁ : 1 ≤ ℓ)
    (hℓ : ℓ + 1 ≤ k) (hsum : a₁ + a₂ = 6 * k - 2 * ℓ + 1) (ha₂ : a₂ ≤ k)
    (σ : Equiv.Perm (Fin 3)) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) (![a₁, a₂, 0] ∘ σ)

/-- Lemma 12: a `K_3` game with `6k - 1` pebbles and a pile of at least `4k + 1` pebbles that
is not in `Γ{4k+1, k-1, k-1}` is an N-game (`k` positive).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 12. -/
public theorem_wanted pebbling_completeThree_isN_of_ge_fourKAddOne (k : ℕ) (hk : 0 < k)
    (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 1) (hbig : ∃ i, 4 * k + 1 ≤ a i)
    (hne : ∀ σ : Equiv.Perm (Fin 3), a ≠ ![4 * k + 1, k - 1, k - 1] ∘ σ) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a

/-! ### `(2:1)`-pebbling on `C_4` -/

/-- `X_{aaab}`: some three cyclically consecutive piles `a_i, a_{i+1}, a_{i+2}` are congruent
mod `3` and the fourth pile `a_{i-1}` is not.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `X_{aaab}`). -/
public def C4PatternAAAB (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, a i ≡ a (i + 1) [MOD 3] ∧ a i ≡ a (i + 2) [MOD 3] ∧ ¬ a i ≡ a (i - 1) [MOD 3]

/-- `X_{abab}`: `a₀ ≡ a₂` and `a₁ ≡ a₃ (mod 3)` with the two residues different.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `X_{abab}`). -/
public def C4PatternABAB (a : Fin 4 → ℕ) : Prop :=
  a 0 ≡ a 2 [MOD 3] ∧ a 1 ≡ a 3 [MOD 3] ∧ ¬ a 0 ≡ a 1 [MOD 3]

/-- `X_{aabc}`: for some `i`, `a_i ≡ a_{i+1} (mod 3)` and `a_i, a_{i+2}, a_{i-1}` are pairwise
distinct mod `3`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `X_{aabc}`). -/
public def C4PatternAABC (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, a i ≡ a (i + 1) [MOD 3] ∧ ¬ a i ≡ a (i + 2) [MOD 3] ∧
    ¬ a i ≡ a (i - 1) [MOD 3] ∧ ¬ a (i + 2) ≡ a (i - 1) [MOD 3]

/-- `X_{abac}`: for some `i ∈ {0, 1}`, `a_i ≡ a_{i+2} (mod 3)` and `a_i, a_{i+1}, a_{i-1}` are
pairwise distinct mod `3`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `X_{abac}`). -/
public def C4PatternABAC (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, (i = 0 ∨ i = 1) ∧ a i ≡ a (i + 2) [MOD 3] ∧ ¬ a i ≡ a (i + 1) [MOD 3] ∧
    ¬ a i ≡ a (i - 1) [MOD 3] ∧ ¬ a (i + 1) ≡ a (i - 1) [MOD 3]

/-- `\hat X_{aabb}`: for some `i ∈ {0, 1}`, `a_i ≡ a_{i+1}` and `a_{i+2} ≡ a_{i-1} (mod 3)`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `\hat X_{aabb}`). -/
public def C4PatternAABBHat (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, (i = 0 ∨ i = 1) ∧ a i ≡ a (i + 1) [MOD 3] ∧ a (i + 2) ≡ a (i - 1) [MOD 3]

/-- `Y_{aabc}`: for some `i`, `a_{i+2} ≡ a_i + 2` and `a_{i+1} ≡ a_{i-1} + 1 (mod 4)`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `Y_{aabc}`). -/
public def C4ModFourAABC (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, a (i + 2) ≡ a i + 2 [MOD 4] ∧ a (i + 1) ≡ a (i - 1) + 1 [MOD 4]

/-- `\hat Y_{abac}`: for some `i`, `a_i ≡ a_{i+2}` and `a_{i+1} ≡ a_{i-1} + 1 (mod 4)`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `\hat Y_{abac}`). -/
public def C4ModFourABACHat (a : Fin 4 → ℕ) : Prop :=
  ∃ i : Fin 4, a i ≡ a (i + 2) [MOD 4] ∧ a (i + 1) ≡ a (i - 1) + 1 [MOD 4]

/-- `\hat Y_{abab}`: `a₀ ≡ a₂` and `a₁ ≡ a₃ (mod 4)`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `\hat Y_{abab}`). -/
public def C4ModFourABABHat (a : Fin 4 → ℕ) : Prop :=
  a 0 ≡ a 2 [MOD 4] ∧ a 1 ≡ a 3 [MOD 4]

/-- `(\hat Y_{abab})^c`: games with an even total that are not in `\hat Y_{abab}`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definition of `(\hat Y_{abab})^c`). -/
public def C4ModFourABABHatCompl (a : Fin 4 → ℕ) : Prop :=
  Even (∑ i, a i) ∧ ¬ C4ModFourABABHat a

/-- Small values of the mod-`3` patterns: `(0,0,0,0) ∈ \hat X_{aabb}`, `(1,0,0,0) ∈ X_{aaab}`,
`(0,1,0,1) ∈ X_{abab}`, `(0,0,1,2) ∈ X_{aabc}`, `(0,1,0,2) ∈ X_{abac}`, and
`(0,0,0,0) ∉ X_{aaab}`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definitions of the sets `X`). -/
public theorem c4Pattern_examples :
    C4PatternAABBHat ![0, 0, 0, 0] ∧ C4PatternAAAB ![1, 0, 0, 0] ∧
      C4PatternABAB ![0, 1, 0, 1] ∧ C4PatternAABC ![0, 0, 1, 2] ∧
      C4PatternABAC ![0, 1, 0, 2] ∧ ¬ C4PatternAAAB ![0, 0, 0, 0] := by
  unfold C4PatternAABBHat C4PatternAAAB C4PatternABAB C4PatternAABC C4PatternABAC
  decide

/-- Small values of the mod-`4` patterns: `(2,0,0,1) ∈ Y_{aabc}`, `(0,1,0,0) ∈ \hat Y_{abac}`,
`(0,0,0,0) ∈ \hat Y_{abab}`, and `(1,1,0,0) ∈ (\hat Y_{abab})^c`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Section 3 (definitions of the sets `Y`). -/
public theorem c4ModFour_examples :
    C4ModFourAABC ![2, 0, 0, 1] ∧ C4ModFourABACHat ![0, 1, 0, 0] ∧
      C4ModFourABABHat ![0, 0, 0, 0] ∧ C4ModFourABABHatCompl ![1, 1, 0, 0] := by
  unfold C4ModFourAABC C4ModFourABACHat C4ModFourABABHatCompl C4ModFourABABHat
  decide

/-- Lemma 14: each of `X_{aaab}`, `X_{abab}`, `X_{aabc}`, `X_{abac}`, `\hat X_{aabb}` is
invariant under a `(2:1)`-pebbling move from `v_j` to `v_{j+ε}` (`ε = ±1`) followed by the
opponent's rotational symmetric move (from `v_{j+2}` to `v_{j-ε}`) or reflectional move (from
`v_{j-ε}` to `v_{j+2}`), whenever both moves are legal.

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

/-- Lemma 15: `\hat X_{aabb} ∪ X_{abac}` and `X_{aaab} ∪ X_{abab} ∪ X_{aabc}` are each closed
under `(2:1)`-pebbling moves on `C_4`.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 15. -/
public theorem_wanted c4Pattern_closed_under_moves (a b : Fin 4 → ℕ)
    (hb : b ∈ pebblingMoves (SimpleGraph.cycleGraph 4) 1 a) :
    ((C4PatternAABBHat a ∨ C4PatternABAC a) → (C4PatternAABBHat b ∨ C4PatternABAC b)) ∧
      ((C4PatternAAAB a ∨ C4PatternABAB a ∨ C4PatternAABC a) →
        (C4PatternAAAB b ∨ C4PatternABAB b ∨ C4PatternAABC b))

/-- Theorem 16: a `C_4` `(2:1)`-pebbling game in `\hat X_{aabb} ∪ X_{abac}` is a P-game iff its
total number of pebbles is even.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 16. -/
public theorem_wanted pebbling_cycleFour_isP_iff_even (a : Fin 4 → ℕ)
    (ha : C4PatternAABBHat a ∨ C4PatternABAC a) :
    IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a ↔ Even (∑ i, a i)

/-- Theorem 17: every `C_4` `(2:1)`-pebbling game in `\hat Y_{abab}` is a P-game. The paper's
sets range over positive totals; this statement also covers the empty position, which lies in
`\hat Y_{abab}` and is a P-game (`pebblingGame_isP_of_forall_le`).

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 17. -/
public theorem_wanted pebbling_cycleFour_isP_of_modFourABABHat (a : Fin 4 → ℕ)
    (ha : C4ModFourABABHat a) : IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a

/-- Theorem 18: every `C_4` `(2:1)`-pebbling game in
`(X_{abab} ∪ X_{aabc} ∪ X_{aaab}) ∩ \hat Y_{abac}` is a P-game.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 18. -/
public theorem_wanted pebbling_cycleFour_isP_of_modFourABACHat (a : Fin 4 → ℕ)
    (hX : C4PatternABAB a ∨ C4PatternAABC a ∨ C4PatternAAAB a) (hY : C4ModFourABACHat a) :
    IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a

/-- Theorem 19: every `C_4` `(2:1)`-pebbling game in `Y_{aabc}` is an N-game.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 19. -/
public theorem_wanted pebbling_cycleFour_isN_of_modFourAABC (a : Fin 4 → ℕ)
    (ha : C4ModFourAABC a) : ¬ IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a

/-- Theorem 20: every `C_4` `(2:1)`-pebbling game in
`(X_{abab} ∪ X_{aabc} ∪ X_{aaab}) ∩ (\hat Y_{abab})^c` is an N-game.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 20. -/
public theorem_wanted pebbling_cycleFour_isN_of_modFourABABHatCompl (a : Fin 4 → ℕ)
    (hX : C4PatternABAB a ∨ C4PatternAABC a ∨ C4PatternAAAB a)
    (hY : C4ModFourABABHatCompl a) : ¬ IsP (pebblingGame (SimpleGraph.cycleGraph 4) 1) a

end

end MetaMathlibExt
