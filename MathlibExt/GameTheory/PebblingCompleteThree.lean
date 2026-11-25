/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ImpartialPebblingGame
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases

/-!
# Winning the triangle pebbling game with a bounded largest pile

`pebbling_completeThree_isN_of_le_fourK` gives a winning move from any position of
total `6 * k - 1` in which every pile has at most `4 * k` pebbles.
-/

namespace MetaMathlibExt

open SpragueGrundy

namespace pebbling_completeThree_isN_of_le_fourK

-- After each pair of moves, the total drops by two and the bound drops by one.
private theorem isP_of_half_total (k : ℕ) (hk : 0 < k) (m : ℕ) (hm : m ≤ 3 * k)
    (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 2 * m) (hmax : ∀ i, a i ≤ m) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a := by
  induction m generalizing a with
  | zero =>
    exact pebblingGame_isP_of_forall_le _ k a fun i => (hmax i).trans (Nat.zero_le k)
  | succ m ih =>
    refine (isP_iff _ _).2 fun b hb hPb => ?_
    obtain ⟨i, j, hij, hi, hab⟩ := (mem_pebblingMoves _ k a b).1 hb
    have hiMax := hmax i
    let ℓ := 3 * k - (m + 1)
    have hcap : 3 * k - ℓ = m + 1 := by dsimp [ℓ]; omega
    obtain ⟨c, hc, hcmax⟩ := pebbling_completeThree_response_lowersMax k ℓ hk
      (by dsimp [ℓ]; omega) a (by omega) ⟨i, hi⟩ (by simpa only [hcap] using hmax) b hb
    obtain ⟨u, v, huv, hu, hbc⟩ := (mem_pebblingMoves _ k b c).1 hc
    have habSum := sum_pebblingStep_add_one k a hij.ne hi
    have hbcSum := sum_pebblingStep_add_one k b huv.ne hu
    rw [hab] at habSum
    rw [hbc] at hbcSum
    apply (isP_iff _ _).1 hPb c hc
    exact ih (by omega) c (by omega) (by simpa only [hcap, Nat.add_sub_cancel] using hcmax)

end pebbling_completeThree_isN_of_le_fourK

/-- **Pebbling on the triangle: total 6k-1 with every pile at most 4k.** Let $k$ be a positive
integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a move removes
$k+1$ pebbles from one vertex and adds $k$ pebbles to another. Every position with $6k - 1$
pebbles in total in which every pile is at most $4k$ is an N-position, that is, not a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Corollary 10. -/
public theorem pebbling_completeThree_isN_of_le_fourK (k : ℕ) (hk : 0 < k)
    (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 1) (hmax : ∀ i, a i ≤ 4 * k) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a := by
  -- In increasing order, transfer from the last pile to the first.
  let σ := Tuple.sort a
  have h₀₁ : a (σ 0) ≤ a (σ 1) := Tuple.monotone_sort a (by decide : (0 : Fin 3) ≤ 1)
  have h₁₂ : a (σ 1) ≤ a (σ 2) := Tuple.monotone_sort a (by decide : (1 : Fin 3) ≤ 2)
  have total : a (σ 0) + a (σ 1) + a (σ 2) = 6 * k - 1 := by
    simpa only [Fin.sum_univ_three] using (Equiv.sum_comp σ a).trans hsum
  have hi : k + 1 ≤ a (σ 2) := by omega
  have hne : σ 2 ≠ σ 0 := σ.injective.ne (by decide)
  let b := pebblingStep k a (σ 2) (σ 0)
  have hb := (mem_pebblingMoves (⊤ : SimpleGraph (Fin 3)) k a b).2 ⟨_, _, hne, hi, rfl⟩
  intro hPa
  apply (isP_iff _ _).1 hPa b hb
  apply pebbling_completeThree_isN_of_le_fourK.isP_of_half_total k hk (3 * k - 1) (by omega)
  · have := sum_pebblingStep_add_one k a hne hi
    change (∑ i, b i) + 1 = _ at this
    omega
  · intro i
    obtain ⟨v, rfl⟩ := σ.surjective i
    have hlim := hmax (σ 2)
    fin_cases v <;> simp [b, pebblingStep, σ.injective.eq_iff] <;> omega

end MetaMathlibExt
