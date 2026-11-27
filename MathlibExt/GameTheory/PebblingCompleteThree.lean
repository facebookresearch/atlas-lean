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
`pebbling_completeThree_isN_of_le` gives a winning move at the odd totals
`6 * k - 2 * ℓ + 1` under bounds on the largest and smallest piles.

`pebbling_completeThree_isP_twoKAddThree` gives the single-pile P-position with
`2 * k + 3` pebbles for positive `k`.

## References

* Kayla Barker, Mia DeStefano, Eugene Fiorini, Michael Gohn, Joe Miller, Jacob Roeder, and
  Tony W. H. Wong, *Generalized Impartial Two-player Pebbling Games on $K_3$ and $C_4$*,
  Journal of Integer Sequences 27 (2024), Article 24.5.8, pp. 1–15
  (<https://cs.uwaterloo.ca/journals/JIS/VOL27/Wong/wong43.pdf>). Lemma 9 and Corollary 10
  (p. 6) give the winning-position criteria, using the reply in Lemma 7 and the even-total
  P-position criterion in Lemma 8 (pp. 5–6).
  Section 2, Lemma 4 gives the single-pile P-position
  (<https://cs.uwaterloo.ca/journals/JIS/VOL27/Wong/wong43.html>).
* Eugene Fiorini, Max Lind, Andrew Woldar, and Tony W. H. Wong,
  *Characterizing Winning Positions in the Impartial Two-Player Pebbling Game on Complete Graphs*,
  Journal of Integer Sequences 24 (2021), Article 21.6.4, pp. 1–10, §1, for the original
  `(2:1)` game credited in §1 of Barker et al.
* Elwyn R. Berlekamp, John H. Conway, and Richard K. Guy, *Winning Ways for Your Mathematical
  Plays*, Vol. 1, CRC Press (2001), for the impartial-game background cited in §1 of Barker et al.
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

/-- **Pebbling on the triangle: a single pile of 2k+3 pebbles is a P-position.** Let $k$ be a
positive integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a
move removes $k+1$ pebbles from one vertex and adds $k$ pebbles to another. Every position with
$2k + 3$ pebbles on one vertex and none on the other two is a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 4. -/
public theorem pebbling_completeThree_isP_twoKAddThree (k : ℕ) (hk : 0 < k)
    (σ : Equiv.Perm (Fin 3)) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) (![2 * k + 3, 0, 0] ∘ σ) := by
  let a : Fin 3 → ℕ := ![2 * k + 3, 0, 0] ∘ σ
  let s := σ.symm 0
  have ha_s : a s = 2 * k + 3 := by simp [a, s]
  have ne_zero (x : Fin 3) (hx : x ≠ s) : σ x ≠ 0 := by
    simpa [s] using (σ.injective.ne hx : σ x ≠ σ s)
  have ha_zero (x : Fin 3) (hx : x ≠ s) : a x = 0 := by
    have hx' := ne_zero x hx
    change ![2 * k + 3, 0, 0] (σ x) = 0
    generalize σ x = v at hx' ⊢
    fin_cases v
    · exact (hx' rfl).elim
    · rfl
    · rfl
  let game := pebblingGame (⊤ : SimpleGraph (Fin 3)) k
  refine (isP_iff game a).2 fun b hb hPb => ?_
  obtain ⟨i, j, hadj, hi, rfl⟩ := (mem_pebblingMoves (⊤ : SimpleGraph (Fin 3)) k a b).1 hb
  -- Only the original pile can supply the first move.
  have his : i = s := by
    by_contra h
    rw [ha_zero i h] at hi
    omega
  subst i
  have hsj : s ≠ j := hadj.ne
  -- Reply from the same source to the vertex untouched by the first move.
  have third : ∀ v : Fin 3, v ≠ 0 → ∃ t : Fin 3, t ≠ 0 ∧ t ≠ v := by decide
  obtain ⟨t, ht0, htj⟩ := third (σ j) (ne_zero j hsj.symm)
  let w := σ.symm t
  have hws : w ≠ s := σ.symm.injective.ne ht0
  have hwj : w ≠ j := by simpa [w] using σ.symm.injective.ne htj
  let b := pebblingStep k a s j
  have hb_s : b s = k + 2 := by
    simp only [b, pebblingStep, Function.update_of_ne hsj, Function.update_self, ha_s]
    omega
  have hb_w : b w = 0 := by simp [b, pebblingStep, hws, hwj, ha_zero w hws]
  let c := pebblingStep k b s w
  have hc := (mem_pebblingMoves (⊤ : SimpleGraph (Fin 3)) k b c).2
    ⟨s, w, hws.symm, by omega, rfl⟩
  apply (isP_iff game b).1 hPb c hc
  -- The reply leaves one pebble at the source and k at each recipient.
  apply pebblingGame_isP_of_forall_le
  intro v
  by_cases hvw : v = w
  · subst v
    simp [c, pebblingStep, hb_w]
  by_cases hvs : v = s
  · subst v
    simp only [c, pebblingStep, Function.update_of_ne hws.symm, Function.update_self, hb_s]
    omega
  by_cases hvj : v = j
  · subst v
    simp [c, b, pebblingStep, hvw, hvs, ha_zero j hsj.symm]
  · simp [c, b, pebblingStep, hvw, hvs, hvj, ha_zero v hvs]

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

/-- **Pebbling on the triangle: N-positions with total 6k-2ℓ+1 and a small pile.** Let $k$ be a
positive integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a
move removes $k+1$ pebbles from one vertex and adds $k$ pebbles to another. Let $\ell$ be an
integer with $1 \le \ell \le 2k - 1$. Every position with $6k - 2\ell + 1$ pebbles in total in
which every pile is at most $4k - \ell + 1$ and some pile is at most $2k - \ell$ is an
N-position, that is, not a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 9. -/
public theorem pebbling_completeThree_isN_of_le (k ℓ : ℕ) (hk : 0 < k) (hℓ₁ : 1 ≤ ℓ)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ + 1)
    (hmax : ∀ i, a i ≤ 4 * k - ℓ + 1) (hmin : ∃ i, a i ≤ 2 * k - ℓ) :
    ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a := by
  let σ := Tuple.sort a
  have h₀₁ : a (σ 0) ≤ a (σ 1) := Tuple.monotone_sort a (by decide : (0 : Fin 3) ≤ 1)
  have h₁₂ : a (σ 1) ≤ a (σ 2) := Tuple.monotone_sort a (by decide : (1 : Fin 3) ≤ 2)
  have total : a (σ 0) + a (σ 1) + a (σ 2) = 6 * k - 2 * ℓ + 1 := by
    simpa only [Fin.sum_univ_three] using (Equiv.sum_comp σ a).trans hsum
  have hsmall : a (σ 0) ≤ 2 * k - ℓ := by
    obtain ⟨i, hi⟩ := hmin
    obtain ⟨v, rfl⟩ := σ.surjective i
    exact (Tuple.monotone_sort a (Fin.zero_le v)).trans hi
  have hi : k + 1 ≤ a (σ 2) := by omega
  have hmid : a (σ 1) ≤ 3 * k - ℓ := by omega
  -- Move from a largest pile to a smallest pile, leaving every pile at most half the new total.
  have hne : σ 2 ≠ σ 0 := σ.injective.ne (by decide)
  let b := pebblingStep k a (σ 2) (σ 0)
  have hb := (mem_pebblingMoves (⊤ : SimpleGraph (Fin 3)) k a b).2 ⟨_, _, hne, hi, rfl⟩
  intro hPa
  apply (isP_iff _ _).1 hPa b hb
  apply pebbling_completeThree_isN_of_le_fourK.isP_of_half_total k hk (3 * k - ℓ) (by omega)
  · have hmove := sum_pebblingStep_add_one k a hne hi
    change (∑ i, b i) + 1 = _ at hmove
    omega
  · intro i
    obtain ⟨v, rfl⟩ := σ.surjective i
    have hlarge := hmax (σ 2)
    fin_cases v <;> simp [b, pebblingStep, σ.injective.eq_iff] <;> omega

end MetaMathlibExt
