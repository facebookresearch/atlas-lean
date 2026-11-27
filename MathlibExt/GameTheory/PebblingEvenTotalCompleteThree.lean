/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.PebblingCompleteThree

/-!
# Even-total P-positions of pebbling on the triangle

`pebbling_completeThree_isP_of_le` shows that a triangle position of even total in the
stated range is a P-position if no pile exceeds half the total.

## References

* Kayla Barker, Mia DeStefano, Eugene Fiorini, Michael Gohn, Joe Miller, Jacob Roeder, and
  Tony W. H. Wong, *Generalized Impartial Two-player Pebbling Games on $K_3$ and $C_4$*,
  Journal of Integer Sequences 27 (2024), Article 24.5.8, pp. 1–15
  (<https://cs.uwaterloo.ca/journals/JIS/VOL27/Wong/wong43.pdf>).
  Section 2, Lemma 8, pp. 5–6, proves this result using the reply from Lemma 7.
* Eugene Fiorini, Max Lind, Andrew Woldar, and Tony W. H. Wong,
  *Characterizing Winning Positions in the Impartial Two-Player Pebbling Game on Complete Graphs*,
  Journal of Integer Sequences 24 (2021), Article 21.6.4, pp. 1–10
  (<https://cs.uwaterloo.ca/journals/JIS/VOL24/Wong/wong31.pdf>).
  Theorem 1(b), p. 3, gives the earlier parity result for the `(2:1)` game on `K_3`
  quoted in Section 1 of Barker et al.
-/

namespace MetaMathlibExt

open SpragueGrundy

/-- **Pebbling on the triangle: total 6k-2ℓ with no pile above half is a P-position.** Let $k$ be
a positive integer and consider the $(k+1:k)$-pebbling game on the complete graph $K_3$, where a
move removes $k+1$ pebbles from one vertex and adds $k$ pebbles to another. Let $\ell$ be a
natural number with $\ell \le 2k - 1$. Every position with $6k - 2\ell$ pebbles in total in which
every pile is at most $3k - \ell$ is a P-position.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Lemma 8. -/
public theorem pebbling_completeThree_isP_of_le (k ℓ : ℕ) (hk : 0 < k)
    (hℓ : ℓ + 1 ≤ 2 * k) (a : Fin 3 → ℕ) (hsum : ∑ i, a i = 6 * k - 2 * ℓ)
    (hmax : ∀ i, a i ≤ 3 * k - ℓ) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) k) a := by
  generalize hd : 2 * k - ℓ = d
  induction d generalizing ℓ a with
  | zero => omega
  | succ d ih =>
    by_cases hterm : ∀ i, a i ≤ k
    · exact pebblingGame_isP_of_forall_le _ k a hterm
    obtain ⟨i, hi⟩ := not_forall.mp hterm
    have hbig : ∃ i, k + 1 ≤ a i := ⟨i, by omega⟩
    refine (isP_iff _ _).2 fun b hb hPb => ?_
    obtain ⟨c, hc, hcmax⟩ :=
      pebbling_completeThree_response_lowersMax k ℓ hk hℓ a hsum hbig hmax b hb
    apply (isP_iff _ _).1 hPb c hc
    -- At the endpoint, the lowered cap is k, so the reply ends the game.
    by_cases hend : ℓ + 1 = 2 * k
    · exact pebblingGame_isP_of_forall_le _ k c fun j => by
        have hj := hcmax j
        omega
    -- Otherwise, the pair of moves lowers the total by two and advances ℓ by one.
    obtain ⟨u, v, huv, hu, hab⟩ := (mem_pebblingMoves _ k a b).1 hb
    obtain ⟨x, y, hxy, hx, hbc⟩ := (mem_pebblingMoves _ k b c).1 hc
    have habSum := sum_pebblingStep_add_one k a huv.ne hu
    have hbcSum := sum_pebblingStep_add_one k b hxy.ne hx
    rw [hab] at habSum
    rw [hbc] at hbcSum
    exact ih (ℓ + 1) (by omega) c (by omega) (by simpa only [Nat.sub_sub] using hcmax)
      (by omega)

end MetaMathlibExt
