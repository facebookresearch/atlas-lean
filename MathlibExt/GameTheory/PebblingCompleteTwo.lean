/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ImpartialPebblingGame

/-!
# Winning positions of pebbling on the complete graph on two vertices

`pebbling_completeTwo_isN_iff` classifies the winning positions by the parity of the total
and the congruence of the two piles modulo three.

## References

* Kayla Barker, Mia DeStefano, Eugene Fiorini, Michael Gohn, Joe Miller, Jacob Roeder, and
  Tony W. H. Wong, *Generalized Impartial Two-player Pebbling Games on $K_3$ and $C_4$*,
  Journal of Integer Sequences 27 (2024), Article 24.5.8, pp. 1–15
  (<https://cs.uwaterloo.ca/journals/JIS/VOL27/Wong/wong43.pdf>). Theorem 1(a), p. 3,
  states both the winning-position classification and the absence of an all-N threshold.
* Eugene Fiorini, Max Lind, Andrew Woldar, and Tony W. H. Wong,
  *Characterizing Winning Positions in the Impartial Two-Player Pebbling Game on Complete Graphs*,
  Journal of Integer Sequences 24 (2021), Article 21.6.4, pp. 1–10
  (<https://cs.uwaterloo.ca/journals/JIS/VOL24/Wong/wong31.pdf>). Theorem 1(a), p. 3,
  gives the original winning-position classification, cited as reference [2] by Barker et al.
-/

namespace MetaMathlibExt

open SpragueGrundy

namespace pebbling_completeTwo_isN_iff

private abbrev game := pebblingGame (⊤ : SimpleGraph (Fin 2)) 1

private def losing (a : Fin 2 → ℕ) : Prop :=
  Even (a 0 + a 1) ↔ a 0 ≡ a 1 [MOD 3]

-- A move removes one pebble overall and adds one modulo three to both piles.
private theorem losing_move {a b : Fin 2 → ℕ} (hb : b ∈ game.moves a) :
    losing b ↔ ¬ losing a := by
  obtain ⟨i, j, hadj, hi, rfl⟩ := (mem_pebblingMoves _ 1 a b).1 hb
  have total := sum_pebblingStep_add_one 1 a hadj.ne hi
  simp only [Fin.sum_univ_two] at total
  have endpoints : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide
  have residues : pebblingStep 1 a i j 0 ≡ pebblingStep 1 a i j 1 [MOD 3] ↔
      a 0 ≡ a 1 [MOD 3] := by
    rcases endpoints i j hadj.ne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [pebblingStep, Nat.ModEq] <;> omega
  unfold losing
  rw [residues, ← total, Nat.even_add_one]
  tauto

private theorem isP_iff_losing (a : Fin 2 → ℕ) : IsP game a ↔ losing a := by
  induction a using (wfRel game).induction with
  | h a ih =>
    rw [isP_iff]
    have successor (b) (hb : b ∈ game.moves a) : ¬ IsP game b ↔ losing a := by
      rw [ih b hb, losing_move hb, not_not]
    constructor
    · intro h
      by_cases h₀ : 2 ≤ a 0
      · have hb := (mem_pebblingMoves (⊤ : SimpleGraph (Fin 2)) 1 a _).2
            ⟨0, 1, by decide, h₀, rfl⟩
        exact (successor _ hb).1 (h _ hb)
      by_cases h₁ : 2 ≤ a 1
      · have hb := (mem_pebblingMoves (⊤ : SimpleGraph (Fin 2)) 1 a _).2
            ⟨1, 0, by decide, h₁, rfl⟩
        exact (successor _ hb).1 (h _ hb)
      -- With both piles at most one, an even total means that the piles are equal.
      simp only [losing, Nat.even_iff, Nat.ModEq]
      omega
    · exact fun ha b hb => (successor b hb).2 ha

end pebbling_completeTwo_isN_iff

/-- **Winning positions of $(2:1)$-pebbling on $K_2$.** Let $a = (a_0, a_1)$ be a position of the
$(2:1)$-pebbling game on the complete graph $K_2$, with $a_0$ and $a_1$ pebbles on its two
vertices. If $a_0 + a_1$ is even, then $a$ is an N-position (that is, not a P-position) if and
only if $a_0 \not\equiv a_1 \pmod 3$. If $a_0 + a_1$ is odd, then $a$ is an N-position if and
only if $a_0 \equiv a_1 \pmod 3$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(a), quoting E. Fiorini, M. Lind, A. Woldar, and T. W. H. Wong,
J. Integer Sequences 24 (2021), Article 21.6.4. -/
public theorem pebbling_completeTwo_isN_iff (a : Fin 2 → ℕ) :
    (Even (a 0 + a 1) →
      (¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) a ↔ ¬ a 0 ≡ a 1 [MOD 3])) ∧
    (Odd (a 0 + a 1) →
      (¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) a ↔ a 0 ≡ a 1 [MOD 3])) := by
  rw [pebbling_completeTwo_isN_iff.isP_iff_losing]
  unfold pebbling_completeTwo_isN_iff.losing
  constructor
  · intro he
    simp [he]
  · intro ho
    simp [Nat.not_even_iff_odd.2 ho]

/-- **No all-N threshold for $(2:1)$-pebbling on $K_2$.** For every natural number $m$, some
$(2:1)$-pebbling game on the complete graph $K_2$ with $m$ pebbles in total is a P-game; that is,
$m^{(2:1)}(K_2)$, the least total at which every game is an N-game, does not exist.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(a), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem pebblingAllNTotals_completeTwo_eq_empty :
    pebblingAllNTotals (⊤ : SimpleGraph (Fin 2)) 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro m hm
  unfold pebblingAllNTotals at hm
  let a : Fin 2 → ℕ := ![m / 2, m - m / 2]
  have hsum : a 0 + a 1 = m := by
    change m / 2 + (m - m / 2) = m
    omega
  have hn := hm a (by rwa [Fin.sum_univ_two])
  obtain ⟨he, ho⟩ := pebbling_completeTwo_isN_iff a
  rw [hsum] at he ho
  by_cases hmEven : Even m
  · have ha : a 0 = a 1 := by
      rw [Nat.even_iff] at hmEven
      change m / 2 = m - m / 2
      omega
    exact (he hmEven).mp hn (ha ▸ Nat.ModEq.refl _)
  · have hc := (ho (Nat.not_even_iff_odd.mp hmEven)).mp hn
    change m / 2 % 3 = (m - m / 2) % 3 at hc
    rw [Nat.even_iff] at hmEven
    omega

end MetaMathlibExt
