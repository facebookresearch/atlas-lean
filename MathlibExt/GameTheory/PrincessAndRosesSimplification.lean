/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.GameTheory.SlowANim
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases
import all MathlibExt.GameTheory.SlowANimGeneralReduction
import all MathlibExt.GameTheory.SpragueGrundy

/-!
# Simplifying four-pile Princess and the Roses

For natural numbers `a ≥ b ≥ c ≥ d` and any natural number `n`, ordinary Princess and the Roses
at `(a, b, c, d)` has the same Sprague–Grundy value as simplified Princess and the Roses at
`(a + n, b + n, c + n, d)`. We sort ordinary moves before comparing them with simplified moves,
which must preserve the order of the piles.

## References

- Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
  INTEGERS 26 (2026), Article G4, pp. 1–40, Sections 2.1–2.2 and Lemmas 5 and 11.
- Elwyn R. Berlekamp, John H. Conway, and Richard K. Guy, *Winning Ways for Your Mathematical
  Plays*, 2nd ed., vol. 3, A K Peters (2003), pp. 524–528, for the game rules.
- John H. Conway, *On Numbers and Games*, 2nd ed., A K Peters (2001), for induction on game
  options. See also Dierk Schleicher and Michael Stoll, *An Introduction to Conway’s Games and
  Numbers*, arXiv:math/0410026 (2005), Theorem 2.3, cited by Friedman.
- R. P. Sprague, *Über mathematische Kampfspiele*, Tôhoku Mathematical Journal 41
  (1935–1936), pp. 438–444, and P. M. Grundy, *Mathematics and games*, Eureka 2 (1939),
  pp. 6–8, for the Sprague–Grundy theory behind the equivalence criterion.
- `MathlibExt.GameTheory.SlowANimGeneralReduction` (`sum_after_add_card`) and
  `MathlibExt.GameTheory.SpragueGrundy` (`sum_cases`, `sum_mem_left`, `sum_mem_right`,
  and `impartialGame_equiv_iff_isP_gameSum`) supply the Lean move-count and game-sum results.
-/

namespace MetaMathlibExt

@[expose] public section

open SpragueGrundy

/-- **The Princess and the Roses game.** For $k \in \mathbb{N}$ and $p \in \mathbb{N}^k$, the
Princess and the Roses game (P&R) with $k$ labelled piles started at $p$ is the impartial game
whose positions are the $q \in \mathbb{N}^k$, with $q_i$ objects on pile $i$, and whose moves
remove one object from one nonempty pile, or one object from each of two distinct nonempty
piles. It is Slow$A$-Nim $\mathrm{SN}(k, \{1, 2\})$ started at $p$, and its rank is the total
number of objects $\sum_i q_i$.

Pile order is not normalized; the paper's convention of listing piles in non-increasing order
does not change the game.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 2.1. -/
public def princessRoses {k : ℕ} (p : Fin k → ℕ) : ImpartialGame :=
  { slowANimGame k {1, 2} with start := p }

/-- **Moves of simplified P&R.** The simplified Princess and the Roses game on four sorted piles
$(a, b, c, d)$ has seven moves, given as the amounts removed from $(a, b, c, d)$: $(1, 0, 0, 0)$,
$(0, 1, 0, 0)$, $(0, 0, 0, 1)$, $(1, 1, 0, 0)$, $(1, 0, 0, 1)$, $(0, 1, 0, 1)$ and $(0, 0, 1, 1)$.

These are the moves of four-pile Princess and the Roses except taking one object from the third
pile alone or together with the first or second pile, so the third pile may be taken from only
together with the fourth.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def simplifiedPrincessRosesMoveList : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1), (1, 1, 0, 0), (1, 0, 0, 1), (0, 1, 0, 1),
    (0, 0, 1, 1)]

/-- **Options in simplified Princess and the Roses.** The seven simplified Princess and the Roses
moves are the removal vectors $(1, 0, 0, 0)$, $(0, 1, 0, 0)$, $(0, 0, 0, 1)$, $(1, 1, 0, 0)$,
$(1, 0, 0, 1)$, $(0, 1, 0, 1)$ and $(0, 0, 1, 1)$. For a quadruple $(a, b, c, d)$ of natural
numbers, its options are the quadruples $(a - r_1, b - r_2, c - r_3, d - r_4)$ for those moves
$(r_1, r_2, r_3, r_4)$ with $r_1 \le a$, $r_2 \le b$, $r_3 \le c$ and $r_4 \le d$ whose result is
in non-increasing order: $a - r_1 \ge b - r_2 \ge c - r_3 \ge d - r_4$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Sections 2.2 and 3.1. -/
public def simplifiedPrincessRosesMoves (p : ℕ × ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (simplifiedPrincessRosesMoveList.toFinset.filter fun m =>
      m.1 ≤ p.1 ∧ m.2.1 ≤ p.2.1 ∧ m.2.2.1 ≤ p.2.2.1 ∧ m.2.2.2 ≤ p.2.2.2 ∧
        p.2.1 - m.2.1 ≤ p.1 - m.1 ∧ p.2.2.1 - m.2.2.1 ≤ p.2.1 - m.2.1 ∧
        p.2.2.2 - m.2.2.2 ≤ p.2.2.1 - m.2.2.1).image
    fun m => (p.1 - m.1, p.2.1 - m.2.1, p.2.2.1 - m.2.2.1, p.2.2.2 - m.2.2.2)

/-- **Characterization of simplified P&R options.** For natural numbers $a, b, c, d$ and
$a', b', c', d'$, the position $[a', b', c', d']$ is an option of the simplified P&R position
$[a, b, c, d]$ if and only if $a' \le a$, $b' \le b$, $c' \le c$, $d' \le d$,
$a' \ge b' \ge c' \ge d'$, and the amounts removed $(a - a', b - b', c - c', d - d')$ form one of
the seven simplified P&R moves $(1, 0, 0, 0)$, $(0, 1, 0, 0)$, $(0, 0, 0, 1)$, $(1, 1, 0, 0)$,
$(1, 0, 0, 1)$, $(0, 1, 0, 1)$ and $(0, 0, 1, 1)$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Sections 2.2 and 3.1. -/
public theorem mem_simplifiedPrincessRosesMoves {a b c d a' b' c' d' : ℕ} :
    (a', b', c', d') ∈ simplifiedPrincessRosesMoves (a, b, c, d) ↔
      a' ≤ a ∧ b' ≤ b ∧ c' ≤ c ∧ d' ≤ d ∧ b' ≤ a' ∧ c' ≤ b' ∧ d' ≤ c' ∧
        (a - a', b - b', c - c', d - d') ∈ simplifiedPrincessRosesMoveList := by
  simp only [simplifiedPrincessRosesMoves, Finset.mem_image, Finset.mem_filter,
    List.mem_toFinset, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨m₁, m₂, m₃, m₄, ⟨hm, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩, rfl, rfl, rfl, rfl⟩
    rw [Nat.sub_sub_self h₁, Nat.sub_sub_self h₂, Nat.sub_sub_self h₃, Nat.sub_sub_self h₄]
    exact ⟨by omega, by omega, by omega, by omega, h₅, h₆, h₇, hm⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, hm⟩
    exact ⟨a - a', b - b', c - c', d - d', ⟨hm, by omega⟩, by omega⟩

-- Keep the moved proof unchanged, including its existing `show` step.
set_option linter.style.show false in
/-- **Simplified P&R moves decrease the number of objects.** For all quadruples $(a, b, c, d)$
and $(a', b', c', d')$ of natural numbers, if $(a', b', c', d')$ is an option of $(a, b, c, d)$
in simplified Princess and the Roses, then $a' + b' + c' + d' < a + b + c + d$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public theorem simplifiedPrincessRosesMoves_rank_lt {p q : ℕ × ℕ × ℕ × ℕ}
    (h : q ∈ simplifiedPrincessRosesMoves p) :
    q.1 + q.2.1 + q.2.2.1 + q.2.2.2 < p.1 + p.2.1 + p.2.2.1 + p.2.2.2 := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨a', b', c', d'⟩ := q
  have := mem_simplifiedPrincessRosesMoves.mp h
  simp only [simplifiedPrincessRosesMoveList, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at this
  show a' + b' + c' + d' < a + b + c + d
  omega

/-- **Simplified Princess and the Roses.** For a quadruple $p$ of natural numbers, simplified
Princess and the Roses started at $p$ is the impartial game whose positions are all quadruples
$(a, b, c, d)$ of natural numbers, whose options from a position are its simplified Princess and
the Roses options (the results of the seven simplified moves that take no pile below zero and
leave the piles in non-increasing order), whose rank is the total number of objects
$a + b + c + d$, and whose start position is $p$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def simplifiedPrincessRoses (p : ℕ × ℕ × ℕ × ℕ) : ImpartialGame where
  Pos := ℕ × ℕ × ℕ × ℕ
  eqDec := inferInstance
  moves := simplifiedPrincessRosesMoves
  rank := fun q => q.1 + q.2.1 + q.2.2.1 + q.2.2.2
  rank_lt := fun _ _ h => simplifiedPrincessRosesMoves_rank_lt h
  start := p

-- A move changes each pile by at most one and removes one or two objects in total.
private theorem mem_one_two_moves_iff {k : ℕ} {p q : Fin k → ℕ} :
    q ∈ slowANimMoves {1, 2} p ↔
      (∀ i, q i ≤ p i ∧ p i ≤ q i + 1) ∧
        (∑ i, q i) < (∑ i, p i) ∧ (∑ i, p i) ≤ (∑ i, q i) + 2 := by
  simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨S, ⟨-, hcard, hpos⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · unfold slowANimAfter
      split_ifs <;> omega
    · have hsum := slowANim_generalReduction.sum_after_add_card p S hpos
      omega
  · rintro ⟨hpq, hlo, hhi⟩
    let S := Finset.univ.filter fun i => q i < p i
    have hpos (i : Fin k) (hi : i ∈ S) : 1 ≤ p i :=
      Nat.one_le_of_lt (Finset.mem_filter.mp hi).2
    have heq : slowANimAfter p S = q := by
      funext i
      have hi := hpq i
      by_cases hlt : q i < p i
      · simp [slowANimAfter, S, hlt]
        omega
      · simp [slowANimAfter, S, hlt]
        omega
    have hsum := slowANim_generalReduction.sum_after_add_card p S hpos
    simp only [heq] at hsum
    exact ⟨S, ⟨Finset.card_pos.mp (by omega), by omega, hpos⟩, heq⟩

private theorem one_two_move_perm {k : ℕ} {p q : Fin k → ℕ} (σ : Equiv.Perm (Fin k))
    (h : q ∈ slowANimMoves {1, 2} p) : q ∘ σ ∈ slowANimMoves {1, 2} (p ∘ σ) := by
  obtain ⟨hb, hlo, hhi⟩ := mem_one_two_moves_iff.mp h
  exact mem_one_two_moves_iff.mpr
    ⟨fun i => hb (σ i), by simpa [Function.comp_def, Equiv.sum_comp] using And.intro hlo hhi⟩

-- Since each pile loses at most one, sorting by the sum of the old and new heights
-- sorts both tuples. In particular, a tie in the old heights is broken by the new heights.
private theorem sort_one_two_move {k : ℕ} {p q : Fin k → ℕ}
    (h : q ∈ slowANimMoves {1, 2} p) :
    ∃ τ : Equiv.Perm (Fin k), Antitone (p ∘ τ) ∧ Antitone (q ∘ τ) := by
  let τ := Tuple.sortDesc fun i => p i + q i
  have hs := Tuple.antitone_sortDesc (fun i => p i + q i)
  have hb := (mem_one_two_moves_iff.mp h).1
  refine ⟨τ, ?_, ?_⟩ <;> intro i j hij
  all_goals
    have hsum : p (τ j) + q (τ j) ≤ p (τ i) + q (τ i) := hs hij
    have hi := hb (τ i)
    have hj := hb (τ j)
    dsimp only [Function.comp_apply]
    omega

private theorem mem_vec_moves_iff {a b c d a' b' c' d' : ℕ} :
    ![a', b', c', d'] ∈ slowANimMoves {1, 2} ![a, b, c, d] ↔
      (a' ≤ a ∧ a ≤ a' + 1) ∧ (b' ≤ b ∧ b ≤ b' + 1) ∧
      (c' ≤ c ∧ c ≤ c' + 1) ∧ (d' ≤ d ∧ d ≤ d' + 1) ∧
      a' + b' + c' + d' < a + b + c + d ∧ a + b + c + d ≤ a' + b' + c' + d' + 2 := by
  rw [mem_one_two_moves_iff]
  simp [Fin.forall_fin_succ, Fin.sum_univ_succ, and_assoc, Nat.add_assoc]

private theorem mem_simplified_moves_iff {a b c d a' b' c' d' : ℕ} :
    (a', b', c', d') ∈ simplifiedPrincessRosesMoves (a, b, c, d) ↔
      (a' ≤ a ∧ a ≤ a' + 1) ∧ (b' ≤ b ∧ b ≤ b' + 1) ∧
      (c' ≤ c ∧ c ≤ c' + 1) ∧ (d' ≤ d ∧ d ≤ d' + 1) ∧
      a' + b' + c' + d' < a + b + c + d ∧ a + b + c + d ≤ a' + b' + c' + d' + 2 ∧
      b' ≤ a' ∧ c' ≤ b' ∧ d' ≤ c' ∧ (c' < c → d' < d) := by
  rw [mem_simplifiedPrincessRosesMoves]
  simp only [simplifiedPrincessRosesMoveList, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hb, hc, hd, hab, hbc, hcd, hm⟩
    rcases hm with h | h | h | h | h | h | h <;> omega
  · rintro ⟨ha, hb, hc, hd, hlo, hhi, hab, hbc, hcd, h⟩
    exact ⟨ha.1, hb.1, hc.1, hd.1, hab, hbc, hcd, by omega⟩

private def ordinaryRoses : ImpartialGame := princessRoses ![0, 0, 0, 0]

private def simplifiedRoses : ImpartialGame := simplifiedPrincessRoses (0, 0, 0, 0)

private theorem isP_shifted_sum (a b c d n : ℕ) (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c)
    (σ : Equiv.Perm (Fin 4)) :
    IsP (gameSum ordinaryRoses simplifiedRoses) (![a, b, c, d] ∘ σ, (a + n, b + n, c + n, d)) := by
  let p : Fin 4 → ℕ := ![a, b, c, d] ∘ σ
  let t := (a + n, b + n, c + n, d)
  refine (isP_iff _ _).2 ?_
  intro v hv
  rcases sum_cases ordinaryRoses simplifiedRoses p t v hv with
    ⟨q, hq, rfl⟩ | ⟨⟨x, y, z, w⟩, hm, rfl⟩
  · change q ∈ slowANimMoves {1, 2} p at hq
    obtain ⟨τ, hpτ, hqτ⟩ := sort_one_two_move hq
    have hp : Antitone (![a, b, c, d] : Fin 4 → ℕ) := by
      rw [Fin.antitone_iff_succ_le]
      intro i
      fin_cases i
      · exact hab
      · exact hbc
      · exact hcd
    have hp' : p ∘ τ = ![a, b, c, d] :=
      Tuple.unique_antitone (σ := τ.trans σ) (τ := Equiv.refl _) hpτ hp
    let a' := q (τ 0)
    let b' := q (τ 1)
    let c' := q (τ 2)
    let d' := q (τ 3)
    have hq' : q ∘ τ = ![a', b', c', d'] := by
      funext i
      fin_cases i <;> rfl
    have hqEq : q = ![a', b', c', d'] ∘ τ.symm := by
      rw [← hq']
      funext i
      change q i = q (τ (τ.symm i))
      exact congrArg q (τ.apply_symm_apply i).symm
    have hmove := one_two_move_perm τ hq
    rw [hp', hq'] at hmove
    obtain ⟨ha, hb, hc, hd, hlo, hhi⟩ := mem_vec_moves_iff.mp hmove
    have hab' : b' ≤ a' := hqτ (show (0 : Fin 4) ≤ 1 by decide)
    have hbc' : c' ≤ b' := hqτ (show (1 : Fin 4) ≤ 2 by decide)
    have hcd' : d' ≤ c' := hqτ (show (2 : Fin 4) ≤ 3 by decide)
    by_cases h : c' < c → d' < d
    · -- A legal move on both boards is mirrored on the simplified board.
      have hmirror : (a' + n, b' + n, c' + n, d') ∈ simplifiedRoses.moves t :=
        mem_simplified_moves_iff.mpr (by omega)
      intro hP
      rw [hqEq] at hP
      exact (isP_iff _ _).mp hP _ (sum_mem_right _ _ _ _ _ hmirror)
        (isP_shifted_sum a' b' c' d' n hab' hbc' hcd' τ.symm)
    · -- A move on the third but not fourth pile is answered on the original board
      -- by decrementing the rest of the top three piles.
      have hc' : c' < c := (not_imp.mp h).1
      have hd' : d' = d := by have := (not_imp.mp h).2; omega
      have hreply : ![a - 1, b - 1, c - 1, d] ∈ slowANimMoves {1, 2} ![a', b', c', d'] :=
        mem_vec_moves_iff.mpr (by omega)
      have hreply' : ![a - 1, b - 1, c - 1, d] ∘ τ.symm ∈ ordinaryRoses.moves q := by
        rw [hqEq]
        exact one_two_move_perm τ.symm hreply
      have hshift (u : ℕ) (hu : 1 ≤ u) : u - 1 + (n + 1) = u + n := by
        rw [Nat.add_comm n 1, ← Nat.add_assoc, Nat.sub_add_cancel hu]
      have ht : (a - 1 + (n + 1), b - 1 + (n + 1), c - 1 + (n + 1), d) = t := by
        simp only [t, hshift a (by omega), hshift b (by omega), hshift c (by omega)]
      have hrec := isP_shifted_sum (a - 1) (b - 1) (c - 1) d (n + 1)
        (by omega) (by omega) (by omega) τ.symm
      rw [ht] at hrec
      exact fun hP => (isP_iff _ _).mp hP _ (sum_mem_left _ _ _ _ _ hreply') hrec
  · change (x, y, z, w) ∈ simplifiedPrincessRosesMoves (a + n, b + n, c + n, d) at hm
    obtain ⟨hx, hy, hz, hw, hlo, hhi, hxy, hyz, hzw, h⟩ := mem_simplified_moves_iff.mp hm
    -- The third pile cannot drop below the shift: decreasing it requires decreasing
    -- the fourth, which in that case started positive. The top two stay above it.
    have hn : n ≤ z := by omega
    have hshift : (x - n + n, y - n + n, z - n + n, w) = (x, y, z, w) := by
      simp only [Nat.sub_add_cancel (hn.trans (hyz.trans hxy)), Nat.sub_add_cancel (hn.trans hyz),
        Nat.sub_add_cancel hn]
    have hmirror : ![x - n, y - n, z - n, w] ∈ slowANimMoves {1, 2} ![a, b, c, d] :=
      mem_vec_moves_iff.mpr (by omega)
    have hmirror' : ![x - n, y - n, z - n, w] ∘ σ ∈ ordinaryRoses.moves p :=
      one_two_move_perm σ hmirror
    have hrec := isP_shifted_sum (x - n) (y - n) (z - n) w n
      (by omega) (by omega) (by omega) σ
    rw [hshift] at hrec
    exact fun hP => (isP_iff _ _).mp hP _ (sum_mem_left _ _ _ _ _ hmirror') hrec
termination_by a + b + c + d
decreasing_by all_goals omega

/-- **Four-pile P&R is equivalent to simplified P&R.** For natural numbers $a \ge b \ge c \ge d$
and every natural number $n$, the Princess and the Roses position $(a, b, c, d)$ is equivalent to
the simplified P&R position $[a + n, b + n, c + n, d]$; that is, the two have the same
Sprague–Grundy value.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 11 (`integers-2026-G4-lem-11`). -/
public theorem princessRoses_equiv_simplifiedPrincessRoses (a b c d n : ℕ)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) :
    Equiv (princessRoses ![a, b, c, d]) (simplifiedPrincessRoses (a + n, b + n, c + n, d)) := by
  rw [impartialGame_equiv_iff_isP_gameSum]
  exact isP_shifted_sum a b c d n hab hbc hcd (Equiv.refl _)

end

end MetaMathlibExt
