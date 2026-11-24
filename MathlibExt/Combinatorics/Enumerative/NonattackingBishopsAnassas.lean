/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Binomial
public import MathlibExt.Combinatorics.AssociatedStirlingSecond
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Prod

/-!
# Nonattacking bishops and anassas

This module defines nonattacking placements on finite boards and proves
`bishopsSquare_eq_sum`, Santos's extended Stirling formula for bishops on a square board.

The proof orders the diagonals of each color by length. Adding the longest diagonal gives
a recurrence for the number of placements on that color. Pascal's identity and the Stirling
recurrence show that the one-color sum satisfies it. Splitting a placement by color then
gives the convolution for the whole board.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Nonattacking placements.** Let $B$ be a board, that is, a finite set of squares
$(i, j) \in \mathbb{Z}^2$, let $M$ be a list of basic moves $v \in \mathbb{Z}^2$, and let $k$ be a
natural number. The nonattacking placements of $k$ pieces with basic moves $M$ on $B$ are the
$k$-element subsets $S \subseteq B$ such that for all distinct squares $p, q \in S$ and every
move $v \in M$, the difference $q - p$ is not parallel to $v$, that is,
$(q_1 - p_1) v_2 \ne (q_2 - p_2) v_1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public def nonattackingPlacements (B : Finset (ℤ × ℤ)) (M : List (ℤ × ℤ)) (k : ℕ) :
    Finset (Finset (ℤ × ℤ)) :=
  (B.powersetCard k).filter fun S =>
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ v ∈ M, (q.1 - p.1) * v.2 ≠ (q.2 - p.2) * v.1

/-- **Exactly one nonattacking placement of no pieces.** For every board $B$, a finite set of
squares of $\mathbb{Z}^2$, and every list $M$ of basic moves in $\mathbb{Z}^2$, there is
exactly one nonattacking placement of $0$ pieces with basic moves $M$ on $B$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public theorem card_nonattackingPlacements_zero (B : Finset (ℤ × ℤ)) (M : List (ℤ × ℤ)) :
    (nonattackingPlacements B M 0).card = 1 := by
  simp [nonattackingPlacements, Finset.filter_singleton]

/-- **The square board.** For a natural number $m$, the square board $S_m$ is the set of squares
$(i, j) \in \mathbb{Z}^2$ with $1 \le i \le m$ and $1 \le j \le m$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2. -/
public def squareBoard (m : ℕ) : Finset (ℤ × ℤ) :=
  Icc (1 : ℤ) m ×ˢ Icc (1 : ℤ) m

/-- **White squares of the square board.** For a natural number $m$, the white squares of the
square board $S_m = [1, m]^2$ are the integer squares $(i, j) \in S_m$ for which $i + j$ is
even.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2, Table 1. -/
public def whiteSquares (m : ℕ) : Finset (ℤ × ℤ) :=
  (squareBoard m).filter fun s => Even (s.1 + s.2)

/-- **Black squares of the square board.** For a natural number $m$, the black squares of the
$m \times m$ board $S_m = [1, m]^2$ are the squares $(i, j) \in S_m$ with $i + j$ odd.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2, Table 1. -/
public def blackSquares (m : ℕ) : Finset (ℤ × ℤ) :=
  (squareBoard m).filter fun s => Odd (s.1 + s.2)

/-- **Basic moves of the bishop.** The basic moves of the bishop are the two vectors $(1, 1)$
and $(-1, 1)$ in $\mathbb{Z}^2$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2. -/
public def bishopMoves : List (ℤ × ℤ) := [(1, 1), (-1, 1)]

/-- **Basic moves of the anassa.** The basic moves of the anassa are the two vectors $(0, 1)$
and $(1, 1)$ in $\mathbb{Z}^2$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 3. -/
public def anassaMoves : List (ℤ × ℤ) := [(0, 1), (1, 1)]

/-- **Nonattacking bishops on a square board.** For natural numbers $m$ and $k$, $B_S(m, k)$ is the
number of ways to place $k$ nonattacking bishops on the $m \times m$ board $S_m = [1, m]^2$, that
is, the number of $k$-element subsets of $S_m$ no two of whose squares lie on a common line of
slope $1$ or $-1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.1. -/
public def bishopsSquare (m k : ℕ) : ℕ :=
  (nonattackingPlacements (squareBoard m) bishopMoves k).card

/-- **Nonattacking bishops on the white squares.** For natural numbers $m$ and $k$, $R_W(m, k)$ is
the number of $k$-element sets of white squares of the $m \times m$ board $S_m = [1, m]^2$ (the
squares $(i, j)$ with $i + j$ even) no two of which lie on a common line of slope $1$ or $-1$, that
is, the number of ways to place $k$ nonattacking bishops on the white squares of $S_m$.

In the source, $R_W(m, k)$ counts placements of $k$ nonattacking rooks on the white board $W_m$,
whose rows and columns are the diagonals of the white squares of $S_m$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.2. -/
public def bishopsWhite (m k : ℕ) : ℕ :=
  (nonattackingPlacements (whiteSquares m) bishopMoves k).card

/-- **Nonattacking bishops on the black squares.** For natural numbers $m$ and $k$, $R_K(m, k)$ is
the number of $k$-element sets of black squares of the $m \times m$ board $S_m = [1, m]^2$ (the
squares $(i, j)$ with $i + j$ odd) no two of which lie on a common line of slope $1$ or $-1$, that
is, the number of ways to place $k$ nonattacking bishops on the black squares of $S_m$.

In the source, $R_K(m, k)$ counts placements of $k$ nonattacking rooks on the black board $K_m$,
whose rows and columns are the diagonals of the black squares of $S_m$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.2. -/
public def bishopsBlack (m k : ℕ) : ℕ :=
  (nonattackingPlacements (blackSquares m) bishopMoves k).card

/-- **Nonattacking anassas by number below the diagonal.** For natural numbers $m$, $k$ and
$p$, $A_S(m, k, p)$ is the number of nonattacking placements of $k$ anassas on the square board
$S_m = \{1, \dots, m\}^2$ (that is, of $k$-element sets of squares of $S_m$ no two of which lie
on a common line in the direction $(0, 1)$ or $(1, 1)$) in which exactly $p$ of the squares
$(i, j)$ satisfy $j < i$, that is, lie strictly below the main diagonal.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 3.1. -/
public def anassasBelow (m k p : ℕ) : ℕ :=
  ((nonattackingPlacements (squareBoard m) anassaMoves k).filter fun S =>
    (S.filter fun s => s.2 < s.1).card = p).card

/-- **Extended Stirling numbers of the second kind.** Knuth's extended Stirling number of the
second kind at integers $n$ and $k$ is the natural number equal to the Stirling number of the
second kind $S(n, k)$ if $n \ge 0$ and $k \ge 0$, equal to the unsigned Stirling number of the
first kind $c(-k, -n)$ if $n < 0$ and $k < 0$, and equal to $0$ otherwise. Here $c(j, i)$ is the
number of permutations of $j$ elements with exactly $i$ cycles.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1 (extended Stirling numbers,
with the identity `{-j, -k} = [k, j]`). -/
public def extStirlingSecond (n k : ℤ) : ℕ :=
  if 0 ≤ n ∧ 0 ≤ k then Nat.stirlingSecond n.toNat k.toNat
  else if n < 0 ∧ k < 0 then Nat.stirlingFirst (-k).toNat (-n).toNat
  else 0

/-- **Extended Stirling numbers at natural arguments.** For all natural numbers $n$ and $k$, the
extended Stirling number of the second kind at $(n, k)$ equals the Stirling number of the second
kind $S(n, k)$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public theorem extStirlingSecond_natCast (n k : ℕ) :
    extStirlingSecond n k = Nat.stirlingSecond n k := by
  simp [extStirlingSecond]

/-- **Extended Stirling numbers at negative arguments.** For all positive integers $a$ and $b$,
the extended Stirling number of the second kind at $(-a, -b)$ equals the unsigned Stirling number
of the first kind $c(b, a)$, the number of permutations of $b$ elements with exactly $a$ cycles.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, proof of Theorem 2.2. -/
public theorem extStirlingSecond_neg_neg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    extStirlingSecond (-(a : ℤ)) (-(b : ℤ)) = Nat.stirlingFirst b a := by
  simp [extStirlingSecond, ha, hb, ha.ne', hb.ne']

/-- **Santos's coefficients.** For natural numbers $i$, $p$, $q$ and a complex number $z$,
Santos's coefficient $\beta_i(p, q, z)$ is the complex number
$$
\beta_i(p, q, z) = 2^{-2q} \sum_{b=\max(0, i-p)}^{q} 2^b \binom{2q-b}{q}
\sum_{a=0}^{b} \binom{p+b-q-z}{a} \binom{q+z}{b-a} \binom{a-q}{p+b-i},
$$
where $\binom{w}{n} = w(w-1)\cdots(w-n+1)/n!$ for complex $w$ and natural $n$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 2.7, equation (9). -/
public noncomputable def santosBeta (i p q : ℕ) (z : ℂ) : ℂ :=
  1 / 2 ^ (2 * q) *
    ∑ b ∈ Icc (i - p) q, 2 ^ b * ((2 * q - b).choose q : ℂ) *
      ∑ a ∈ range (b + 1),
        Ring.choose ((p : ℂ) + b - q - z) a * Ring.choose ((q : ℂ) + z) (b - a) *
          Ring.choose ((a : ℂ) - q) (p + b - i)

/-- **Santos's coefficient with all indices zero.** For every complex number $z$, Santos's
coefficient satisfies $\beta_0(0, 0, z) = 1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 2.7. -/
public theorem santosBeta_zero (z : ℂ) : santosBeta 0 0 0 z = 1 := by
  simp [santosBeta]

/-- **Constituent coefficients for bishops on one color.** For natural numbers $k$, $d$ and a
complex number $z$, the constituent coefficient $c_{k,d}(z)$ is
$$c_{k,d}(z) = \sum_{i=d}^{2k} \frac{(-1)^{i-d}}{i!} {i \brack d}
\sum_{p=\max(0, i-k)}^{k} \sum_{j=p}^{k} S_2(p+j, p) \, \beta_i(p+j, k-j, z),$$
where ${i \brack d}$ is the unsigned Stirling number of the first kind, $S_2(n, r)$ is the
2-associated Stirling number of the second kind, and $\beta_i(p, q, z)$ is the coefficient
$\beta$ of Santos's Lemma 2.7.

Taking $z = -\pi(m)$ and $z = \pi(m)$, where $\pi(m) \in \{0, 1\}$ is the parity of $m$, gives
the coefficients of $m^d$ in the quasi-polynomials (13) and (14) for $k$ bishops on the white
and black squares.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.8. -/
public noncomputable def bishopColorQuasiCoeff (k d : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Icc d (2 * k), (-1) ^ (i - d) / (i.factorial : ℂ) * (Nat.stirlingFirst i d : ℂ) *
    ∑ p ∈ Icc (i - k) k, ∑ j ∈ Icc p k,
      (twoAssocStirlingSecond (p + j) p : ℂ) * santosBeta i (p + j) (k - j) z

/-- **Constituent coefficient for no bishops.** For every complex number $z$, the constituent
coefficient $c_{0,0}(z)$ of the bishop quasi-polynomials (the case $k = d = 0$) equals $1$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.8. -/
public theorem bishopColorQuasiCoeff_zero_zero (z : ℂ) : bishopColorQuasiCoeff 0 0 z = 1 := by
  simp [bishopColorQuasiCoeff, twoAssocStirlingSecond, santosBeta_zero]

end

namespace bishopsSquare_eq_sum

open Finset

-- A row is a diagonal of fixed coordinate sum. Its columns are indexed by half
-- the coordinate difference, rounded down. The color is 0 for white and 1 for black.
private def columns (c r : ℕ) : Finset ℤ :=
  Ico (-(((r : ℤ) + c) / 2)) (((r : ℤ) + c) / 2 + 1 - c)

private def rows (c m : ℕ) : Finset (ℕ × ℤ) :=
  (range m).biUnion fun r => (columns c r).image (Prod.mk r)

private theorem mem_rows {c m : ℕ} {p : ℕ × ℤ} :
    p ∈ rows c m ↔ p.1 < m ∧ p.2 ∈ columns c p.1 := by
  rcases p with ⟨r, t⟩
  simp [rows]

private def rooks (c m k : ℕ) : Finset (Finset (ℕ × ℤ)) :=
  ((rows c m).powersetCard k).filter fun s =>
    (∀ p ∈ s, ∀ q ∈ s, p.1 = q.1 → p = q) ∧
    (∀ p ∈ s, ∀ q ∈ s, p.2 = q.2 → p = q)

private theorem mem_rooks {c m k : ℕ} {s : Finset (ℕ × ℤ)} :
    s ∈ rooks c m k ↔ s ⊆ rows c m ∧ s.card = k ∧
      Set.InjOn Prod.fst (s : Set (ℕ × ℤ)) ∧ Set.InjOn Prod.snd (s : Set (ℕ × ℤ)) := by
  simp only [rooks, mem_filter, mem_powersetCard, and_assoc]
  rfl

private theorem columns_mono (c : ℕ) {r m : ℕ} (hr : r ≤ m) : columns c r ⊆ columns c m := by
  intro t ht
  obtain ⟨h₁, h₂⟩ := mem_Ico.mp ht
  apply mem_Ico.mpr
  constructor <;> omega

private theorem available_card {s : Finset (ℕ × ℤ)} {c m k : ℕ} (hs : s ∈ rooks c m k) :
    (columns c m \ s.image Prod.snd).card = (columns c m).card - k := by
  obtain ⟨h, hk, _, hi⟩ := mem_rooks.mp hs
  rw [card_sdiff_of_subset, card_image_of_injOn hi, hk]
  intro t ht
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
  obtain ⟨hr, ht⟩ := mem_rows.mp (h hp)
  exact columns_mono _ hr.le ht

private theorem insert_rook {s : Finset (ℕ × ℤ)} {c m k : ℕ} {t : ℤ}
    (hs : s ∈ rooks c m k) (ht : t ∈ columns c m \ s.image Prod.snd) :
    insert (m, t) s ∈ rooks c (m + 1) (k + 1) := by
  obtain ⟨hb, hk, hr, hd⟩ := mem_rooks.mp hs
  obtain ⟨hc, hf⟩ := mem_sdiff.mp ht
  have hm (p) (hp : p ∈ s) : p.1 < m := (mem_rows.mp (hb hp)).1
  have hn : (m, t) ∉ s := fun h => (Nat.lt_irrefl m) (hm _ h)
  refine mem_rooks.mpr ⟨?_, by simp [hn, hk], ?_, ?_⟩
  · intro p hp
    rcases mem_insert.mp hp with rfl | hs'
    · exact mem_rows.mpr ⟨by omega, hc⟩
    obtain ⟨h₁, h₂⟩ := mem_rows.mp (hb hs')
    exact mem_rows.mpr ⟨by omega, h₂⟩
  · intro p hp q hq he
    rcases mem_insert.mp hp with rfl | hp <;> rcases mem_insert.mp hq with rfl | hq
    · rfl
    · exact False.elim ((hm _ hq).ne he.symm)
    · exact False.elim ((hm _ hp).ne he)
    · exact hr hp hq he
  · intro p hp q hq he
    rcases mem_insert.mp hp with rfl | hp <;> rcases mem_insert.mp hq with rfl | hq
    · rfl
    · exact False.elim (hf (mem_image.mpr ⟨q, hq, he.symm⟩))
    · exact False.elim (hf (mem_image.mpr ⟨p, hp, he⟩))
    · exact hd hp hq he

-- Erasing the unique rook in the last row recovers the old placement and its free column.
private theorem rooks_step (c m k : ℕ) :
    (rooks c (m + 1) (k + 1)).card = (rooks c m (k + 1)).card +
      ((columns c m).card - k) * (rooks c m k).card := by
  classical
  let old := rooks c m (k + 1)
  let choices := (rooks c m k).sigma fun s => columns c m \ s.image Prod.snd
  have hm {s p} {j : ℕ} (hs : s ∈ rooks c m j) (hp : p ∈ s) : p.1 < m :=
    (mem_rows.mp ((mem_rooks.mp hs).1 hp)).1
  let assemble : Finset (ℕ × ℤ) ⊕ (Σ _ : Finset (ℕ × ℤ), ℤ) → Finset (ℕ × ℤ) :=
    Sum.elim id fun x => insert (m, x.2) x.1
  have hbij : (old.disjSum choices).card = (rooks c (m + 1) (k + 1)).card := by
    apply card_nbij assemble
    · intro a ha
      cases a with
      | inl s =>
        obtain ⟨hb, hk, hr, hd⟩ := mem_rooks.mp (inl_mem_disjSum.mp ha)
        refine mem_rooks.mpr ⟨?_, hk, hr, hd⟩
        intro p hp
        obtain ⟨h₁, h₂⟩ := mem_rows.mp (hb hp)
        exact mem_rows.mpr ⟨by omega, h₂⟩
      | inr a =>
        obtain ⟨hs, ht⟩ := mem_sigma.mp (inr_mem_disjSum.mp ha)
        exact insert_rook hs ht
    · intro a ha b hb he
      cases a with
      | inl s =>
        cases b with
        | inl z => exact congrArg Sum.inl he
        | inr z =>
          change s = insert (m, z.2) z.1 at he
          have hp : (m, z.2) ∈ s := he.symm ▸ mem_insert_self ..
          exact False.elim ((Nat.lt_irrefl m) (hm (inl_mem_disjSum.mp ha) hp))
      | inr x =>
        cases b with
        | inl s =>
          change insert (m, x.2) x.1 = s at he
          have hp : (m, x.2) ∈ s := he ▸ mem_insert_self ..
          exact False.elim ((Nat.lt_irrefl m) (hm (inl_mem_disjSum.mp hb) hp))
        | inr y =>
          obtain ⟨s, t⟩ := x
          obtain ⟨z, u⟩ := y
          change insert (m, t) s = insert (m, u) z at he
          have hs := (mem_sigma.mp (inr_mem_disjSum.mp ha)).1
          have hz := (mem_sigma.mp (inr_mem_disjSum.mp hb)).1
          have hp : (m, t) ∈ insert (m, u) z := he ▸ mem_insert_self ..
          rcases mem_insert.mp hp with h | hz'
          · obtain rfl : t = u := congrArg Prod.snd h
            have hn : (m, t) ∉ s := fun h => (Nat.lt_irrefl m) (hm hs h)
            have hn' : (m, t) ∉ z := fun h => (Nat.lt_irrefl m) (hm hz h)
            have := congrArg (fun v : Finset (ℕ × ℤ) => v.erase (m, t)) he
            have : s = z := by simpa [hn, hn'] using this
            subst z
            rfl
          · exact False.elim ((Nat.lt_irrefl m) (hm hz hz'))
    · intro s hs
      obtain ⟨hsub, hk, hr, hd⟩ := mem_rooks.mp hs
      by_cases h : ∃ t, (m, t) ∈ s
      · obtain ⟨t, ht⟩ := h
        let z := s.erase (m, t)
        have hz : z ∈ rooks c m k := by
          refine mem_rooks.mpr ⟨?_, by simp [z, card_erase_of_mem ht, hk],
            hr.mono (erase_subset ..), hd.mono (erase_subset ..)⟩
          intro p hp
          obtain ⟨hne, hp⟩ := mem_erase.mp hp
          obtain ⟨h₁, h₂⟩ := mem_rows.mp (hsub hp)
          have : p.1 ≠ m := fun h => hne (hr hp ht h)
          exact mem_rows.mpr ⟨by omega, h₂⟩
        have hf : t ∉ z.image Prod.snd := by
          intro h
          obtain ⟨p, hp, he⟩ := mem_image.mp h
          exact (mem_erase.mp hp).1 (hd (mem_erase.mp hp).2 ht he)
        refine ⟨.inr ⟨z, t⟩, inr_mem_disjSum.mpr (mem_sigma.mpr ⟨hz, mem_sdiff.mpr
          ⟨(mem_rows.mp (hsub ht)).2, hf⟩⟩), insert_erase ht⟩
      · refine ⟨.inl s, inl_mem_disjSum.mpr (mem_rooks.mpr ⟨?_, hk, hr, hd⟩), rfl⟩
        rintro ⟨r, t⟩ hp
        obtain ⟨h₁, h₂⟩ := mem_rows.mp (hsub hp)
        have : r ≠ m := fun e => h ⟨t, e ▸ hp⟩
        exact mem_rows.mpr ⟨by change r < m + 1 at h₁; omega, h₂⟩
  rw [← hbij, card_disjSum, card_sigma]
  congr 1
  rw [sum_congr rfl fun s hs => available_card hs]
  simp [mul_comm]

-- Shift the second argument to an integer so that the recurrence also covers
-- placements using more than the available number of rows.
private def weight (a m : ℕ) (d : ℤ) : ℕ :=
  ∑ i ∈ range (a + 1), a.choose i * extStirlingSecond ((m : ℤ) - i) d

private theorem stirling_step (n d : ℤ) (hn : 0 ≤ n) :
    extStirlingSecond (n + 1) d =
      d.toNat * extStirlingSecond n d + extStirlingSecond n (d - 1) := by
  lift n to ℕ using hn
  cases d with
  | negSucc z =>
    simp [extStirlingSecond]
    split_ifs <;> omega
  | ofNat d =>
    cases d with
    | zero => simp [extStirlingSecond, Int.toNat_add]
    | succ d =>
      simp [extStirlingSecond, Int.toNat_add, Nat.stirlingSecond_succ_succ]
      split_ifs <;> omega

private theorem weight_step {a m : ℕ} (ha : a ≤ m) (d : ℤ) :
    weight a (m + 1) d = d.toNat * weight a m d + weight a m (d - 1) := by
  simp only [weight, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [show ((m + 1 : ℕ) : ℤ) - i = ((m : ℤ) - i) + 1 by omega, stirling_step _ _ (by omega)]
  simp [mul_add, mul_left_comm]

private theorem weight_pascal (a m : ℕ) (d : ℤ) :
    weight (a + 1) (m + 1) d = weight a (m + 1) d + weight a m d := by
  simp only [weight]
  rw [sum_range_succ' (fun i => (a + 1).choose i * _) (a + 1)]
  simp only [Nat.choose_succ_succ, add_mul, sum_add_distrib]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, Nat.choose_zero_right, one_mul,
    add_sub_add_right_eq_sub]
  rw [sum_range_succ' (fun i => a.choose i * extStirlingSecond ((m : ℤ) + 1 - i) d) a]
  rw [sum_range_succ (fun i => a.choose (i + 1) * _) a]
  simp [add_comm, add_left_comm]

private theorem weight_neg {a m : ℕ} (ha : a ≤ m) {d : ℤ} (hd : d < 0) :
    weight a m d = 0 := by
  refine sum_eq_zero fun i hi => ?_
  have := mem_range.mp hi
  simp [extStirlingSecond, show ¬ 0 ≤ d by omega, show ¬ (m : ℤ) - i < 0 by omega]

private theorem weight_diag {a m : ℕ} (ha : a ≤ m) : weight a m m = 1 := by
  unfold weight
  rw [sum_eq_single 0]
  · simp [extStirlingSecond, Nat.stirlingSecond_self]
  · intro i hi hn
    have := mem_range.mp hi
    simp [extStirlingSecond, show i ≤ m by omega,
      Nat.stirlingSecond_eq_zero_of_lt (show m - i < m by omega)]
  · simp

-- The number of rows whose length exceeds their zero-based row index.
private def extra (c m : ℕ) := (m + 1 - c) / 2

private theorem rooks_weight (c : ℕ) (hc : c ≤ 1) (m k : ℕ) :
    (rooks c m k).card = weight (extra c m) m ((m : ℤ) - k) := by
  induction m generalizing k with
  | zero =>
    have he : extra c 0 = 0 := by unfold extra; omega
    cases k with
    | zero => simp [rooks, rows, weight, he, extStirlingSecond, filter_singleton]
    | succ k =>
      rw [weight_neg (by omega) (by omega)]
      simp [rooks, rows, powersetCard_eq_empty.mpr (show (∅ : Finset (ℕ × ℤ)).card < k + 1 by simp)]
  | succ m ih =>
    have ha : extra c m ≤ m := by unfold extra; omega
    have ha' : extra c (m + 1) ≤ m + 1 := by unfold extra; omega
    cases k with
    | zero =>
      rw [Nat.cast_zero, sub_zero, weight_diag ha']
      simp [rooks, filter_singleton]
    | succ k =>
      rw [rooks_step, ih, ih]
      simp only [Nat.cast_succ, add_sub_add_right_eq_sub]
      rw [show (m : ℤ) - (k + 1) = (m - k) - 1 by omega]
      have hcol : (columns c m).card = (2 * ((m + c) / 2) + 1 - c) := by
        simp only [columns, Int.card_Ico]
        omega
      rw [hcol]
      by_cases h : extra c (m + 1) = extra c m
      · rw [h, weight_step ha]
        have : 2 * ((m + c) / 2) + 1 - c - k = ((m : ℤ) - k).toNat := by
          unfold extra at h
          omega
        rw [this, add_comm]
      · have he : extra c (m + 1) = extra c m + 1 := by unfold extra at *; omega
        rw [he, weight_pascal, weight_step ha]
        by_cases hk : k ≤ m
        · have : 2 * ((m + c) / 2) + 1 - c - k = ((m : ℤ) - k).toNat + 1 := by
            unfold extra at he
            omega
          rw [this, add_mul, one_mul]
          omega
        · simp [weight_neg ha (show (m : ℤ) - k < 0 by omega)]

private theorem weight_sum {a m : ℕ} (ha : a ≤ m) (k : ℕ) :
    weight a m ((m : ℤ) - k) =
      ∑ i ∈ range (k + 1), a.choose i * extStirlingSecond ((m : ℤ) - i) ((m : ℤ) - k) := by
  unfold weight
  rcases le_total a k with h | h
  · apply sum_subset (range_mono (by omega))
    intro i _ hi
    simp only [mem_range] at hi
    simp [Nat.choose_eq_zero_of_lt (show a < i by omega)]
  · symm
    apply sum_subset (range_mono (by omega))
    intro i hi hn
    simp only [mem_range] at hi hn
    simp [extStirlingSecond, show i ≤ m by omega, show k ≤ m by omega,
      Nat.stirlingSecond_eq_zero_of_lt (show m - i < m - k by omega)]

private abbrev Square := ℤ × ℤ

private def rising (p : Square) := p.1 - p.2

private def falling (p : Square) := p.1 + p.2

private def color (p : Square) := falling p % 2

private def board (c m : ℕ) := (squareBoard m).filter fun p => color p = c

private def placements (b : Finset Square) (k : ℕ) := nonattackingPlacements b bishopMoves k

private theorem mem_placements {b : Finset Square} {s : Finset Square} {k : ℕ} :
    s ∈ placements b k ↔ s ⊆ b ∧ s.card = k ∧
      Set.InjOn rising (s : Set Square) ∧ Set.InjOn falling (s : Set Square) := by
  simp only [placements, nonattackingPlacements, mem_filter, mem_powersetCard, bishopMoves,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    mul_one, mul_neg, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h
    constructor
    · intro p hp q hq he
      by_contra hn
      have := (h p hp q hq hn).1
      unfold rising at he
      omega
    · intro p hp q hq he
      by_contra hn
      have := (h p hp q hq hn).2
      unfold falling at he
      omega
  · rintro ⟨hr, hf⟩ p hp q hq hn
    constructor
    · intro he
      exact hn (hr hp hq (by unfold rising; omega))
    · intro he
      exact hn (hf hp hq (by unfold falling; omega))

-- Read diagonals alternately from the two corners, in increasing order of length.
private def rowSum (c m r : ℕ) : ℤ :=
  if r % 2 = c then (r : ℤ) + 2 else 2 * m + 1 - r

private def decode (c m : ℕ) (p : ℕ × ℤ) : Square :=
  (((rowSum c m p.1 + c) / 2) + p.2, ((rowSum c m p.1 - c) / 2) - p.2)

private theorem rowSum_inj {c m r s : ℕ} (hr : r < m) (hs : s < m)
    (h : rowSum c m r = rowSum c m s) : r = s := by
  unfold rowSum at h
  split_ifs at h <;> omega

private theorem decode_diags {c : ℕ} (hc : c ≤ 1) (m : ℕ) (p : ℕ × ℤ) :
    falling (decode c m p) = rowSum c m p.1 ∧ rising (decode c m p) = 2 * p.2 + c := by
  rcases p with ⟨r, t⟩
  simp only [decode, falling, rising, rowSum]
  split_ifs <;> constructor <;> omega

private theorem image_board {c : ℕ} (hc : c ≤ 1) (m : ℕ) :
    (rows c m).image (decode c m) = board c m := by
  apply Finset.ext
  rintro ⟨x, y⟩
  rw [mem_image, show ((x, y) ∈ board c m) ↔ _ from mem_filter]
  change _ ↔ (x, y) ∈ Icc (1 : ℤ) m ×ˢ Icc (1 : ℤ) m ∧ (x + y) % 2 = c
  rw [mem_product, mem_Icc, mem_Icc]
  constructor
  · rintro ⟨⟨r, t⟩, h, he⟩
    obtain ⟨hr, ht⟩ := mem_rows.mp h
    obtain ⟨hl, hu⟩ := mem_Ico.mp ht
    change -(((r : ℤ) + c) / 2) ≤ t at hl
    change t < ((r : ℤ) + c) / 2 + 1 - c at hu
    change r < m at hr
    simp only [decode, rowSum, Prod.mk.injEq] at he
    split_ifs at he <;> exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
  · rintro ⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, hcol⟩
    let r : ℕ := (if x + y ≤ m + 1 then x + y - 2 else 2 * (m : ℤ) + 1 - x - y).toNat
    let t := (x - y) / 2
    have hr : r < m := by dsimp [r]; split <;> omega
    have hsum : rowSum c m r = x + y := by
      dsimp [rowSum, r]
      split_ifs <;> omega
    refine ⟨⟨r, t⟩, mem_rows.mpr ⟨hr, mem_Ico.mpr ?_⟩, ?_⟩
    · change -(((r : ℤ) + c) / 2) ≤ t ∧ t < ((r : ℤ) + c) / 2 + 1 - c
      dsimp [r, t]
      split_ifs <;> constructor <;> omega
    · simp only [decode, hsum, Prod.mk.injEq, t]
      constructor <;> omega

private theorem injOn_image_iff {α β γ δ : Type*} [DecidableEq β]
    {f : α → β} {s : Finset α} (hf : Set.InjOn f (s : Set α)) {g : β → γ} {h : α → δ}
    (he : ∀ p ∈ s, ∀ q ∈ s, g (f p) = g (f q) ↔ h p = h q) :
    Set.InjOn g (s.image f : Set β) ↔ Set.InjOn h (s : Set α) := by
  constructor
  · intro hi p hp q hq eq
    exact hf hp hq (hi (mem_image_of_mem _ hp) (mem_image_of_mem _ hq) ((he _ hp _ hq).2 eq))
  · intro hi x hx y hy eq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hy
    exact congrArg f (hi hp hq ((he _ hp _ hq).1 eq))

private theorem color_count {c : ℕ} (hc : c ≤ 1) (m k : ℕ) :
    (placements (board c m) k).card = (rooks c m k).card := by
  have hf {p q : ℕ × ℤ} (hp : p ∈ rows c m) (hq : q ∈ rows c m) :
      falling (decode c m p) = falling (decode c m q) ↔ p.1 = q.1 := by
    rw [(decode_diags hc m p).1, (decode_diags hc m q).1]
    exact ⟨rowSum_inj (mem_rows.mp hp).1 (mem_rows.mp hq).1, congrArg _⟩
  have hr (p q : ℕ × ℤ) : rising (decode c m p) = rising (decode c m q) ↔ p.2 = q.2 := by
    rw [(decode_diags hc m p).2, (decode_diags hc m q).2]
    omega
  have hi : Set.InjOn (decode c m) (rows c m : Set (ℕ × ℤ)) := by
    intro p hp q hq he
    exact Prod.ext ((hf hp hq).1 (congrArg falling he)) ((hr p q).1 (congrArg rising he))
  have he {s : Finset (ℕ × ℤ)} (hs : s ⊆ rows c m) :
      s.image (decode c m) ∈ placements (board c m) k ↔ s ∈ rooks c m k := by
    have hb : s.image (decode c m) ⊆ board c m := image_board hc m ▸ image_subset_image hs
    rw [mem_placements, mem_rooks, and_iff_right hb, and_iff_right hs,
      card_image_of_injOn (hi.mono hs), injOn_image_iff (hi.mono hs) (fun p _ q _ => hr p q),
      injOn_image_iff (hi.mono hs) (fun _ hp _ hq => hf (hs hp) (hs hq))]
    rw [and_comm (a := Set.InjOn Prod.snd _)]
  symm
  apply card_nbij (image (decode c m))
  · intro s hs
    exact (he (mem_rooks.mp hs).1).2 hs
  · intro s hs t ht h
    exact (image_eq_image_iff_of_injOn hi (mem_rooks.mp hs).1 (mem_rooks.mp ht).1).1 h
  · intro t ht
    have hb := (mem_placements.mp ht).1
    rw [← image_board hc m, subset_image_iff] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    exact ⟨s, (he hs).1 ht, rfl⟩

-- The two colors can be combined freely: both diagonal coordinates determine the color.
private def part (c : ℕ) (s : Finset Square) := s.filter fun p => color p = c

private theorem parts_union (s : Finset Square) : part 1 s ∪ part 0 s = s := by
  ext p
  simp only [mem_union, part, mem_filter, color, Nat.cast_one, Nat.cast_zero]
  by_cases hp : p ∈ s <;> simp [hp]
  omega

private theorem colored {c m k : ℕ} {s : Finset Square} (h : s ∈ placements (board c m) k)
    {p : Square} (hp : p ∈ s) : color p = c :=
  (mem_filter.mp ((mem_placements.mp h).1 hp)).2

private theorem restrict_color {s : Finset Square} {m k : ℕ}
    (h : s ∈ placements (squareBoard m) k) (c : ℕ) :
    part c s ∈ placements (board c m) (part c s).card := by
  obtain ⟨hs, _, hr, hf⟩ := mem_placements.mp h
  exact mem_placements.mpr ⟨filter_subset_filter _ hs, rfl,
    hr.mono (filter_subset ..), hf.mono (filter_subset ..)⟩

private theorem disjoint_colors {s t : Finset Square} {m i j : ℕ}
    (hs : s ∈ placements (board 1 m) i) (ht : t ∈ placements (board 0 m) j) :
    Disjoint s t := by
  apply disjoint_left.mpr
  intro p hp hq
  have := colored hs hp
  have := colored ht hq
  omega

private theorem recover_colors {s t : Finset Square} {m i j : ℕ}
    (hs : s ∈ placements (board 1 m) i) (ht : t ∈ placements (board 0 m) j) :
    part 1 (s ∪ t) = s ∧ part 0 (s ∪ t) = t := by
  have hb (p) (hp : p ∈ s) := colored hs hp
  have hw (p) (hp : p ∈ t) := colored ht hp
  constructor <;> ext p <;> simp only [part, mem_filter, mem_union, Nat.cast_one, Nat.cast_zero]
  all_goals
    specialize hb p
    specialize hw p
    simp only [Nat.cast_one, Nat.cast_zero] at hb hw
    grind

private theorem combine_colors {s t : Finset Square} {m i j : ℕ}
    (hs : s ∈ placements (board 1 m) i) (ht : t ∈ placements (board 0 m) j) :
    s ∪ t ∈ placements (squareBoard m) (i + j) := by
  have hd := disjoint_colors hs ht
  obtain ⟨hsb, hsc, hsr, hsf⟩ := mem_placements.mp hs
  obtain ⟨htb, htc, htr, htf⟩ := mem_placements.mp ht
  refine mem_placements.mpr ⟨union_subset (hsb.trans (filter_subset ..))
    (htb.trans (filter_subset ..)), by rw [card_union_of_disjoint hd, hsc, htc], ?_, ?_⟩
  all_goals rw [coe_union, Set.injOn_union (Finset.disjoint_coe.mpr hd)]
  · refine ⟨hsr, htr, ?_⟩
    intro p hp q hq he
    have h₁ := colored hs hp
    have h₂ := colored ht hq
    unfold color falling at h₁ h₂
    unfold rising at he
    omega
  · refine ⟨hsf, htf, ?_⟩
    intro p hp q hq he
    have h₁ := colored hs hp
    have h₂ := colored ht hq
    unfold color at h₁ h₂
    omega

private theorem convolution (m k : ℕ) :
    bishopsSquare m k =
      ∑ j ∈ range (k + 1),
        (placements (board 1 m) j).card * (placements (board 0 m) (k - j)).card := by
  change (placements (squareBoard m) k).card = _
  let count := fun s : Finset Square => (part 1 s).card
  rw [card_eq_sum_card_fiberwise (f := count) (t := range (k + 1)) (by
    intro s hs
    have hb : (part 1 s).card ≤ s.card := card_le_card (filter_subset ..)
    exact mem_range.mpr ((hb.trans_eq (mem_placements.mp hs).2.1).trans_lt k.lt_succ_self))]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  rw [← card_product]
  symm
  apply card_nbij (fun st : Finset Square × Finset Square => st.1 ∪ st.2)
  · intro st h
    obtain ⟨hs, ht⟩ := mem_product.mp h
    exact mem_filter.mpr ⟨(show j + (k - j) = k by omega) ▸ combine_colors hs ht,
      (congrArg card (recover_colors hs ht).1).trans (mem_placements.mp hs).2.1⟩
  · intro a ha b hb he
    obtain ⟨has, hat⟩ := mem_product.mp ha
    obtain ⟨hbs, hbt⟩ := mem_product.mp hb
    obtain ⟨ha₁, ha₂⟩ := recover_colors has hat
    obtain ⟨hb₁, hb₂⟩ := recover_colors hbs hbt
    exact Prod.ext (ha₁.symm.trans ((congrArg (part 1) he).trans hb₁))
      (ha₂.symm.trans ((congrArg (part 0) he).trans hb₂))
  · intro s hs
    obtain ⟨h, he⟩ := mem_filter.mp hs
    have hb := restrict_color h 1
    have hw := restrict_color h 0
    have hk := (mem_placements.mp h).2.1
    have hu := congrArg card (parts_union s)
    rw [card_union_of_disjoint (disjoint_colors hb hw)] at hu
    change (part 1 s).card = j at he
    have hw' : (part 0 s).card = k - j := by omega
    exact ⟨(part 1 s, part 0 s), mem_product.mpr ⟨he ▸ hb, hw' ▸ hw⟩, parts_union s⟩

end bishopsSquare_eq_sum

open Finset bishopsSquare_eq_sum

/-- **Extended Stirling formula for bishops on a square board.** For all natural numbers $m$ and
$k$, the number $B_S(m, k)$ of placements of $k$ nonattacking bishops on the $m \times m$ board
satisfies

$$
B_S(m, k) = \sum_{j=0}^{k} \sum_{i=0}^{j} \binom{\lfloor m/2 \rfloor}{i} S(m - i, m - j)
\sum_{l=0}^{k-j} \binom{\lceil m/2 \rceil}{l} S(m - l, m - k + j),
$$

where $S(a, b)$ is Knuth's extended Stirling number of the second kind for integers $a, b$: the
Stirling number of the second kind when $a, b \ge 0$, the unsigned Stirling number of the first
kind with arguments $-b, -a$ when $a, b < 0$, and $0$ otherwise.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 6 (`jis-2025-25.8.6-thm-6`). -/
public theorem bishopsSquare_eq_sum (m k : ℕ) :
    bishopsSquare m k =
      ∑ j ∈ range (k + 1), ∑ i ∈ range (j + 1),
        (m / 2).choose i * extStirlingSecond ((m : ℤ) - i) ((m : ℤ) - j) *
          ∑ l ∈ range (k - j + 1),
            ((m + 1) / 2).choose l * extStirlingSecond ((m : ℤ) - l) ((m : ℤ) - k + j) := by
  rw [convolution]
  refine sum_congr rfl fun j hj => ?_
  have h := mem_range.mp hj
  rw [color_count (by decide : 1 ≤ 1), color_count (by decide : 0 ≤ 1),
    rooks_weight _ (by decide), rooks_weight _ (by decide),
    weight_sum (by unfold extra; omega), weight_sum (by unfold extra; omega), sum_mul]
  simp only [extra, Nat.add_sub_cancel, Nat.sub_zero]
  rw [show (m : ℤ) - (k - j : ℕ) = m - k + j by omega]

end MetaMathlibExt
