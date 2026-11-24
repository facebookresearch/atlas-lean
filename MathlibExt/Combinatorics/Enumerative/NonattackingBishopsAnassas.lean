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

namespace AnassaRooks

open scoped Classical

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

private noncomputable def rooks (b : Finset (α × β)) (mark : α × β → Prop) (k p : ℕ) :
    Finset (Finset (α × β)) :=
  (b.powersetCard k).filter fun s =>
    Set.InjOn Prod.fst (s : Set (α × β)) ∧ Set.InjOn Prod.snd (s : Set (α × β)) ∧
      (s.filter mark).card = p

private theorem mem_rooks {b s : Finset (α × β)} {mark : α × β → Prop} {k p : ℕ} :
    s ∈ rooks b mark k p ↔ s ⊆ b ∧ s.card = k ∧ Set.InjOn Prod.fst (s : Set (α × β)) ∧
      Set.InjOn Prod.snd (s : Set (α × β)) ∧ (s.filter mark).card = p := by
  simp only [rooks, mem_filter, mem_powersetCard, and_assoc]

private theorem card_filter_insert_rook (mark : α × β → Prop) {s : Finset (α × β)}
    {x : α × β} (hx : x ∉ s) :
    ((insert x s).filter mark).card = (s.filter mark).card + (if mark x then 1 else 0) := by
  by_cases hm : mark x <;> simp [filter_insert, hm, hx]

private theorem injOn_insert_rook {γ : Type*} {f : α × β → γ} {s : Finset (α × β)}
    {x : α × β} (hi : Set.InjOn f (s : Set (α × β)))
    (hf : ∀ y ∈ s, f y ≠ f x) : Set.InjOn f (↑(insert x s) : Set (α × β)) := by
  intro a ha b hb h
  change a ∈ insert x s at ha
  change b ∈ insert x s at hb
  rcases mem_insert.mp ha with rfl | ha' <;> rcases mem_insert.mp hb with rfl | hb'
  · rfl
  · exact (hf _ hb' h.symm).elim
  · exact (hf _ ha' h).elim
  · exact hi ha' hb' h

-- A placement either avoids the new row or comes from inserting a rook in a free column.
private theorem rook_step (b : Finset (α × β)) (mark : α × β → Prop) (r : α)
    (cols : Finset β) (k p d c : ℕ) (fresh : ∀ x ∈ b, x.1 ≠ r)
    (hmark : ∀ y ∈ cols, (if mark (r, y) then 1 else 0) = d)
    (havail : ∀ s ∈ rooks b mark k p, (cols \ s.image Prod.snd).card = c) :
    (rooks (b ∪ cols.image (Prod.mk r)) mark (k + 1) (p + d)).card =
      (rooks b mark (k + 1) (p + d)).card + c * (rooks b mark k p).card := by
  let old := rooks b mark (k + 1) (p + d)
  let choices := (rooks b mark k p).sigma fun s => cols \ s.image Prod.snd
  let assemble : Finset (α × β) ⊕ (Σ _ : Finset (α × β), β) → Finset (α × β) :=
    Sum.elim id fun x => insert (r, x.2) x.1
  have hrow {s : Finset (α × β)} {j q : ℕ} (hs : s ∈ rooks b mark j q) {x : α × β}
      (hx : x ∈ s) : x.1 ≠ r := fresh x ((mem_rooks.mp hs).1 hx)
  have hcol {x : α × β} (hx : x ∈ cols.image (Prod.mk r)) : x.1 = r ∧ x.2 ∈ cols := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
    exact ⟨rfl, ht⟩
  have hbij : (old.disjSum choices).card =
      (rooks (b ∪ cols.image (Prod.mk r)) mark (k + 1) (p + d)).card := by
    apply card_nbij assemble
    · intro a ha
      cases a with
      | inl s =>
        obtain ⟨hb, hs, hr, hc, hp⟩ := mem_rooks.mp (inl_mem_disjSum.mp ha)
        exact mem_rooks.mpr ⟨fun x hx => mem_union_left _ (hb hx), hs, hr, hc, hp⟩
      | inr a =>
        obtain ⟨s, t⟩ := a
        obtain ⟨hs, ht⟩ := mem_sigma.mp (inr_mem_disjSum.mp ha)
        obtain ⟨hb, hk, hr, hc, hp⟩ := mem_rooks.mp hs
        obtain ⟨ht, hf⟩ := mem_sdiff.mp ht
        have hn : (r, t) ∉ s := fun h => hrow hs h rfl
        refine mem_rooks.mpr ⟨?_, by simp [assemble, hn, hk],
          injOn_insert_rook hr (fun _ hx => hrow hs hx),
          injOn_insert_rook hc (fun x hx he => hf (mem_image.mpr ⟨x, hx, he⟩)), ?_⟩
        · intro x hx
          rcases mem_insert.mp hx with rfl | hx
          · exact mem_union_right _ (mem_image.mpr ⟨t, ht, rfl⟩)
          · exact mem_union_left _ (hb hx)
        · change ((insert (r, t) s).filter mark).card = p + d
          rw [card_filter_insert_rook mark hn, hp, hmark _ ht]
    · intro a ha e he h
      cases a with
      | inl s =>
        cases e with
        | inl z => exact congrArg Sum.inl h
        | inr z =>
          change s = insert (r, z.2) z.1 at h
          have hx : (r, z.2) ∈ s := h.symm ▸ mem_insert_self ..
          exact (hrow (inl_mem_disjSum.mp ha) hx rfl).elim
      | inr a =>
        cases e with
        | inl z =>
          change insert (r, a.2) a.1 = z at h
          have hx : (r, a.2) ∈ z := h ▸ mem_insert_self ..
          exact (hrow (inl_mem_disjSum.mp he) hx rfl).elim
        | inr e =>
          obtain ⟨s, t⟩ := a
          obtain ⟨z, u⟩ := e
          change insert (r, t) s = insert (r, u) z at h
          have hs := (mem_sigma.mp (inr_mem_disjSum.mp ha)).1
          have hz := (mem_sigma.mp (inr_mem_disjSum.mp he)).1
          have hx : (r, t) ∈ insert (r, u) z := h ▸ mem_insert_self ..
          rcases mem_insert.mp hx with heq | hx
          · obtain rfl : t = u := congrArg Prod.snd heq
            have hn : (r, t) ∉ s := fun hx => hrow hs hx rfl
            have hn' : (r, t) ∉ z := fun hx => hrow hz hx rfl
            have herase := congrArg (fun v : Finset (α × β) => v.erase (r, t)) h
            have : s = z := by simpa [hn, hn'] using herase
            subst z
            rfl
          · exact (hrow hz hx rfl).elim
    · intro s hs
      obtain ⟨hb, hk, hr, hc, hp⟩ := mem_rooks.mp hs
      by_cases h : ∃ t, (r, t) ∈ s
      · obtain ⟨t, ht⟩ := h
        let z := s.erase (r, t)
        have htcol : t ∈ cols := by
          rcases mem_union.mp (hb ht) with ht' | ht'
          · exact (fresh _ ht' rfl).elim
          · exact (hcol ht').2
        have hz : z ∈ rooks b mark k p := by
          refine mem_rooks.mpr ⟨?_, by simp [z, card_erase_of_mem ht, hk],
            hr.mono (erase_subset ..), hc.mono (erase_subset ..), ?_⟩
          · intro x hx
            obtain ⟨hne, hx⟩ := mem_erase.mp hx
            rcases mem_union.mp (hb hx) with hx' | hx'
            · exact hx'
            · exact (hne (hr hx ht (hcol hx').1)).elim
          · have hn : (r, t) ∉ z := fun hx => (mem_erase.mp hx).1 rfl
            have hcount := card_filter_insert_rook mark hn
            rw [show insert (r, t) z = s from insert_erase ht, hp, hmark _ htcol] at hcount
            exact Nat.add_right_cancel hcount.symm
        have hf : t ∉ z.image Prod.snd := by
          intro hf
          obtain ⟨x, hx, he⟩ := mem_image.mp hf
          exact (mem_erase.mp hx).1 (hc (mem_erase.mp hx).2 ht he)
        exact ⟨.inr ⟨z, t⟩, inr_mem_disjSum.mpr
          (mem_sigma.mpr ⟨hz, mem_sdiff.mpr ⟨htcol, hf⟩⟩), insert_erase ht⟩
      · refine ⟨.inl s, inl_mem_disjSum.mpr (mem_rooks.mpr ⟨?_, hk, hr, hc, hp⟩), rfl⟩
        rintro ⟨x, t⟩ hx
        rcases mem_union.mp (hb hx) with hx' | hx'
        · exact hx'
        · have he : x = r := (hcol hx').1
          exact (h ⟨t, he ▸ hx⟩).elim
  rw [← hbij, card_disjSum, card_sigma]
  congr 1
  rw [sum_congr rfl fun s hs => havail s hs]
  simp [mul_comm]

private theorem image_swap_image (s : Finset (α × β)) :
    (s.image Prod.swap).image Prod.swap = s := by
  simp [image_image, Function.comp_def]

private theorem mem_rooks_swap {b s : Finset (α × β)} {mark : α × β → Prop} {k p : ℕ}
    (hs : s ∈ rooks b mark k p) :
    s.image Prod.swap ∈ rooks (b.image Prod.swap) (fun x => mark x.swap) k p := by
  obtain ⟨hb, hk, hr, hc, hp⟩ := mem_rooks.mp hs
  refine mem_rooks.mpr ⟨image_subset_image hb, ?_, ?_, ?_, ?_⟩
  · rwa [card_image_of_injective _ Prod.swap_injective]
  · intro x hx y hy he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact congrArg Prod.swap (hc ha hb he)
  · intro x hx y hy he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact congrArg Prod.swap (hr ha hb he)
  · simpa only [filter_image, Prod.swap_swap, card_image_of_injective _ Prod.swap_injective]
      using hp

-- Transposing exchanges row- and column-injectivity without changing the number of tags.
private theorem rooks_swap (b : Finset (α × β)) (mark : α × β → Prop) (k p : ℕ) :
    (rooks (b.image Prod.swap) (fun x => mark x.swap) k p).card =
      (rooks b mark k p).card := by
  symm
  apply card_nbij (fun s => s.image Prod.swap)
  · exact fun _ hs => mem_rooks_swap hs
  · intro s _ t _ h
    simpa only [image_swap_image] using congrArg (fun z : Finset (β × α) => z.image Prod.swap) h
  · intro s hs
    refine ⟨s.image Prod.swap, ?_, image_swap_image s⟩
    change s.image Prod.swap ∈ rooks b mark k p
    simpa only [image_swap_image, Prod.swap_swap] using mem_rooks_swap hs

-- A column is an anassa diagonal: retain the positive differences, and label
-- nonpositive differences from the other end of the square. The two signs are
-- disjoint, and the labels of the old columns do not change in the rook board.
private abbrev Cell := ℤ × ℤ
private def below (x : Cell) : Prop := 0 < x.2

private def board (m : ℕ) : Finset Cell :=
  (Icc 1 (m : ℤ) ×ˢ Icc (-(m : ℤ)) (m : ℤ)).filter fun x =>
    (0 < x.2 ∧ x.2 < x.1) ∨ x.2 ≤ -x.1

private theorem mem_board {m : ℕ} {x : Cell} :
    x ∈ board m ↔ 1 ≤ x.1 ∧ x.1 ≤ (m : ℤ) ∧
      ((1 ≤ x.2 ∧ x.2 < x.1) ∨ (-(m : ℤ) ≤ x.2 ∧ x.2 ≤ -x.1)) := by
  simp only [board, mem_filter, mem_product, mem_Icc]
  omega

private def encode (m : ℕ) (x : Cell) : Cell :=
  let d := x.1 - x.2
  (x.1, if 0 < d then d else -((m : ℤ) + d))

private noncomputable def decode (m : ℕ) (x : Cell) : Cell :=
  (x.1, if below x then x.1 - x.2 else (m : ℤ) + x.1 + x.2)

private theorem mem_square {m : ℕ} {x : Cell} :
    x ∈ squareBoard m ↔ 1 ≤ x.1 ∧ x.1 ≤ (m : ℤ) ∧ 1 ≤ x.2 ∧ x.2 ≤ (m : ℤ) := by
  simp [squareBoard, and_assoc]

private theorem encode_below {m : ℕ} {x : Cell} (hx : x ∈ squareBoard m) :
    below (encode m x) ↔ x.2 < x.1 := by
  obtain ⟨_, _, _, _⟩ := mem_square.mp hx
  simp only [below, encode]
  split <;> omega

private theorem encode_mem {m : ℕ} {x : Cell} (hx : x ∈ squareBoard m) :
    encode m x ∈ board m := by
  obtain ⟨_, _, _, _⟩ := mem_square.mp hx
  simp only [mem_board, encode]
  split <;> omega

private theorem decode_mem {m : ℕ} {x : Cell} (hx : x ∈ board m) :
    decode m x ∈ squareBoard m := by
  obtain ⟨_, _, h⟩ := mem_board.mp hx
  simp only [mem_square, decode, below]
  split_ifs <;> omega

private theorem encode_decode {m : ℕ} {x : Cell} (hx : x ∈ board m) :
    encode m (decode m x) = x := by
  obtain ⟨_, _, _⟩ := mem_board.mp hx
  refine Prod.ext (show (encode m (decode m x)).1 = x.1 from rfl) ?_
  simp only [encode, decode, below]
  split_ifs <;> omega

private theorem encode_snd {m : ℕ} {x y : Cell} (hx : x ∈ squareBoard m)
    (hy : y ∈ squareBoard m) :
    (encode m x).2 = (encode m y).2 ↔ x.1 - x.2 = y.1 - y.2 := by
  obtain ⟨_, _, _, _⟩ := mem_square.mp hx
  obtain ⟨_, _, _, _⟩ := mem_square.mp hy
  simp only [encode]
  split_ifs <;> omega

private theorem encode_inj {m : ℕ} : Set.InjOn (encode m) (squareBoard m : Set Cell) := by
  intro x hx y hy he
  have h₁ := congrArg Prod.fst he
  change x.1 = y.1 at h₁
  have h₂ := (encode_snd hx hy).mp (congrArg Prod.snd he)
  exact Prod.ext h₁ (by omega)

private theorem encode_image (m : ℕ) : (squareBoard m).image (encode m) = board m := by
  ext x
  rw [mem_image]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ encode_mem hy,
    fun h => ⟨decode m x, decode_mem h, encode_decode h⟩⟩

private theorem mem_anassas {m k p : ℕ} {s : Finset Cell} :
    s ∈ (nonattackingPlacements (squareBoard m) anassaMoves k).filter
        (fun S => (S.filter fun x => x.2 < x.1).card = p) ↔
      s ⊆ squareBoard m ∧ s.card = k ∧
      Set.InjOn Prod.fst (s : Set Cell) ∧ Set.InjOn (fun x => x.1 - x.2) (s : Set Cell) ∧
      (s.filter fun x => x.2 < x.1).card = p := by
  simp only [nonattackingPlacements, mem_filter, mem_powersetCard, anassaMoves,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    mul_one, mul_zero, and_assoc]
  rw [← and_assoc (a := Set.InjOn Prod.fst (s : Set Cell))]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_left' ?_
  constructor
  · intro h
    constructor
    · intro x hx y hy he
      by_contra hn
      exact (h x hx y hy hn).1 (by omega)
    · intro x hx y hy he
      by_contra hn
      change x.1 - x.2 = y.1 - y.2 at he
      exact (h x hx y hy hn).2 (by omega)
  · rintro ⟨h₁, h₂⟩ x hx y hy hn
    refine ⟨fun h => hn (h₁ hx hy (by omega)), fun h => hn (h₂ hx hy ?_)⟩
    change x.1 - x.2 = y.1 - y.2
    omega

private theorem card_filter_image {α β : Type*} [DecidableEq β]
    {f : α → β} {s : Finset α} (hf : Set.InjOn f (s : Set α))
    {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ x ∈ s, q (f x) ↔ p x) : ((s.image f).filter q).card = (s.filter p).card := by
  rw [filter_image, card_image_of_injOn (hf.mono (filter_subset ..))]
  congr 1
  exact filter_congr h

private theorem anassas_eq_rooks (m k p : ℕ) :
    anassasBelow m k p = (rooks (board m) below k p).card := by
  have he {s : Finset Cell} (hs : s ⊆ squareBoard m) :
      s.image (encode m) ∈ rooks (board m) below k p ↔
        s ∈ (nonattackingPlacements (squareBoard m) anassaMoves k).filter
          (fun S => (S.filter fun x => x.2 < x.1).card = p) := by
    have hb : s.image (encode m) ⊆ board m := encode_image m ▸ image_subset_image hs
    have hi := encode_inj.mono hs
    rw [mem_rooks, mem_anassas, and_iff_right hb, and_iff_right hs,
      card_image_of_injOn hi,
      bishopsSquare_eq_sum.injOn_image_iff hi (g := Prod.fst) (h := Prod.fst)
        (fun _ _ _ _ => Iff.rfl),
      bishopsSquare_eq_sum.injOn_image_iff hi (fun _ hx _ hy => encode_snd (hs hx) (hs hy)),
      card_filter_image hi (fun _ hx => encode_below (hs hx))]
  unfold anassasBelow
  apply card_nbij (image (encode m))
  · intro s hs
    exact (he (mem_anassas.mp hs).1).2 hs
  · intro s hs t ht h
    exact (image_eq_image_iff_of_injOn encode_inj
      (mem_anassas.mp hs).1 (mem_anassas.mp ht).1).mp h
  · intro t ht
    have hb := (mem_rooks.mp ht).1
    rw [← encode_image m, subset_image_iff] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    exact ⟨s, (he hs).1 ht, rfl⟩

-- The added positive row comes first, and then the new negative column,
-- which meets every row including the new one.
private def indices (m : ℕ) : Finset ℤ := Icc 1 (m : ℤ)

private def withRow (m : ℕ) : Finset Cell :=
  board m ∪ (indices m).image (Prod.mk ((m : ℤ) + 1))

private def withCol (b : Finset Cell) (m : ℕ) : Finset Cell :=
  b ∪ (indices (m + 1)).image (fun x => (x, -((m : ℤ) + 1)))

private theorem mem_withRow {m : ℕ} {x : Cell} :
    x ∈ withRow m ↔ x ∈ board m ∨
      (x.1 = (m : ℤ) + 1 ∧ x.2 ∈ indices m) := by
  rcases x with ⟨i, j⟩
  simp [withRow, mem_image, Prod.mk.injEq, eq_comm, and_comm]

private theorem mem_withCol {b : Finset Cell} {m : ℕ} {x : Cell} :
    x ∈ withCol b m ↔ x ∈ b ∨
      (x.1 ∈ indices (m + 1) ∧ x.2 = -((m : ℤ) + 1)) := by
  rcases x with ⟨i, j⟩
  simp [withCol, mem_image, Prod.mk.injEq, eq_comm]

private theorem board_succ (m : ℕ) : board (m + 1) = withCol (withRow m) m := by
  ext x
  simp only [mem_withCol, mem_withRow, mem_board, indices, mem_Icc, Nat.cast_add, Nat.cast_one]
  omega

private noncomputable def upper (m : ℕ) : Finset Cell := (board m).filter (fun x => ¬ below x)

private theorem mem_upper {m : ℕ} {x : Cell} :
    x ∈ upper m ↔ 1 ≤ x.1 ∧ -(m : ℤ) ≤ x.2 ∧ x.2 ≤ -x.1 := by
  simp [upper, below, mem_board]
  omega

private theorem upper_succ (m : ℕ) : upper (m + 1) = withCol (upper m) m := by
  ext x
  simp only [mem_withCol, mem_upper, indices, mem_Icc, Nat.cast_add, Nat.cast_one]
  omega

private theorem card_indices (m : ℕ) : (indices m).card = m := by
  simp [indices, Int.card_Icc]

private theorem rooks_empty (k p : ℕ) :
    (rooks (∅ : Finset Cell) below k p).card = (if k = 0 ∧ p = 0 then 1 else 0) := by
  have : rooks (∅ : Finset Cell) below k p = if k = 0 ∧ p = 0 then {∅} else ∅ := by
    ext s
    rw [mem_rooks]
    simp only [subset_empty]
    by_cases h : k = 0 ∧ p = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [show (if 0 = 0 ∧ 0 = 0 then ({∅} : Finset (Finset Cell)) else ∅) = {∅} by simp]
      exact ⟨fun hs => mem_singleton.mpr hs.1, by intro hs; obtain rfl := mem_singleton.mp hs; simp⟩
    · simp only [ite_eq_right h, notMem_empty, iff_false]
      rintro ⟨rfl, hk, _, _, hp⟩
      exact h ⟨by simpa using hk.symm, by simpa using hp.symm⟩
  rw [this]
  split <;> simp

private theorem rooks_zero (b : Finset Cell) (p : ℕ) :
    (rooks b below 0 p).card = (if p = 0 then 1 else 0) := by
  have : rooks b below 0 p = if p = 0 then {∅} else ∅ := by
    ext s
    rw [mem_rooks, card_eq_zero]
    by_cases h : p = 0
    · rw [ite_eq_left h, mem_singleton]
      exact ⟨fun hs => hs.2.1, by rintro rfl; simp [h]⟩
    · simp only [ite_eq_right h, notMem_empty, iff_false]
      rintro ⟨_, rfl, _, _, hp⟩
      exact h (by simpa using hp.symm)
  rw [this]
  split <;> simp

-- With no marked rooks, the original placement is supported on the unmarked subboard.
private theorem rooks_unmarked (m k : ℕ) :
    rooks (board m) below k 0 = rooks (upper m) below k 0 := by
  ext s
  simp only [mem_rooks, card_eq_zero]
  refine ⟨?_, fun ⟨hs, h⟩ => ⟨hs.trans (filter_subset ..), h⟩⟩
  rintro ⟨hs, hk, hr, hc, hz⟩
  refine ⟨?_, hk, hr, hc, hz⟩
  intro x hx
  apply mem_filter.mpr ⟨hs hx, ?_⟩
  intro hm
  have := mem_filter.mpr (⟨hx, hm⟩ : x ∈ s ∧ below x)
  rw [hz] at this
  exact notMem_empty _ this

private theorem rooks_one (b : Finset Cell) (p : ℕ) :
    (rooks b below 1 p).card = (b.filter fun x => (if below x then 1 else 0) = p).card := by
  symm
  apply card_nbij (fun x => {x})
  · intro x hx
    obtain ⟨h, ht⟩ := mem_filter.mp hx
    simpa [mem_rooks, Finset.filter_singleton, apply_ite card] using And.intro h ht
  · intro x _ y _ h
    simpa using h
  · intro s hs
    obtain ⟨x, rfl⟩ := card_eq_one.mp (mem_rooks.mp hs).2.1
    refine ⟨x, ?_, rfl⟩
    simpa [mem_rooks, Finset.filter_singleton, apply_ite card] using hs

private theorem board_zero : board 0 = ∅ := by
  ext x
  simp only [mem_board, notMem_empty, Nat.cast_zero, iff_false]
  omega

private theorem upper_zero : upper 0 = ∅ := by
  simp [upper, board_zero]

private theorem positive_card (m : ℕ) :
    ((board (m + 1)).filter below).card = (upper m).card := by
  apply card_nbij (fun x : Cell => (x.2, 1 - x.1))
  · intro x hx
    change x ∈ (board (m + 1)).filter below at hx
    change (x.2, 1 - x.1) ∈ upper m
    simp only [mem_filter, mem_board, Nat.cast_add, Nat.cast_one, below] at hx
    simp only [mem_upper]
    omega
  · intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) h.1
  · intro x hx
    have hx' := mem_upper.mp (show x ∈ upper m from hx)
    refine ⟨(1 - x.2, x.1), ?_, Prod.ext rfl (by simp)⟩
    change (1 - x.2, x.1) ∈ (board (m + 1)).filter below
    simp only [mem_filter, mem_board, Nat.cast_add, Nat.cast_one, below]
    omega

private theorem rows_withRow {m : ℕ} {x : Cell} (hx : x ∈ withRow m) :
    x.1 ∈ indices (m + 1) := by
  rw [mem_withRow, mem_board] at hx
  simp only [indices, mem_Icc, Nat.cast_add, Nat.cast_one]
  omega

private theorem cols_withRow {m : ℕ} {x : Cell} (hx : x ∈ withRow m) :
    x.2 ≠ -((m : ℤ) + 1) := by
  rw [mem_withRow, mem_board] at hx
  simp only [indices, mem_Icc] at hx
  omega

private theorem positive_columns {m : ℕ} {s : Finset Cell} (hs : s ⊆ board m) :
    (s.filter below).image Prod.snd ⊆ indices m := by
  intro j hj
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
  obtain ⟨hx, hb⟩ := mem_filter.mp hx
  have h := mem_board.mp (hs hx)
  simp only [below] at hb
  simp only [indices, mem_Icc]
  omega

private theorem row_step_nat (m k p : ℕ) :
    (rooks (withRow m) below (k + 1) (p + 1)).card =
      (rooks (board m) below (k + 1) (p + 1)).card +
        (m - p) * (rooks (board m) below k p).card := by
  apply rook_step
  · intro x hx he
    have h := (mem_board.mp hx).2.1
    omega
  · intro j hj
    simp only [indices, mem_Icc] at hj
    simp [below, show (0 : ℤ) < j by omega]
  · intro s hs
    have hm := mem_rooks.mp hs
    have hdiff : indices m \ s.image Prod.snd = indices m \ (s.filter below).image Prod.snd := by
      ext j
      rw [mem_sdiff, mem_sdiff]
      refine and_congr_right fun hj => not_congr ⟨?_, ?_⟩
      · intro h
        obtain ⟨x, hx, rfl⟩ := mem_image.mp h
        exact mem_image_of_mem _ (mem_filter.mpr ⟨hx, by
          simp only [below]
          have hh := (mem_Icc.mp hj).1
          omega⟩)
      · intro h
        exact image_subset_image (f := Prod.snd) (filter_subset below s) h
    rw [hdiff, card_sdiff_of_subset (positive_columns hm.1),
      card_image_of_injOn (hm.2.2.2.1.mono (filter_subset below s)), card_indices, hm.2.2.2.2]

private theorem rook_row_image {b s : Finset Cell} {m k p : ℕ}
    (hb : ∀ x ∈ b, x.1 ∈ indices (m + 1)) (hs : s ∈ rooks b below k p) :
    s.image Prod.fst ⊆ indices (m + 1) := by
  intro i hi
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hi
  exact hb x ((mem_rooks.mp hs).1 hx)

private theorem col_step_nat (b : Finset Cell) (m k p : ℕ)
    (hf : ∀ x ∈ b, x.2 ≠ -((m : ℤ) + 1)) (hb : ∀ x ∈ b, x.1 ∈ indices (m + 1)) :
    (rooks (withCol b m) below (k + 1) p).card =
      (rooks b below (k + 1) p).card + (m + 1 - k) * (rooks b below k p).card := by
  let t := -((m : ℤ) + 1)
  have hboard : (withCol b m).image Prod.swap =
      b.image Prod.swap ∪ (indices (m + 1)).image (Prod.mk t) := by
    simp [withCol, t, image_union, image_image, Function.comp_def]
  have hstep := rook_step (b.image Prod.swap) (fun x => below x.swap) t
    (indices (m + 1)) k p 0 (m + 1 - k) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact hf y hy) (by
      intro j _
      simp [below, t]) (by
      intro s hs
      have hm := mem_rooks.mp hs
      have hsub : s.image Prod.snd ⊆ indices (m + 1) := by
        intro j hj
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
        obtain ⟨y, hy, rfl⟩ := mem_image.mp (hm.1 hx)
        exact hb y hy
      rw [card_sdiff_of_subset hsub, card_image_of_injOn hm.2.2.2.1, card_indices, hm.2.1])
  simpa only [← hboard, Nat.add_zero, rooks_swap] using hstep

-- A negative integer coefficient can occur only in front of an empty count.
private theorem cast_mul_sub (n j a : ℕ) (ha : a ≠ 0 → j ≤ n) :
    ((n - j : ℕ) : ℤ) * (a : ℤ) = ((n : ℤ) - j) * a := by
  by_cases h : a = 0
  · simp [h]
  · rw [Nat.cast_sub (ha h)]

private theorem row_step (m k p : ℕ) :
    ((rooks (withRow m) below (k + 1) (p + 1)).card : ℤ) =
      (rooks (board m) below (k + 1) (p + 1)).card +
        ((m : ℤ) - p) * (rooks (board m) below k p).card := by
  rw [row_step_nat, Nat.cast_add, Nat.cast_mul, cast_mul_sub]
  intro h
  obtain ⟨s, hs⟩ := card_pos.mp (Nat.pos_of_ne_zero h)
  have hm := mem_rooks.mp hs
  have hcard := card_le_card (positive_columns hm.1)
  rwa [card_indices, card_image_of_injOn (hm.2.2.2.1.mono (filter_subset ..)), hm.2.2.2.2] at hcard

private theorem col_step (m k p : ℕ) :
    ((rooks (withCol (withRow m) m) below (k + 1) p).card : ℤ) =
      (rooks (withRow m) below (k + 1) p).card +
        ((m : ℤ) + 1 - k) * (rooks (withRow m) below k p).card := by
  rw [col_step_nat _ _ _ _ (fun _ => cols_withRow) (fun _ => rows_withRow),
    Nat.cast_add, Nat.cast_mul, cast_mul_sub, Nat.cast_add, Nat.cast_one]
  intro h
  obtain ⟨s, hs⟩ := card_pos.mp (Nat.pos_of_ne_zero h)
  have hcard := card_le_card (rook_row_image (fun _ => rows_withRow) hs)
  have hm := mem_rooks.mp hs
  rwa [card_indices, card_image_of_injOn hm.2.2.1, hm.2.1] at hcard

-- The p = 0 subboard is a staircase. Its one-column extension gives the
-- Stirling recurrence directly, with the empty board giving the initial row.
private theorem upper_count (m k : ℕ) :
    (rooks (upper m) below k 0).card = extStirlingSecond (m + 1 : ℕ) ((m : ℤ) - k + 1) := by
  induction m generalizing k with
  | zero =>
    rw [upper_zero, rooks_empty]
    rcases k with _ | _ | k
    · decide
    · decide
    · simp [extStirlingSecond, show ¬ (k : ℤ) ≤ -1 by omega]
  | succ m ih =>
    cases k with
    | zero =>
      rw [rooks_zero, show ((m + 1 : ℕ) : ℤ) - (0 : ℕ) + 1 = ((m + 1 + 1 : ℕ) : ℤ) by omega,
        extStirlingSecond_natCast, Nat.stirlingSecond_self]
      rfl
    | succ k =>
      rw [upper_succ, col_step_nat _ _ _ _ (by
        intro x hx
        have h := mem_upper.mp hx
        omega) (by
        intro x hx
        have h := mem_upper.mp hx
        simp only [indices, mem_Icc, Nat.cast_add, Nat.cast_one]
        omega), ih, ih]
      let d : ℤ := (m : ℤ) - k + 1
      have h1 : ((m + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) + 1 = d := by dsimp [d]; omega
      have h2 : (m : ℤ) - ((k + 1 : ℕ) : ℤ) + 1 = d - 1 := by dsimp [d]; omega
      have h3 : m + 1 - k = d.toNat := by dsimp [d]; omega
      rw [h1, h2, h3, show ((m + 1 + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) + 1 by omega,
        bishopsSquare_eq_sum.stirling_step _ _ (by omega), add_comm]

private theorem one_count (m p : ℕ) :
    (rooks (board m) below 1 p).card =
      (if p = 0 then Nat.stirlingSecond (m + 1) m else 0) +
        (if p = 1 then extStirlingSecond m ((m : ℤ) - 1) else 0) := by
  rcases p with _ | _ | p
  · rw [rooks_unmarked, upper_count, show (m : ℤ) - (1 : ℕ) + 1 = (m : ℤ) by omega,
      extStirlingSecond_natCast]
    simp
  · simp only [show (if (1 : ℕ) = 0 then Nat.stirlingSecond (m + 1) m else 0) = 0 by simp,
      zero_add]
    rw [rooks_one]
    have he : ((board m).filter fun x => (if below x then 1 else 0) = 1) =
        (board m).filter below := by
      ext x
      by_cases h : below x <;> simp [h]
    rw [he]
    cases m with
    | zero => rw [board_zero]; decide
    | succ m =>
      rw [positive_card, ← show (rooks (upper m) below 1 0).card = (upper m).card by
        rw [rooks_one]
        congr 1
        refine filter_eq_self.mpr fun x hx => ?_
        have h := mem_upper.mp hx
        have hn : ¬ below x := by unfold below; omega
        simp [hn]]
      rw [upper_count]
      congr 1
      omega
  · rw [rooks_one]
    have he : (board m).filter (fun x => (if below x then 1 else 0) = p + 1 + 1) = ∅ := by
      ext x
      by_cases h : below x <;> simp [h]
    simp [he]

private theorem recurrence (m k p : ℕ) :
    ((anassasBelow (m + 1) (k + 2) (p + 1) : ℤ)) =
      anassasBelow m (k + 2) (p + 1) + ((m : ℤ) - k) * anassasBelow m (k + 1) (p + 1) +
        ((m : ℤ) - p) * anassasBelow m (k + 1) p +
        ((m : ℤ) - p) * ((m : ℤ) - k) * anassasBelow m k p := by
  simp only [anassas_eq_rooks]
  rw [board_succ, show k + 2 = (k + 1) + 1 by omega, col_step, row_step, row_step]
  push_cast
  ring

end AnassaRooks

/-- **Recurrence for anassas below the diagonal.** Let $A(m, k, p)$ be the number of
nonattacking placements of $k$ anassas on the square board $\{1, \dots, m\}^2$ with exactly $p$
of them strictly below the main diagonal, let ${n \brace j}$ be Knuth's extended Stirling
numbers of the second kind, and let $\delta$ be the Kronecker delta. For $m \ge 1$, $k \ge 2$
and $p \ge 1$,
$$A(m, k, p) = A(m-1, k, p) + (m-k+1) A(m-1, k-1, p) + (m-p) A(m-1, k-1, p-1) +
(m-p)(m-k+1) A(m-1, k-2, p-1)$$
in the integers. Moreover, for all natural numbers $m$, $k$ and $p$,
$A(0, k, p) = \delta_{k0} \delta_{p0}$, $A(m, 0, p) = \delta_{p0}$,
$A(m, 1, p) = {m+1 \brace m} \delta_{p0} + {m \brace m-1} \delta_{p1}$ and
$A(m, k, 0) = {m+1 \brace m-k+1}$.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 11 (`jis-2025-25.8.6-thm-11`). -/
public theorem anassasBelow_recurrence (m k p : ℕ) :
    ((anassasBelow (m + 1) (k + 2) (p + 1) : ℤ) =
        anassasBelow m (k + 2) (p + 1) + ((m : ℤ) - k) * anassasBelow m (k + 1) (p + 1) +
          ((m : ℤ) - p) * anassasBelow m (k + 1) p +
          ((m : ℤ) - p) * ((m : ℤ) - k) * anassasBelow m k p) ∧
      anassasBelow 0 k p = (if k = 0 ∧ p = 0 then 1 else 0) ∧
      anassasBelow m 0 p = (if p = 0 then 1 else 0) ∧
      anassasBelow m 1 p =
        (if p = 0 then Nat.stirlingSecond (m + 1) m else 0) +
          (if p = 1 then extStirlingSecond m ((m : ℤ) - 1) else 0) ∧
      anassasBelow m k 0 = extStirlingSecond (m + 1 : ℕ) ((m : ℤ) - k + 1) := by
  refine ⟨AnassaRooks.recurrence m k p, ?_, ?_, ?_, ?_⟩
  · rw [AnassaRooks.anassas_eq_rooks, AnassaRooks.board_zero, AnassaRooks.rooks_empty]
  · rw [AnassaRooks.anassas_eq_rooks, AnassaRooks.rooks_zero]
  · rw [AnassaRooks.anassas_eq_rooks, AnassaRooks.one_count]
  · rw [AnassaRooks.anassas_eq_rooks, AnassaRooks.rooks_unmarked, AnassaRooks.upper_count]

end MetaMathlibExt
