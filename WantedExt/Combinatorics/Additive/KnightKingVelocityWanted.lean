/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/--
**Knight moves.** For integers $a$ and $b$, the $(a,b)$-knight's move set is
$$N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\} \subset \mathbb{Z}^2,$$
the finite set of the points $(a, b)$, $(-a, b)$, $(a, -b)$, $(-a, -b)$, $(b, a)$, $(-b, a)$,
$(b, -a)$ and $(-b, -a)$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `N_{a,b}`.
-/
public def knightMoves (a b : ℤ) : Finset (ℤ × ℤ) :=
  {(b, a), (a, b), (-a, b), (-b, a), (-b, -a), (-a, -b), (a, -b), (b, -a)}

/--
**King moves.** The king's move set $K \subset \mathbb{Z}^2$ consists of the eight unit
horizontal, vertical and diagonal steps:
$$K = \{(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)\}.$$

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `K`.
-/
public def kingMoves : Finset (ℤ × ℤ) :=
  {(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)}

/--
**Piece distance on the integer lattice.** Let $A \subseteq \mathbb{Z}^2$ be a finite set of
moves and, for $h \ge 1$, let $hA = \{a_1 + \dots + a_h : a_1, \dots, a_h \in A\}$ be its
$h$-fold sumset. The piece distance of a point $p \in \mathbb{Z}^2$ for $A$ is the natural
number that is $0$ if $p = (0,0)$ and otherwise the infimum of the set of integers $h \ge 1$
with $p \in hA$, where the infimum of the empty set is taken to be $0$.

Points other than the origin that are not a sum of moves from $A$ therefore have distance $0$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `A(x,y)`.
-/
public noncomputable def pieceDistance (A : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : ℕ :=
  if p = 0 then 0 else sInf {h : ℕ | 1 ≤ h ∧ p ∈ h • A}

/--
**Max-norm ball.** For a natural number $h$, the max-norm ball $B_h \subset \mathbb{Z}^2$ is the
product of two copies of the integer interval $\{-h, \dots, h\}$, that is, the set of lattice
points $(x, y)$ with $\max(|x|, |y|) \le h$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `B_h`.
-/
public def maxNormBall (h : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(h : ℤ)) h ×ˢ Finset.Icc (-(h : ℤ)) h

/--
**Piece distance from a minimal fold.** Let $A \subset \mathbb{Z}^2$ be a finite set, let
$p \in \mathbb{Z}^2$ be nonzero and let $n \ge 1$ be a natural number. If $p$ lies in the
$n$-fold sumset $nA = \{a_1 + \dots + a_n : a_1, \dots, a_n \in A\}$, and every natural number
$h \ge 1$ with $p \in hA$ satisfies $n \le h$, then the piece distance of $p$ for $A$ is $n$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `A(x,y)`.
-/
public theorem pieceDistance_eq_of_mem_of_forall
    (A : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (n : ℕ)
    (hp : p ≠ 0) (hn : 1 ≤ n) (hmem : p ∈ n • A)
    (hmin : ∀ h : ℕ, 1 ≤ h → p ∈ h • A → n ≤ h) :
    pieceDistance A p = n := by
  simp only [pieceDistance, hp, ↓reduceIte]
  apply le_antisymm
  · exact Nat.sInf_le ⟨hn, hmem⟩
  · let hs : ({h : ℕ | 1 ≤ h ∧ p ∈ h • A} : Set ℕ).Nonempty :=
      ⟨n, hn, hmem⟩
    exact hmin _ (Nat.sInf_mem hs).1 (Nat.sInf_mem hs).2

/--
For `k ≤ n`, summing `z` over the first `k` elements of `Fin n` and zero over
the rest gives `k*z`.  This finite-sum identity is used only to assemble an
explicit shortest king path coordinate by coordinate.
Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definitions of `A(x,y)` and `K`.
-/
private theorem sum_fin_indicator_lt (n k : ℕ) (hk : k ≤ n) (z : ℤ) :
    (∑ i : Fin n, if (i : ℕ) < k then z else 0) = (k : ℤ) * z := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte, Fin.val_succ,
            Nat.succ_lt_succ_iff]
          rw [ih k (by omega)]
          push_cast
          ring

/--
Any point in the `h`-fold king sumset has both coordinate absolute values, and
hence their natural maximum, at most `h`.  This formalizes the lower-bound
half of the king's max-norm metric.
Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definitions of `A(x,y)` and `K`.
-/
private theorem king_norm_le_of_mem (p : ℤ × ℤ) (h : ℕ) (hp : p ∈ h • kingMoves) :
    max p.1.natAbs p.2.natAbs ≤ h := by
  rw [Finset.mem_nsmul] at hp
  rcases hp with ⟨f, hf⟩
  rw [List.sum_ofFn] at hf
  have hx : (∑ i, ((f i : ℤ × ℤ).1)) = p.1 := by
    have hx' := congrArg Prod.fst hf
    rw [Prod.fst_sum] at hx'
    exact hx'
  have hy : (∑ i, ((f i : ℤ × ℤ).2)) = p.2 := by
    have hy' := congrArg Prod.snd hf
    rw [Prod.snd_sum] at hy'
    exact hy'
  have hcoord (j : Fin h) :
      |((f j : ℤ × ℤ).1)| ≤ 1 ∧ |((f j : ℤ × ℤ).2)| ≤ 1 := by
    have hj := (f j).property
    simp only [kingMoves, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with (hj | hj | hj | hj | hj | hj | hj | hj) <;>
      simp_all
  apply max_le
  · rw [← Int.ofNat_le, Int.natCast_natAbs]
    rw [← hx]
    calc
      |∑ i, (f i : ℤ × ℤ).1| ≤ ∑ i, |(f i : ℤ × ℤ).1| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin h, (1 : ℤ) := by
        exact Finset.sum_le_sum fun i _ => (hcoord i).1
      _ = (h : ℤ) := by simp
  · rw [← Int.ofNat_le, Int.natCast_natAbs]
    rw [← hy]
    calc
      |∑ i, (f i : ℤ × ℤ).2| ≤ ∑ i, |(f i : ℤ × ℤ).2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin h, (1 : ℤ) := by
        exact Finset.sum_le_sum fun i _ => (hcoord i).2
      _ = (h : ℤ) := by simp

/--
Every integer point belongs to the king sumset whose fold count is its natural
max norm.  The witness takes one signed unit step in each still-unfinished
coordinate, so each step is one of the eight members of `kingMoves`.
Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definitions of `A(x,y)` and `K`.
-/
private theorem king_mem_nsmul_norm (p : ℤ × ℤ) :
    p ∈ max p.1.natAbs p.2.natAbs • kingMoves := by
  let n := max p.1.natAbs p.2.natAbs
  let step : Fin n → ℤ × ℤ := fun i =>
    (if (i : ℕ) < p.1.natAbs then p.1.sign else 0,
      if (i : ℕ) < p.2.natAbs then p.2.sign else 0)
  have hstep (i : Fin n) : step i ∈ kingMoves := by
    by_cases hxi : (i : ℕ) < p.1.natAbs
    · have hsx : p.1.sign = 1 ∨ p.1.sign = -1 := by
        rcases Int.sign_trichotomy p.1 with hsx | hsx | hsx
        · exact Or.inl hsx
        · have hp0 := Int.eq_zero_of_sign_eq_zero hsx
          simp [hp0] at hxi
        · exact Or.inr hsx
      by_cases hyi : (i : ℕ) < p.2.natAbs
      · have hsy : p.2.sign = 1 ∨ p.2.sign = -1 := by
          rcases Int.sign_trichotomy p.2 with hsy | hsy | hsy
          · exact Or.inl hsy
          · have hp0 := Int.eq_zero_of_sign_eq_zero hsy
            simp [hp0] at hyi
          · exact Or.inr hsy
        rcases hsx with hsx | hsx <;> rcases hsy with hsy | hsy <;>
          simp [step, hxi, hyi, hsx, hsy, kingMoves]
      · rcases hsx with hsx | hsx <;>
          simp [step, hxi, hyi, hsx, kingMoves]
    · by_cases hyi : (i : ℕ) < p.2.natAbs
      · have hsy : p.2.sign = 1 ∨ p.2.sign = -1 := by
          rcases Int.sign_trichotomy p.2 with hsy | hsy | hsy
          · exact Or.inl hsy
          · have hp0 := Int.eq_zero_of_sign_eq_zero hsy
            simp [hp0] at hyi
          · exact Or.inr hsy
        rcases hsy with hsy | hsy <;>
          simp [step, hxi, hyi, hsy, kingMoves]
      · have hi := i.isLt
        simp only [n] at hi
        omega
  rw [Finset.mem_nsmul]
  refine ⟨fun i => ⟨step i, hstep i⟩, ?_⟩
  rw [List.sum_ofFn]
  apply Prod.ext
  · rw [Prod.fst_sum]
    change (∑ i : Fin n, if (i : ℕ) < p.1.natAbs then p.1.sign else 0) = p.1
    rw [sum_fin_indicator_lt n p.1.natAbs (by simp [n])]
    rw [mul_comm, Int.sign_mul_natAbs]
  · rw [Prod.snd_sum]
    change (∑ i : Fin n, if (i : ℕ) < p.2.natAbs then p.2.sign else 0) = p.2
    rw [sum_fin_indicator_lt n p.2.natAbs (by simp [n])]
    rw [mul_comm, Int.sign_mul_natAbs]

/--
**King distance is the max norm.** For every lattice point $p = (x, y) \in \mathbb{Z}^2$, the
piece distance of $p$ for the king's move set $K$ is $\max(|x|, |y|)$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definitions of `A(x,y)` and `K`.
-/
public theorem pieceDistance_kingMoves (p : ℤ × ℤ) :
    pieceDistance kingMoves p = max p.1.natAbs p.2.natAbs := by
  by_cases hp : p = 0
  · subst p
    simp [pieceDistance]
  · apply pieceDistance_eq_of_mem_of_forall
    · exact hp
    · have hpos : max p.1.natAbs p.2.natAbs ≠ 0 := by
        intro hzero
        have hx : p.1 = 0 := Int.natAbs_eq_zero.mp (by omega)
        have hy : p.2 = 0 := Int.natAbs_eq_zero.mp (by omega)
        exact hp (Prod.ext hx hy)
      omega
    · exact king_mem_nsmul_norm p
    · intro h _ hmem
      exact king_norm_le_of_mem p h hmem

/--
**The knight reaches $(1,2)$ in one move.** Let $N \subseteq \mathbb{Z}^2$ be the move set of the
usual knight, consisting of the eight vectors $(\pm 1, \pm 2)$ and $(\pm 2, \pm 1)$. The piece
distance of the point $(1,2)$ for $N$ is $1$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of the usual knight following the definition of `N_{a,b}`.
-/
public theorem pieceDistance_knightMoves_one_two :
    pieceDistance (knightMoves 1 2) (1, 2) = 1 := by
  apply pieceDistance_eq_of_mem_of_forall
  · norm_num
  · norm_num
  · simp [knightMoves]
  · intro h hh _
    omega

/--
**The knight needs three moves to reach $(1,0)$.** Let $N \subseteq \mathbb{Z}^2$ be the move set
of the usual knight, consisting of the eight vectors $(\pm 1, \pm 2)$ and $(\pm 2, \pm 1)$. The
piece distance of the point $(1,0)$ for $N$ is $3$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), characteristic value for the usual knight.
-/
public theorem pieceDistance_knightMoves_one_zero :
    pieceDistance (knightMoves 1 2) (1, 0) = 3 := by
  apply pieceDistance_eq_of_mem_of_forall
  · norm_num
  · norm_num
  · rw [Finset.mem_nsmul]
    refine ⟨![⟨(1, 2), by simp [knightMoves]⟩,
      ⟨(2, -1), by simp [knightMoves]⟩,
      ⟨(-2, -1), by simp [knightMoves]⟩], ?_⟩
    norm_num [List.sum_ofFn]
  · intro h hh hmem
    by_contra hnot
    have hle : h ≤ 2 := by omega
    interval_cases h
    · simp [knightMoves] at hmem
    · rw [Finset.mem_nsmul] at hmem
      rcases hmem with ⟨f, hf⟩
      have hf0 := (f 0).property
      have hf1 := (f 1).property
      simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hf0 hf1
      rcases hf0 with (h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0) <;>
        rcases hf1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;>
        simp_all

/--
**The usual knight reaches (1, 1) in two moves.** For the usual knight's move set
$N_{1,2} = \{(\pm 1, \pm 2), (\pm 2, \pm 1)\}$, the piece distance of the point $(1, 1)$ is $2$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), characteristic value for the usual knight.
-/
public theorem pieceDistance_knightMoves_one_one :
    pieceDistance (knightMoves 1 2) (1, 1) = 2 := by
  apply pieceDistance_eq_of_mem_of_forall
  · norm_num
  · norm_num
  · rw [Finset.mem_nsmul]
    refine ⟨![⟨(2, -1), by simp [knightMoves]⟩,
      ⟨(-1, 2), by simp [knightMoves]⟩], ?_⟩
    norm_num [List.sum_ofFn]
  · intro h hh hmem
    by_contra hnot
    have hle : h ≤ 1 := by omega
    interval_cases h
    norm_num [Finset.mem_nsmul, knightMoves, List.sum_ofFn] at hmem

/--
**The knight's distance to the origin is zero.** Let $N \subseteq \mathbb{Z}^2$ be the move set of
the usual knight, consisting of the eight vectors $(\pm 1, \pm 2)$ and $(\pm 2, \pm 1)$. The
piece distance of the origin $(0,0)$ for $N$ is $0$.

This holds by the definition of piece distance, which sets the distance at the origin to $0$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `A(0,0)`.
-/
public theorem pieceDistance_knightMoves_zero_zero :
    pieceDistance (knightMoves 1 2) (0, 0) = 0 := by
  simp [pieceDistance]

/--
**Number of points in the max-norm ball.** For every natural number $h$, the max-norm ball
$B_h = \{(x, y) \in \mathbb{Z}^2 : \max(|x|, |y|) \le h\}$ has exactly $(2h+1)^2$ points.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `B_h`.
-/
public theorem card_maxNormBall (h : ℕ) : (maxNormBall h).card = (2 * h + 1) ^ 2 := by
  have hcard : (Finset.Icc (-(h : ℤ)) h).card = 2 * h + 1 := by
    rw [Int.card_Icc]
    omega
  simp [maxNormBall, Finset.card_product, hcard, pow_two]

/--
**Uniform bound for knight distance on a box.** There is an absolute constant $M \in \mathbb{R}$
such that for all natural numbers $a$ and $b$ with $1 \le a < b$, $\gcd(a, b) = 1$ and $a + b$
odd, every lattice point $(x, y) \in \mathbb{Z}^2$ with $\max(|x|, |y|) \le a + b$ has piece
distance at most $Mb$ for the $(a,b)$-knight's move set
$N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\}$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Lemma 2.1.
-/
public theorem_wanted knight_distance_uniform_on_box :
    ∃ M : ℝ, ∀ a b : ℕ,
      1 ≤ a → a < b → Nat.Coprime a b → Odd (a + b) →
      ∀ p : ℤ × ℤ,
        max |p.1| |p.2| ≤ ((a + b : ℕ) : ℤ) →
        (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℝ) ≤ M * b

/--
**Knight distance asymptotics.** There is an absolute constant $M \in \mathbb{R}$ with the
following property. Let $a$ and $b$ be natural numbers with $1 \le a < b$, $\gcd(a, b) = 1$ and
$a + b$ odd, let $N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\}$ be the $(a,b)$-knight's move set,
and for $p \in \mathbb{Z}^2$ let $d_{a,b}(p)$ be the piece distance of $p$ for $N_{a,b}$. Then
for all integers $x$ and $y$ with $0 \le y \le x$: if $by \le ax$, then
$|d_{a,b}(x, y) - x/b| \le Mb$; and if $ax < by$, then
$|d_{a,b}(x, y) - (x + y)/(a + b)| \le Mb$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Theorem 1.1.
-/
public theorem_wanted knight_distance_asymptotics :
    ∃ M : ℝ, ∀ (a b : ℕ) (x y : ℤ),
      1 ≤ a → a < b → Nat.Coprime a b → Odd (a + b) →
      0 ≤ y → y ≤ x →
      (((b : ℤ) * y ≤ (a : ℤ) * x →
          |(pieceDistance (knightMoves (a : ℤ) (b : ℤ)) (x, y) : ℝ) -
              (x : ℝ) / (b : ℝ)| ≤ M * b) ∧
        ((a : ℤ) * x < (b : ℤ) * y →
          |(pieceDistance (knightMoves (a : ℤ) (b : ℤ)) (x, y) : ℝ) -
              ((x : ℝ) + (y : ℝ)) / ((a : ℝ) + (b : ℝ))| ≤ M * b))

/--
**Velocity formula for the (a, b)-knight.** Let $a$ and $b$ be natural numbers with
$1 \le a < b$, $\gcd(a, b) = 1$ and $a + b$ odd, let
$N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\}$ be the $(a,b)$-knight's move set, and for
$p \in \mathbb{Z}^2$ let $d_{a,b}(p)$ be the piece distance of $p$ for $N_{a,b}$. For a natural
number $h$, let $B_h = \{(x, y) \in \mathbb{Z}^2 : \max(|x|, |y|) \le h\}$ be the max-norm
ball and let $\bar{d}(h) = |B_h|^{-1} \sum_{p \in B_h} d_{a,b}(p)$ be the average of $d_{a,b}$
over $B_h$. Then
$$\lim_{h \to \infty} \frac{2h}{3} \, \bar{d}(h)^{-1} = \frac{2(a+b)b^2}{a^2 + 3b^2}.$$

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Theorem 1.3.
-/
public theorem_wanted knight_velocity_formula (a b : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hcoprime : Nat.Coprime a b)
    (hodd : Odd (a + b)) :
    Filter.Tendsto
      (fun h : ℕ =>
        (2 * (h : ℝ) / 3) *
          (((∑ p ∈ maxNormBall h,
              (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℝ)) /
            ((maxNormBall h).card : ℝ))⁻¹))
      Filter.atTop
      (nhds
        (2 * ((a : ℝ) + (b : ℝ)) * (b : ℝ) ^ 2 /
          ((a : ℝ) ^ 2 + 3 * (b : ℝ) ^ 2)))

end

end MetaMathlibExt
