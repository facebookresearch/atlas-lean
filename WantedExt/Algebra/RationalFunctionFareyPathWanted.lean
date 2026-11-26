/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.ContinuedFractions.RationalFunctionFareyPath
public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Field.ZMod
public import MathlibExt.Algebra.RationalFunctionFareyPathPolyContFractExtendFareyPath
public import MathlibExt.Algebra.RationalFunctionFareyPathPolyContFractOfFareyPathDetNegOnePowPred
public import MathlibExt.Algebra.RationalFunctionFareyPathPolyContFractOfFareyPathDetNegOne
public import MathlibExt.Algebra.RationalFunctionFareyPathArePolyFareyNeighborsIff

namespace MetaMathlibExt

@[expose] public section

open Polynomial

variable {F : Type*} [Field F]

/-- **Convergents of a polynomial continued fraction form a Farey path.** Let $F$ be a field, let
$n \in \mathbb N$, and let $a_0, a_1, \dots, a_n \in F[X]$ with $a_i$ nonconstant for
$1 \le i \le n$. Write $A_i$ and $B_i$ for the numerator and the denominator of the $i$th
convergent $A_i / B_i$ of the continued fraction $[a_0, a_1, \dots, a_n]$ over $F(X)$. Then for
every $i \le n$, $A_i$ and $B_i$ are polynomials in $F[X]$, $B_i \ne 0$, and $A_i$ and $B_i$ are
coprime in $F[X]$; and for $1 \le i \le n$, the polynomial $A_i B_{i-1} - A_{i-1} B_i$ is a unit
of $F[X]$, that is, a nonzero constant.

In the language of the paper, each convergent $A_i / B_i$ is a vertex of the Farey graph over $F$
and consecutive convergents are adjacent in it.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 4. -/
public theorem_wanted polyContFract_convergents_farey_path (a : ℕ → F[X]) (n : ℕ)
    (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) :
    ∃ A B : ℕ → F[X], ∀ i ≤ n,
      (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i) ∧
      (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i) ∧
      B i ≠ 0 ∧ IsCoprime (A i) (B i) ∧
      (1 ≤ i → IsUnit (A i * B (i - 1) - A (i - 1) * B i))

/-- **Continued fraction along a Farey path of polynomials.** Let $F$ be a field, let
$n \in \mathbb N$, let $u_i, v_i \in F[X]$ for $i \ge 0$, and let $c_i \in F$ for $i \ge 1$.
Suppose that $v_0 = 1$ and that for $1 \le i \le n$ we have $c_i \ne 0$,
$\deg v_{i-1} < \deg v_i$ and $u_i v_{i-1} - u_{i-1} v_i = c_i$. Let $a_0, a_1, \ldots \in F[X]$
satisfy $a_0 = u_0$, $a_1 = c_1^{-1} v_1$, $a_2 = -c_2^{-1} c_1 (u_2 v_0 - u_0 v_2)$ and, for
$3 \le i \le n$,
$$a_i = (-1)^{i+1}c_i^{-1}c_{i-1}(u_i v_{i-2} - u_{i-2} v_i)\prod_{j=1}^{i-2} c_j^{2(-1)^{i-j+1}}.$$
Then $a_i$ is nonconstant for $1 \le i \le n$. Moreover, for every $i \le n$ let
$t_i = \varepsilon_i \prod_{j=1}^{i} c_j^{(-1)^{i-j+1}}$, where $\varepsilon_i = 1$ if
$i \equiv 0, 1 \pmod 4$ and $\varepsilon_i = -1$ if $i \equiv 2, 3 \pmod 4$. Then the numerator
$A_i$ and the denominator $B_i$ of the $i$th convergent of the continued fraction
$[a_0; a_1, \ldots, a_n]$ over $F(X)$ are $A_i = t_i u_i$ and $B_i = t_i v_i$, and this
convergent equals $u_i / v_i$.

The paper's coprimality hypothesis $(u_i, v_i) = 1$ is omitted: it follows from the determinant
condition.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 6. -/
public theorem_wanted polyContFract_of_farey_path (u v : ℕ → F[X]) (c : ℕ → F) (n : ℕ)
    (hv0 : v 0 = 1) (hc : ∀ i, 1 ≤ i → i ≤ n → c i ≠ 0)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = C (c i))
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = C (c 1)⁻¹ * v 1)
    (ha2 : a 2 = -C ((c 2)⁻¹ * c 1) * (u 2 * v 0 - u 0 * v 2))
    (ha : ∀ i, 3 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1) * (c i)⁻¹ * c (i - 1) *
        ∏ j ∈ Finset.Icc 1 (i - 2), c j ^ (2 * (-1 : ℤ) ^ (i - j + 1))) *
        (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, ∃ t : F,
        t = (if i % 4 = 0 ∨ i % 4 = 1 then 1 else -1) *
          ∏ j ∈ Finset.Icc 1 i, c j ^ ((-1 : ℤ) ^ (i - j + 1)) ∧
        (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (C t * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (C t * v i) ∧
        (polyContFract a n).convs i =
          algebraMap F[X] (RatFunc F) (u i) / algebraMap F[X] (RatFunc F) (v i)

/-- **The fraction $0/1$ lies in every Farey series.** For every field $F$ and every natural number
$n$, the pair $(0, 1)$, that is the fraction $0 / 1$, belongs to the Farey series $\mathcal{F}_n$
of order $n$ over $F$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1. -/
public theorem zero_one_mem_polyFareySeries (n : ℕ) :
    ((0 : F[X]), (1 : F[X])) ∈ polyFareySeries n := by
  refine ⟨?_, ?_, isCoprime_zero_left.2 isUnit_one, monic_one⟩ <;> simp

/-- **The fraction 1/X in the polynomial Farey series.** Let $F$ be a field. For every natural
number $n \ge 1$, the pair $(1, X)$, that is, the fraction $1/X$, belongs to the Farey series
$\mathcal F_n$ of order $n$ over $F$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 1. -/
public theorem one_X_mem_polyFareySeries {n : ℕ} (hn : 1 ≤ n) :
    ((1 : F[X]), (X : F[X])) ∈ polyFareySeries n := by
  refine ⟨?_, ?_, isCoprime_one_left, monic_X⟩ <;> simp [hn]

/-- **No fraction is its own degree neighbour.** Let $F$ be a field and let $n \in \mathbb N$. For
every pair $(u, v)$ of polynomials over $F$, the fraction $u/v$ is not a $(\deg v)$-neighbour of
itself in the Farey series $\mathcal F_n$ of order $n$ over $F$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Definition 2. -/
public theorem not_isPolyFareyDegNeighbor_self [DecidableEq (RatFunc F)] (n : ℕ)
    (w : F[X] × F[X]) : ¬ IsPolyFareyDegNeighbor n w w :=
  fun h => h.2.2.1 rfl

/-- **Number of neighbours of a polynomial Farey fraction.** Let $p$ be a prime, let
$n \in \mathbb{N}$, and let $u / v$ be a fraction of the Farey series $\mathcal{F}_n$ over
$\mathbb{F}_p$ with $q = \deg v \ge 1$. Then for every $t \in \mathbb{N}$ with $q + t \le n$,
exactly $(p - 1) p^t$ fractions $h / k \in \mathcal{F}_n$ with $\deg k = q + t$ are neighbours
of $u / v$ in $\mathcal{F}_n$, and exactly one fraction $h / k \in \mathcal{F}_n$ with
$\deg k < q$ is a neighbour of $u / v$ in $\mathcal{F}_n$.

Compared with the paper, $t$ is restricted to $q + t \le n$ (there are no fractions of larger
degree in $\mathcal{F}_n$), the hypothesis $q \ge 1$ is added (for $0 / 1$ there is no neighbour
of degree less than $0$), and the field is the prime field $\mathbb{F}_p$, the case of the
paper's count $(p - 1) p^t$ and of its Example 2.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 3 (`integers-2026-A3-thm-3`). -/
public theorem_wanted polyFarey_neighbor_count (p : ℕ) [Fact p.Prime]
    [DecidableEq (RatFunc (ZMod p))] (n : ℕ) {w : (ZMod p)[X] × (ZMod p)[X]}
    (hw : w ∈ polyFareySeries (F := ZMod p) n) (hq : 1 ≤ w.2.natDegree) :
    (∀ t : ℕ, w.2.natDegree + t ≤ n →
      Set.ncard {z | z ∈ polyFareySeries (F := ZMod p) n ∧ z.2.natDegree = w.2.natDegree + t ∧
        ArePolyFareyNeighbors (F := ZMod p) n w z} = (p - 1) * p ^ t) ∧
      ∃! z, z ∈ polyFareySeries (F := ZMod p) n ∧ z.2.natDegree < w.2.natDegree ∧
        ArePolyFareyNeighbors (F := ZMod p) n w z

end

end MetaMathlibExt
