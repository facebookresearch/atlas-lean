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
public import MathlibExt.Algebra.RationalFunctionFareyPathPolyContFractConvergentsFareyPath

namespace MetaMathlibExt

@[expose] public section

open Polynomial

variable {F : Type*} [Field F]

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

end

end MetaMathlibExt
