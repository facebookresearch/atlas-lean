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
public import MathlibExt.Algebra.RationalFunctionFareyPathPolyContFractOfFareyPath

namespace MetaMathlibExt

@[expose] public section

open Polynomial

variable {F : Type*} [Field F]

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
