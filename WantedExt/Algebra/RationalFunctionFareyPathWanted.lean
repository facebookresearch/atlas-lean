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

end

end MetaMathlibExt
