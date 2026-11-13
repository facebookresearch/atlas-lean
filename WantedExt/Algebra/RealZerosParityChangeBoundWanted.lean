/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Real zeros bounded by coefficient parity changes (AMR-021-0014)

For a polynomial with positive coefficients, the number of (distinct) real
zeros does not exceed the number of parity changes in the positive-`c̃`
index sequence.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Algebra.RealZerosParityChangeBoundWanted

/-! Source record `AMR-021-0014`. -/

/-- The differences `c̃_k = (k+1)a_k² - k·a_{k-1}·a_{k+1}`. -/
def cTilde (f : Polynomial ℝ) (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) * (f.coeff k) ^ 2 -
    (k : ℝ) * f.coeff (k - 1) * f.coeff (k + 1)

/-- Indices with positive `c̃`, in increasing order. -/
noncomputable def posIndices (f : Polynomial ℝ) : List ℕ :=
  ((Finset.range (f.natDegree + 1)).filter (fun k => 0 < cTilde f k)).sort (· ≤ ·)

/-- Number of parity changes in the index sequence. -/
noncomputable def vVal (f : Polynomial ℝ) : ℕ :=
  ((posIndices f).zip ((posIndices f).drop 1)).countP
    (fun p => p.1 % 2 ≠ p.2 % 2)

/-- [AMR-021-0014] A real polynomial with positive coefficients has at most
`v(f)` distinct real zeros. -/
def conjecture : Prop :=
  ∀ f : Polynomial ℝ,
    (∀ k ∈ Finset.range (f.natDegree + 1), 0 < f.coeff k) →
    Set.ncard {x : ℝ | f.eval x = 0} ≤ vVal f

/--
Resolved false: Katkova, Shapiro and Vishnyakova (arXiv:2403.12200, Sec. 5) disprove Conjecture
9 via iterated primitives Q_n of an explicit Q_15. Splitting the repeated root also refutes this
entry's distinct-zero reading: ∏_{j<23}(x+1+j/10^4)(38x²−199x+363) has 23 distinct real zeros
and v = 21. Source: Olga Katkova, Boris Shapiro and Anna Vishnyakova, In search of Newton-type
inequalities, arXiv:2403.12200 (2024), https://arxiv.org/abs/2403.12200. Moved from
`OpenConjectures/Algebra/RealZerosParityChangeBound`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.RealZerosParityChangeBoundWanted
