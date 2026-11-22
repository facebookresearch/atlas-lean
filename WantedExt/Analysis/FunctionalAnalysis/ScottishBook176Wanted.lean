/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook176Wanted

/-- Eidelheit's Problem 176 from the Scottish Book, in its original form:
in a Banach ring (a normed, complete linear ring with `‖x * y‖ ≤ ‖x‖ * ‖y‖`)
containing a unit, every element possessing an inverse is a limit of
polynomials in itself, with scalar coefficients depending on the sequence
index. -/
def ScottishBookProblem176Claim : Prop :=
  ∀ (A : Type) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a b : A), a * b = 1 → b * a = 1 →
    ∃ p : ℕ → Polynomial ℝ,
      Filter.Tendsto (fun n => Polynomial.aeval a (p n)) Filter.atTop (nhds b)

/--
Eidelheit's Problem 176 is false: the answer is negative, with the
counterexample of the ring of linear operations on the space `(C)` given
by `U(x)(t) = x(t ^ 2)` for `0 ≤ t ≤ 1`. Source: M. Eidelheit,
Problem 176 of the Scottish Book, with the negative answer recorded in
Ad 176 of the typescript (November 11, 1938). See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted eidelheit176_refuted : ¬ ScottishBookProblem176Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook176Wanted
