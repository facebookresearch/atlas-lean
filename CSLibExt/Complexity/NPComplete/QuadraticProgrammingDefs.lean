/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC PROGRAMMING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP2] QUADRATIC PROGRAMMING;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974), 262-279,
doi:10.1137/0203021 (NP-hardness);
S. A. Vavasis, "Quadratic programming is in NP", Information Processing Letters 36 (1990),
73-77, doi:10.1016/0020-0190(90)90100-C (membership in NP).
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming

/-- The code `((p, q), r)` of the rational number `(p - q) / r`. -/
abbrev RatCode := (ℕ × ℕ) × ℕ

/-- The rational number `(p - q) / r` encoded by `((p, q), r)`. -/
def ratVal (q : RatCode) : ℚ := ((q.1.1 : ℚ) - q.1.2) / q.2

/-- An instance: the dimension `m`, the constraint pairs `(x, b)`, the tuples `c` and `d`, and
the bound `B`. -/
abbrev QuadraticProgrammingInstance :=
  ℕ × List (List RatCode × RatCode) × List RatCode × List RatCode × RatCode

/-- Well-formedness of an instance: every tuple has length `m`, and every encoded rational has
a positive denominator. -/
def WellFormed (i : QuadraticProgrammingInstance) : Prop :=
  (∀ xb ∈ i.2.1, xb.1.length = i.1 ∧ (∀ q ∈ xb.1, 0 < q.2) ∧ 0 < xb.2.2) ∧
    i.2.2.1.length = i.1 ∧ (∀ q ∈ i.2.2.1, 0 < q.2) ∧
    i.2.2.2.1.length = i.1 ∧ (∀ q ∈ i.2.2.2.1, 0 < q.2) ∧ 0 < i.2.2.2.2.2

/-- A rational point `y` satisfying every constraint `x · y ≤ b` at which the objective
`∑ᵢ (cᵢ yᵢ² + dᵢ yᵢ)` is at least `B`. -/
def QuadraticProgrammingFeasible (i : QuadraticProgrammingInstance) : Prop :=
  ∃ y : Fin i.1 → ℚ,
    (∀ xb ∈ i.2.1, ∑ j : Fin i.1, ratVal (xb.1.getD j ((0, 0), 1)) * y j ≤ ratVal xb.2) ∧
      ratVal i.2.2.2.2 ≤ ∑ j : Fin i.1,
        (ratVal (i.2.2.1.getD j ((0, 0), 1)) * y j ^ 2 +
          ratVal (i.2.2.2.1.getD j ((0, 0), 1)) * y j)

open Classical in
/-- QUADRATIC PROGRAMMING as a decision problem over bitstrings. -/
noncomputable def quadraticProgrammingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuadraticProgrammingInstance) x with
  | some i => decide (WellFormed i ∧ QuadraticProgrammingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming
