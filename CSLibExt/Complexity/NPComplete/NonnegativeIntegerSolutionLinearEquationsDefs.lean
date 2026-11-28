/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-NEGATIVE INTEGER SOLUTION OF LINEAR EQUATIONS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP1] INTEGER PROGRAMMING, comment
(p. 245): "Also NP-complete are the questions of whether a `y` with non-negative integer entries
exists such that `x·y = b` for all `(x, b) ∈ X`, …" [Sahni, 1974];
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974), 262-279,
doi:10.1137/0203021;
I. Borosh and L. B. Treybig, "Bounds on positive integral solutions of linear Diophantine
equations", Proceedings of the American Mathematical Society 55 (1976), 299-304,
doi:10.1090/S0002-9939-1976-0396605-3 (membership in NP).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IntegerProgrammingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonnegativeIntegerSolutionLinearEquations

open IntegerProgramming (toInt dot)

/-- An instance: the dimension `m` and the pairs `(x, b)` of `X`, integers as
`(positive part, negative part)` pairs. -/
abbrev NonnegativeIntegerSolutionLinearEquationsInstance :=
  ℕ × List (List (ℕ × ℕ) × (ℕ × ℕ))

/-- Well-formedness of an instance: every tuple `x` has length `m`. -/
def WellFormed (i : NonnegativeIntegerSolutionLinearEquationsInstance) : Prop :=
  ∀ p ∈ i.2, p.1.length = i.1

/-- Some `m`-tuple `y` of non-negative integers satisfies `x · y = b` for every `(x, b) ∈ X`. -/
def NonnegativeIntegerSolutionLinearEquationsFeasible
    (i : NonnegativeIntegerSolutionLinearEquationsInstance) : Prop :=
  ∃ y : List ℕ, y.length = i.1 ∧ ∀ p ∈ i.2, dot p.1 (y.map fun n : ℕ => (n : ℤ)) = toInt p.2

open Classical in
/-- NON-NEGATIVE INTEGER SOLUTION OF LINEAR EQUATIONS as a decision problem over bitstrings. -/
noncomputable def nonnegativeIntegerSolutionLinearEquationsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonnegativeIntegerSolutionLinearEquationsInstance) x with
  | some i => decide (WellFormed i ∧ NonnegativeIntegerSolutionLinearEquationsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NonnegativeIntegerSolutionLinearEquations
