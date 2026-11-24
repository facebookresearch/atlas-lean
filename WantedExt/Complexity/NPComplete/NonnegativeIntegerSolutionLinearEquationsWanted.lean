/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-NEGATIVE INTEGER SOLUTION OF LINEAR EQUATIONS is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.IntegerProgrammingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonnegativeIntegerSolutionLinearEquations

open IntegerProgramming (toInt dot)

/-!
# NON-NEGATIVE INTEGER SOLUTION OF LINEAR EQUATIONS is NP-complete

INSTANCE: a finite set `X` of pairs `(x, b)`, where `x` is an `m`-tuple of integers and `b` is an
integer.
QUESTION: is there an `m`-tuple `y` with non-negative integer entries such that `x · y = b` for
all `(x, b) ∈ X` (where the dot-product of two `m`-tuples `u` and `v` is `∑ᵢ uᵢ vᵢ`)?

This is the equality variant of [MP1] INTEGER PROGRAMMING in its comment. Integers are pairs of
naturals `(positive part, negative part)`, and the dot product is that of
`WantedExt.Complexity.NPComplete.IntegerProgrammingWanted` (`toInt`, `dot`); `X` is a list of
pairs, and a repeated pair imposes the same equation twice. The solution `y` is a list of `m`
naturals, cast to integers in the dot product. Numbers use the binary encoding; Borosh and
Treybig bound a smallest non-negative solution polynomially in the input size, which gives
membership in `NP`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **NON-NEGATIVE INTEGER SOLUTION OF LINEAR EQUATIONS is NP-complete.** Source: Garey and
Johnson (1979), [MP1], comment; Sahni (1974); Borosh and Treybig (1976). -/
public theorem_wanted nonnegativeIntegerSolutionLinearEquations_npComplete :
    nonnegativeIntegerSolutionLinearEquationsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonnegativeIntegerSolutionLinearEquationsDec

end MetaMathlibExt.Complexity.NPComplete.NonnegativeIntegerSolutionLinearEquations
