/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC DIOPHANTINE EQUATIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN8] QUADRATIC DIOPHANTINE EQUATIONS;
K. L. Manders and L. M. Adleman, "NP-complete decision problems for binary quadratics",
Journal of Computer and System Sciences 16 (1978), 168-184,
doi:10.1016/0022-0000(78)90044-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticDiophantineEquations

/-!
# QUADRATIC DIOPHANTINE EQUATIONS is NP-complete

Given positive integers `a`, `b` and `c`, are there positive integers `x` and `y` such that
`a x² + b y = c`?

Numbers use the canonical binary encoding (the problem is NP-complete in the weak sense:
trying every `x ≤ √(c / a)` is pseudo-polynomial).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the coefficients `(a, b, c)`. -/
abbrev QuadraticDiophantineEquationsInstance := ℕ × ℕ × ℕ

/-- Well-formedness of an instance: `a`, `b` and `c` are positive. -/
def WellFormed (i : QuadraticDiophantineEquationsInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Positive integers `x` and `y` with `a x² + b y = c`. -/
def QuadraticDiophantineEquationsFeasible (i : QuadraticDiophantineEquationsInstance) : Prop :=
  ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ i.1 * x ^ 2 + i.2.1 * y = i.2.2

open Classical in
/-- QUADRATIC DIOPHANTINE EQUATIONS as a decision problem over bitstrings. -/
noncomputable def quadraticDiophantineEquationsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuadraticDiophantineEquationsInstance) x with
  | some i => decide (WellFormed i ∧ QuadraticDiophantineEquationsFeasible i)
  | none => false

/-- **QUADRATIC DIOPHANTINE EQUATIONS is NP-complete.** Source: Garey and Johnson (1979), [AN8];
Manders and Adleman (1978). -/
public theorem_wanted quadraticDiophantineEquations_npComplete :
    quadraticDiophantineEquationsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticDiophantineEquationsDec

end MetaMathlibExt.Complexity.NPComplete.QuadraticDiophantineEquations
