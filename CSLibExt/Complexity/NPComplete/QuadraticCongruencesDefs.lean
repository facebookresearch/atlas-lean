/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC CONGRUENCES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN1] QUADRATIC
CONGRUENCES;
K. L. Manders and L. M. Adleman, "NP-complete decision problems for binary
quadratics", Journal of Computer and System Sciences 16 (1978), 168-184,
doi:10.1016/0022-0000(78)90044-2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.ModEq

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticCongruences

/-- An instance: the numbers `(a, b, c)`. -/
abbrev QuadraticCongruencesInstance := ℕ × ℕ × ℕ

/-- Well-formedness of an instance: `a`, `b` and `c` are positive. -/
def WellFormed (i : QuadraticCongruencesInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some positive `x < c` satisfies `x ^ 2 ≡ a [MOD b]`. -/
def QuadraticCongruencesFeasible (i : QuadraticCongruencesInstance) : Prop :=
  ∃ x : ℕ, 0 < x ∧ x < i.2.2 ∧ x ^ 2 ≡ i.1 [MOD i.2.1]

open Classical in
/-- QUADRATIC CONGRUENCES as a decision problem over bitstrings. -/
noncomputable def quadraticCongruencesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuadraticCongruencesInstance) x with
  | some i => decide (WellFormed i ∧ QuadraticCongruencesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.QuadraticCongruences
