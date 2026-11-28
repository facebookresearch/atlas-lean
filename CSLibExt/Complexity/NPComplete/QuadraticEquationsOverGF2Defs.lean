/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALGEBRAIC EQUATIONS OVER GF[2] with at most two variables per term: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN9] ALGEBRAIC EQUATIONS OVER GF[2],
p. 251, comment: "Remains NP-complete even if none of the polynomials has a term involving more
than two variables", credited there to L. G. Valiant (1977, private communication; not
available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.AlgebraicEquationsOverGF2Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticEquationsOverGF2

open MetaMathlibExt.Complexity.NPComplete.AlgebraicEquationsOverGF2

/-- Well-formedness of an instance: a well-formed ALGEBRAIC EQUATIONS OVER GF[2] instance in
which no term involves more than two variables. -/
def WellFormed (i : AlgebraicEquationsOverGF2Instance) : Prop :=
  AlgebraicEquationsOverGF2.WellFormed i ∧ ∀ P ∈ i.2, ∀ t ∈ P, t.length ≤ 2

open Classical in
/-- ALGEBRAIC EQUATIONS OVER GF[2] with at most two variables per term as a decision problem
over bitstrings. -/
noncomputable def quadraticEquationsOverGF2Dec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AlgebraicEquationsOverGF2Instance) x with
  | some i => decide (WellFormed i ∧ AlgebraicEquationsOverGF2Feasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.QuadraticEquationsOverGF2
