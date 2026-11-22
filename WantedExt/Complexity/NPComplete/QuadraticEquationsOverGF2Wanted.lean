/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALGEBRAIC EQUATIONS OVER GF[2] with at most two variables per term is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN9] ALGEBRAIC EQUATIONS OVER GF[2],
p. 251, comment: "Remains NP-complete even if none of the polynomials has a term involving more
than two variables", credited there to L. G. Valiant (1977, private communication; not
available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.AlgebraicEquationsOverGF2Wanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticEquationsOverGF2

open MetaMathlibExt.Complexity.NPComplete.AlgebraicEquationsOverGF2

/-!
# ALGEBRAIC EQUATIONS OVER GF[2] with at most two variables per term is NP-complete

INSTANCE: polynomials `P₁, …, Pₘ` over `GF[2]` in the variables `x₁, …, xₙ`, each a sum of terms,
each term either `1` or a product of distinct variables, and no term involving more than two
variables. QUESTION: is there `(u₁, …, uₙ) ∈ {0, 1}ⁿ` with `Pᵢ(u₁, …, uₙ) = 0` for
`1 ≤ i ≤ m`?

This is the restriction of [AN9] ALGEBRAIC EQUATIONS OVER GF[2]
(`WantedExt.Complexity.NPComplete.AlgebraicEquationsOverGF2Wanted`) recorded in Garey and
Johnson's comment. The instance, its well-formedness and the question are those of the parent:
a term is the list of the indices of its variables (`[]` is the term `1`), with distinct indices
below `n`, so the number of variables of a term is the length of its list. The restriction adds
that every term has at most two variables. Garey and Johnson add that the problem is solvable in
polynomial time if no term involves more than one variable.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **ALGEBRAIC EQUATIONS OVER GF[2] with at most two variables per term is NP-complete.**
Source: Garey and Johnson (1979), [AN9], comment (credited to Valiant). -/
public theorem_wanted quadraticEquationsOverGF2_npComplete :
    quadraticEquationsOverGF2Dec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticEquationsOverGF2Dec

end MetaMathlibExt.Complexity.NPComplete.QuadraticEquationsOverGF2
