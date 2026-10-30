/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 0-1 INTEGER PROGRAMMING;
R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ZeroOneILP

/-!
# 0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete

A system of integer linear inequalities in `n` binary variables and a right-hand side. Each
coefficient and each right-hand side entry is encoded as a pair of naturals `(positive part,
negative part)` representing their difference. The question is whether some assignment in `{0,
1}^n` satisfies all inequalities.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A 0-1 ILP instance: number of variables, coefficient matrix (positive, negative parts),
right-hand side. -/
abbrev ZeroOneILPInstance := ℕ × List (List (ℕ × ℕ)) × List (ℕ × ℕ)

/-- Well-formedness of an instance. -/
def WellFormed (i : ZeroOneILPInstance) : Prop :=
  i.2.1.length = i.2.2.length ∧ ∀ row ∈ i.2.1, row.length = i.1

/-- A binary assignment satisfying all inequalities. -/
def ZeroOneILPFeasible
    (i : ZeroOneILPInstance) : Prop :=
  ∃ x : List Bool, x.length = i.1 ∧
    ∀ r < i.2.1.length,
      ((Finset.range i.1).sum (fun j =>
        ((((i.2.1.getD r []).getD j (0, 0)).1 : ℤ) -
        (((i.2.1.getD r []).getD j (0, 0)).2 : ℤ)) *
        (if x.getD j false then (1 : ℤ) else 0))) ≤
      (((i.2.2.getD r (0, 0)).1 : ℤ) - ((i.2.2.getD r (0, 0)).2 : ℤ))

open Classical in
/-- 0-1 INTEGER PROGRAMMING FEASIBILITY as a decision problem over bitstrings. -/
noncomputable def zeroOneILPDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ZeroOneILPInstance) x with
  | some i => decide (WellFormed i ∧ ZeroOneILPFeasible i)
  | none => false

/-- **0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete.** Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), 0-1 INTEGER PROGRAMMING; R. M. Karp,
"Reducibility among combinatorial problems" (1972). -/
public theorem_wanted zeroOneILP_npComplete :
    zeroOneILPDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zeroOneILPDec

end MetaMathlibExt.Complexity.NPComplete.ZeroOneILP
