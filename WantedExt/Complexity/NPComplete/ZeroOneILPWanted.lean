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

/-- **0-1 integer programming instances.** A 0-1 integer programming instance is a triple
$(n, A, b)$ consisting of a natural number $n$ (the number of variables), a coefficient matrix
$A$ given as a list of rows, each row a list of pairs of natural numbers, and a right-hand side
$b$ given as a list of pairs of natural numbers. A pair $(p, q)$ is read as the integer $p - q$,
so coefficients and right-hand side entries are stored by positive and negative parts. -/
abbrev ZeroOneILPInstance := ℕ × List (List (ℕ × ℕ)) × List (ℕ × ℕ)

/-- **Well-formed 0-1 integer programming instances.** A 0-1 integer programming instance
$(n, A, b)$ is well formed when the right-hand side list $b$ has as many entries as there are
rows of the coefficient matrix $A$, and every row of $A$ has exactly $n$ entries. -/
def WellFormed (i : ZeroOneILPInstance) : Prop :=
  i.2.1.length = i.2.2.length ∧ ∀ row ∈ i.2.1, row.length = i.1

/-- **Feasible 0-1 integer programs.** Let $(n, A, b)$ be a 0-1 integer programming instance whose
coefficient matrix has the rows $A_0, \dots, A_{m-1}$, with list entries indexed from $0$. For
$r < m$ and $j < n$, let $a_{rj}$ be the integer $p - q$ if row $A_r$ has a $j$-th entry
$(p, q)$, and $a_{rj} = 0$ otherwise; let $b_r$ be the integer $p' - q'$ if $b$ has an $r$-th
entry $(p', q')$, and $b_r = 0$ otherwise. The instance is feasible when there is
$x \in \{0, 1\}^n$ such that $\sum_{j < n} a_{rj} x_j \le b_r$ in $\mathbb{Z}$ for every $r < m$. -/
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
/-- **0-1 integer programming feasibility as a decision problem.** The decision problem 0-1
INTEGER PROGRAMMING FEASIBILITY accepts a bitstring $x$ exactly when $x$ decodes, under the
canonical bitstring encoding, to a 0-1 integer programming instance that is well formed and
feasible; it rejects every bitstring that does not decode to such an instance. -/
noncomputable def zeroOneILPDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ZeroOneILPInstance) x with
  | some i => decide (WellFormed i ∧ ZeroOneILPFeasible i)
  | none => false

/-- **0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete.** The decision problem 0-1 INTEGER
PROGRAMMING FEASIBILITY belongs to NP, and every decision problem in NP has a polynomial-time
many-one reduction to it.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), 0-1 INTEGER PROGRAMMING; R. M. Karp,
"Reducibility among combinatorial problems" (1972). -/
public theorem_wanted zeroOneILP_npComplete :
    zeroOneILPDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zeroOneILPDec

end MetaMathlibExt.Complexity.NPComplete.ZeroOneILP
