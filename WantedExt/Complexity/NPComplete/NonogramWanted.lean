/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NONOGRAM is NP-complete

Source:
N. Ueda and T. Nagao, "NP-completeness results for nonogram via parsimonious reductions"
(1996).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nonogram

/-!
# NONOGRAM is NP-complete

Row and column run-length clues for a two-color picture. The question is whether there is a
picture (rows of Booleans) whose rows and columns have exactly the given runs of consecutive
true cells, where runs are the maximal blocks of true cells in order.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Nonogram instances.** A nonogram instance is a pair $(R, C)$ of finite lists, the row clues
$R$ and the column clues $C$, where each clue is a finite list of natural numbers. -/
abbrev NonogramInstance := List (List ℕ) × List (List ℕ)


/-- **One step of the run-length computation.** For a Boolean $b$ and a pair $(k, R)$ of a
natural number $k$ and a finite list $R$ of natural numbers, the step returns $(k + 1, R)$ if $b$
is true. If $b$ is false it returns $(0, R)$ when $k = 0$, and $(0, R')$ when $k > 0$, where $R'$
is the list $R$ with $k$ prepended.

Here $k$ is the length of the current run of true cells and $R$ is the list of completed runs. -/
def RunsStep (b : Bool) (acc : ℕ × List ℕ) : ℕ × List ℕ :=
  if b then (acc.1 + 1, acc.2) else (0, if acc.1 = 0 then acc.2 else acc.1 :: acc.2)

/-- **Run lengths of a row.** For a finite list $l$ of Booleans, the runs of $l$ are its maximal
blocks of consecutive true entries. The run list of $l$ is the list of the lengths of these
blocks, in order from left to right; it is empty when $l$ has no true entry. -/
def Runs (l : List Bool) : List ℕ :=
  let acc := l.foldr RunsStep (0, [])
  if acc.1 = 0 then acc.2 else acc.1 :: acc.2


/-- **Feasible nonogram instances.** A nonogram instance with row clues $R_0, \dots, R_{m-1}$ and
column clues $C_0, \dots, C_{n-1}$ is feasible when there is a picture, a list of $m$ rows of
Booleans each of length $n$, such that for every $r < m$ the run list of row $r$ equals $R_r$,
and for every $c < n$ the run list of column $c$, read from row $0$ to row $m - 1$, equals $C_c$.
-/
def NonogramFeasible
    (i : NonogramInstance) : Prop :=
  ∃ picture : List (List Bool), picture.length = i.1.length ∧
    (∀ row ∈ picture, row.length = i.2.length) ∧
    (∀ r < i.1.length, Runs (picture.getD r []) = i.1.getD r []) ∧
    ∀ c < i.2.length, Runs ((List.range picture.length).map
      (fun r => (picture.getD r []).getD c false)) = i.2.getD c []

open Classical in
/-- **The NONOGRAM decision problem.** NONOGRAM is the decision problem that accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding of nonogram instances, to a
feasible nonogram instance. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def nonogramDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonogramInstance) x with
  | some i => decide (NonogramFeasible i)
  | none => false

/-- **NONOGRAM is NP-complete.** The NONOGRAM decision problem belongs to NP, and every decision
problem in NP reduces to NONOGRAM by a polynomial-time many-one reduction.

Source: N. Ueda and T. Nagao, "NP-completeness results for
nonogram via parsimonious reductions" (1996). -/
public theorem_wanted nonogram_npComplete :
    nonogramDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonogramDec

end MetaMathlibExt.Complexity.NPComplete.Nonogram
