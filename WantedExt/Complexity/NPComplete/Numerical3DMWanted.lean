/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NUMERICAL 3-DIMENSIONAL MATCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), NUMERICAL 3-DIMENSIONAL
MATCHING (strongly NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Numerical3DM

/-!
# NUMERICAL 3-DIMENSIONAL MATCHING is NP-complete

Three lists `A, B, C` of the same length `n` and a common target `B`. The question is whether
permutations `p, q` satisfy `A_i + B_{p(i)} + C_{q(i)} = Target` for every `i`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Numerical 3-dimensional matching instances.** An instance of NUMERICAL 3-DIMENSIONAL
MATCHING is a quadruple $(A, B, C, t)$ of three finite lists $A$, $B$, $C$ of natural numbers
and a natural number $t$, the target. -/
abbrev Numerical3DMInstance := List ℕ × List ℕ × List ℕ × ℕ

/-- **Well-formed numerical 3-dimensional matching instances.** An instance $(A, B, C, t)$ of
NUMERICAL 3-DIMENSIONAL MATCHING is well formed when the lists $B$ and $C$ have the same length
as the list $A$. -/
def WellFormed (i : Numerical3DMInstance) : Prop :=
  i.2.1.length = i.1.length ∧ i.2.2.1.length = i.1.length

/-- **Feasible numerical 3-dimensional matching instances.** Let $(A, B, C, t)$ be an instance
and let $n$ be the length of $A$, with lists indexed from $0$. The instance is feasible when
there are permutations $p$ and $q$ of the numbers $0$ through $n-1$ such that
$A_j + B_{p(j)} + C_{q(j)} = t$ for every $j < n$, where an entry of $B$ or $C$ at an index past
the end of its list counts as $0$. -/
def Numerical3DMFeasible
    (i : Numerical3DMInstance) : Prop :=
  ∃ p : List ℕ, p.Perm (List.range i.1.length) ∧
    ∃ q : List ℕ, q.Perm (List.range i.1.length) ∧
    ∀ j < i.1.length, i.1.getD j 0 + i.2.1.getD (p.getD j 0) 0 +
      i.2.2.1.getD (q.getD j 0) 0 = i.2.2.2

open Classical in
/-- **NUMERICAL 3-DIMENSIONAL MATCHING as a decision problem.** The decision problem NUMERICAL
3-DIMENSIONAL MATCHING accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding (natural numbers in binary), to an instance $(A, B, C, t)$ that is well
formed and feasible: the lists $B$ and $C$ have the same length $n$ as the list $A$, and there
are permutations $p$ and $q$ of the numbers $0$ through $n-1$ such that
$A_j + B_{p(j)} + C_{q(j)} = t$ for every $j < n$, with lists indexed from $0$. Every other
bitstring is rejected. -/
noncomputable def numerical3DMDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := Numerical3DMInstance) x with
  | some i => decide (WellFormed i ∧ Numerical3DMFeasible i)
  | none => false

/-- **NUMERICAL 3-DIMENSIONAL MATCHING is NP-complete.** The decision problem NUMERICAL
3-DIMENSIONAL MATCHING belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), NUMERICAL 3-DIMENSIONAL MATCHING (strongly
NP-complete). -/
public theorem_wanted numerical3DM_npComplete :
    numerical3DMDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L numerical3DMDec

end MetaMathlibExt.Complexity.NPComplete.Numerical3DM
