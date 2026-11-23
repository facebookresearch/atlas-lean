/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSEST STRING is NP-complete

Source:
J. K. Lanctot et al., "Distinguishing string selection problems" (2003); M. Frances and A.
Litman, "On covering problems of codes" (1997).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosestString

/-!
# CLOSEST STRING is NP-complete

A list of binary strings, all of the same length, and a distance bound `d`. The question is
whether there is a center string of the same length within Hamming distance `d` of every given
string.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Closest-string instances.** A closest-string instance is a pair $(S, d)$ of a finite list
$S$ of bitstrings (finite lists of booleans) and a natural number $d$, the distance bound.

The bitstrings are not required to have equal length; that is the well-formedness condition. -/
abbrev ClosestStringInstance := List (List Bool) × ℕ

/-- **Well-formed closest-string instances.** A closest-string instance $(S, d)$ is well formed
when all bitstrings in the list $S$ have the same length. -/
def WellFormed (i : ClosestStringInstance) : Prop :=
  ∀ s ∈ i.1, ∀ t ∈ i.1, s.length = t.length

/-- **Feasible closest-string instances.** Write $\ell(x)$ for the length of a bitstring $x$.
A closest-string instance $(S, d)$ is feasible when there is a bitstring $c$ with
$\ell(c) = \ell(s_1)$, where $s_1$ is the first bitstring of $S$ (and $\ell(c) = 0$ if $S$ is
empty), such that for every $s$ in $S$ the number of positions $j < \min(\ell(c), \ell(s))$ at
which $c$ and $s$ differ is at most $d$.

If all bitstrings of $S$ have length $\ell(c)$, this number is the Hamming distance between $c$
and $s$. -/
def ClosestStringFeasible
    (i : ClosestStringInstance) : Prop :=
  ∃ center : List Bool, center.length = (i.1.getD 0 []).length ∧
    ∀ s ∈ i.1, ((List.zip center s).filter (fun p => !(p.1 == p.2))).length ≤ i.2

open Classical in
/-- **The CLOSEST STRING decision problem.** The decision problem CLOSEST STRING accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of
closest-string instances, to an instance that is well formed and feasible. Bitstrings that do
not decode to a closest-string instance are rejected. -/
noncomputable def closestStringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClosestStringInstance) x with
  | some i => decide (WellFormed i ∧ ClosestStringFeasible i)
  | none => false

/-- **CLOSEST STRING is NP-complete.** The CLOSEST STRING decision problem belongs to NP, and
every decision problem in NP has a polynomial-time many-one reduction to it.

Source: J. K. Lanctot et al., "Distinguishing string
selection problems" (2003); M. Frances and A. Litman, "On covering problems of codes"
(1997). -/
public theorem_wanted closestString_npComplete :
    closestStringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L closestStringDec

end MetaMathlibExt.Complexity.NPComplete.ClosestString
