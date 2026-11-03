/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), ACHROMATIC NUMBER; M.
Farber et al., "The achromatic number of graphs" (1986).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumber

/-!
# ACHROMATIC NUMBER is NP-complete

An undirected graph and a bound `K`. The question is whether the achromatic number is at least
`K`: a proper coloring using some number `q ≥ K` of colors (colors `0, …, q - 1`, all used)
such that every pair of used colors appears on some edge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of ACHROMATIC NUMBER.** An instance of ACHROMATIC NUMBER is a triple $(n, E, K)$
of a natural number $n$ (the number of vertices), a finite list $E$ of ordered pairs of natural
numbers (the edges) and a natural number $K$ (the bound). -/
abbrev AchromaticNumberInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed ACHROMATIC NUMBER instances.** An instance $(n, E, K)$ of ACHROMATIC NUMBER is
well-formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$. -/
def WellFormed (i : AchromaticNumberInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible ACHROMATIC NUMBER instances.** An instance $(n, E, K)$ of ACHROMATIC NUMBER is
feasible when there are a natural number $q \ge K$ and a list $c = (c_0, \dots, c_{n-1})$ of $n$
natural numbers, with $c_u$ read as $0$ for $u \ge n$, such that $c_v < q$ for every $v < n$, every
$a < q$ equals $c_v$ for some $v < n$, $c_u \ne c_v$ for every pair $(u, v)$ in $E$, and for all
distinct $a, b < q$ some pair $(u, v)$ in $E$ has $(c_u, c_v) = (a, b)$ or
$(c_u, c_v) = (b, a)$. -/
def AchromaticNumberFeasible
    (i : AchromaticNumberInstance) : Prop :=
  ∃ q : ℕ, i.2.2 ≤ q ∧
    ∃ coloring : List ℕ, coloring.length = i.1 ∧ (∀ v < i.1, coloring.getD v 0 < q) ∧
    (∀ c < q, ∃ v < i.1, coloring.getD v 0 = c) ∧
    (∀ e ∈ i.2.1, coloring.getD e.1 0 ≠ coloring.getD e.2 0) ∧
    ∀ a < q, ∀ b < q, a ≠ b → ∃ e ∈ i.2.1,
      (coloring.getD e.1 0 = a ∧ coloring.getD e.2 0 = b) ∨
      (coloring.getD e.1 0 = b ∧ coloring.getD e.2 0 = a)

open Classical in
/-- **ACHROMATIC NUMBER as a decision problem.** The ACHROMATIC NUMBER decision problem accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of instances
$(n, E, K)$, to an instance of ACHROMATIC NUMBER that is well-formed and feasible; it rejects
every bitstring that does not decode to an instance. -/
noncomputable def achromaticNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AchromaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ AchromaticNumberFeasible i)
  | none => false

/-- **ACHROMATIC NUMBER is NP-complete.** The ACHROMATIC NUMBER decision problem belongs to NP, and
every decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), ACHROMATIC NUMBER; M. Farber et al., "The achromatic number of
graphs" (1986). -/
public theorem_wanted achromaticNumber_npComplete :
    achromaticNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L achromaticNumberDec

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumber
