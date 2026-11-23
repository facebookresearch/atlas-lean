/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER KNAPSACK with `s(u) = v(u)` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP10] INTEGER KNAPSACK, comment
(p. 247): "Remains NP-complete if `s(u) = v(u)` for all `u ∈ U`" (reference of the entry:
[Lueker, 1975], G. S. Lueker, "Two NP-complete problems in nonnegative integer programming",
Report 178, Computer Science Laboratory, Princeton University (1975); transformation from
SUBSET SUM).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnboundedKnapsackWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegerKnapsackEqualSizeValue

open UnboundedKnapsack (UnboundedKnapsackInstance UnboundedKnapsackFeasible)

/-!
# INTEGER KNAPSACK with `s(u) = v(u)` is NP-complete

INSTANCE: a finite set `U`, for each `u ∈ U` a size `s(u) ∈ Z⁺` and a value `v(u) ∈ Z⁺` with
`s(u) = v(u)`, and positive integers `B` and `K`.
QUESTION: is there an assignment of a non-negative integer `c(u)` to each `u ∈ U` such that
`∑_{u ∈ U} c(u) · s(u) ≤ B` and such that `∑_{u ∈ U} c(u) · v(u) ≥ K`?

This is the restriction of [MP10] INTEGER KNAPSACK stated in its comment. INTEGER KNAPSACK is
`WantedExt.Complexity.NPComplete.UnboundedKnapsackWanted` (items as `(s(u), v(u))` pairs, the
capacity `B`, the target `K`; multiplicities `c(u)` as a list of naturals); its instance type and
`UnboundedKnapsackFeasible` are reused unchanged. That module has no well-formedness condition
(it admits zero sizes and bounds); here `WellFormed` states the source's instance class: every
item has `s(u) = v(u)` and `s(u) > 0`, and `B, K > 0`. Numbers use the binary encoding (the
problem is solvable in pseudo-polynomial time, as the comment notes).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: every item `(s(u), v(u))` has `s(u) = v(u)` and
`0 < s(u)`, and `B` and `K` are positive. -/
def WellFormed (i : UnboundedKnapsackInstance) : Prop :=
  (∀ u ∈ i.1, u.1 = u.2 ∧ 0 < u.1) ∧ 0 < i.2.1 ∧ 0 < i.2.2

open Classical in
/-- INTEGER KNAPSACK with `s(u) = v(u)` as a decision problem over bitstrings. -/
noncomputable def integerKnapsackEqualSizeValueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnboundedKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ UnboundedKnapsackFeasible i)
  | none => false

/-- **INTEGER KNAPSACK with `s(u) = v(u)` is NP-complete.**
Source: Garey and Johnson (1979), [MP10], comment; Lueker (1975). -/
public theorem_wanted integerKnapsackEqualSizeValue_npComplete :
    integerKnapsackEqualSizeValueDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integerKnapsackEqualSizeValueDec

end MetaMathlibExt.Complexity.NPComplete.IntegerKnapsackEqualSizeValue
