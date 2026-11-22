/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIRST ORDER SUBSUMPTION with a fixed number `n ≥ 3` of target expressions is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO18] FIRST ORDER SUBSUMPTION, comment ("Remains
NP-complete for any fixed `n ≥ 3`"; reference: [Baxter, 1976], [Baxter, 1977]), p. 264;
L. D. Baxter, *The Complexity of Unification*, Doctoral Thesis, Department of Computer Science,
University of Waterloo (1976);
L. D. Baxter, "The NP-completeness of subsumption", unpublished manuscript (1977).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FirstOrderSubsumptionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumptionFixedTargets

open MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption
  (FirstOrderSubsumptionInstance FirstOrderSubsumptionFeasible)

/-!
# FIRST ORDER SUBSUMPTION with a fixed number `n ≥ 3` of target expressions is NP-complete

FIRST ORDER SUBSUMPTION (`FirstOrderSubsumptionWanted`) with the size `n` of the collection
`F = {F₁, F₂, ..., Fₙ}` fixed. INSTANCE: a finite set `U` of "variable symbols", a finite set
`C` of "function symbols", a collection `E = {E₁, E₂, ..., Eₘ}` of expressions over `U ∪ C`, and
a collection `F = {F₁, F₂, ..., Fₙ}` of `n` expressions over `C`.
QUESTION: is there a substitution mapping `s` that assigns to each `u ∈ U` an expression `s(u)`
over `C` such that `{s(E₁), s(E₂), ..., s(Eₘ)}` is a subset of `{F₁, F₂, ..., Fₙ}`?

Garey and Johnson record that the problem "remains NP-complete for any fixed `n ≥ 3`, but is
solvable in polynomial time for any fixed `m`". This module states the first half: for every
fixed `n ≥ 3`, the problem restricted to instances with exactly `n` expressions in `F` is
NP-complete. The instances, their well-formedness and the question are those of
`FirstOrderSubsumptionWanted`; `F` is given as a list of `n` token lists, and since token lists
determine expressions, requiring them to be distinct makes `F` a set of `n` expressions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed `n`: it is a well-formed FIRST ORDER
SUBSUMPTION instance, and `F` consists of exactly `n` distinct expressions. -/
def WellFormed (n : ℕ) (i : FirstOrderSubsumptionInstance) : Prop :=
  FirstOrderSubsumption.WellFormed i ∧ i.2.2.2.length = n ∧ i.2.2.2.Nodup

open Classical in
/-- FIRST ORDER SUBSUMPTION with exactly `n` target expressions, as a decision problem over
bitstrings. -/
noncomputable def firstOrderSubsumptionFixedTargetsDec (n : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FirstOrderSubsumptionInstance) x with
  | some i => decide (WellFormed n i ∧ FirstOrderSubsumptionFeasible i)
  | none => false

/-- **FIRST ORDER SUBSUMPTION with a fixed number `n ≥ 3` of target expressions is
NP-complete.** Source: Garey and Johnson (1979), [LO18]; Baxter (1976, 1977). -/
public theorem_wanted firstOrderSubsumptionFixedTargets_npComplete (n : ℕ) (_hn : 3 ≤ n) :
    firstOrderSubsumptionFixedTargetsDec n ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (firstOrderSubsumptionFixedTargetsDec n)

end MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumptionFixedTargets
