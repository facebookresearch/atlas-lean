/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET SPLITTING for partial Steiner triple systems is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
182-195, doi:10.1016/0196-6774(82)90018-9 (recording the result of K. T. Phelps);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP4] SET SPLITTING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted
public import WantedExt.Complexity.NPComplete.SetSplittingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetSplittingPartialSteinerTripleSystems

/-!
# SET SPLITTING for partial Steiner triple systems is NP-complete

INSTANCE: a set `V` and a collection `C` of `3`-element subsets of `V` such that every pair of
elements of `V` lies in at most one member of `C` (a partial Steiner triple system). QUESTION: can
`V` be partitioned into two sets so that no member of `C` lies entirely within one of them?

This is Garey and Johnson's SET SPLITTING [SP4] (hypergraph 2-colorability) restricted to partial
Steiner triple systems. Johnson's NP-completeness column (J. Algorithms 3 (1982), in its
discussion of [SP4]) records: "Phelps [33] has shown that the problem is NP-complete for partial
Steiner triple systems (3-regular hypergraphs in which each pair of vertices occurs in at most one
hyperedge)"; Phelps's proof itself was not available. The column uses "3-regular hypergraphs"
for "instances where all hyperedges are of size 3", i.e. 3-uniform hypergraphs, not vertex
degree three. Membership in NP: the partition is a certificate.

The instance type, the parent well-formedness condition and the question are those of
`SetSplitting` (`SetSplitting.SetSplittingInstance`, `SetSplitting.WellFormed`,
`SetSplitting.SetSplittingFeasible`): `V = {0, ..., n - 1}`, the members of `C` are
duplicate-free lists of elements of `V`, and the question asks for a part `S ⊆ V` (the other part
being `V \ S`) that every member meets and does not contain. `WellFormed` adds the restriction:
the members of `C`, read as subsets of `Fin n` (`tripleFamily`), form a partial Steiner triple
system in the sense of `IsLinearTripleSystem` (every member has three elements and two distinct
members share at most one element, i.e. every pair lies in at most one member). A member listed
twice is the same member of the collection.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted
  (IsLinearTripleSystem)

/-- The members of `C` as a family of subsets of `Fin n`. -/
def tripleFamily (i : SetSplitting.SetSplittingInstance) : Finset (Finset (Fin i.1)) :=
  (i.2.map fun c => Finset.univ.filter fun v : Fin i.1 => (v : ℕ) ∈ c).toFinset

/-- Well-formedness of an instance: it is a well-formed SET SPLITTING instance (every member is
a duplicate-free list of elements of `V`), and the members form a partial Steiner triple system
(`IsLinearTripleSystem`). -/
def WellFormed (i : SetSplitting.SetSplittingInstance) : Prop :=
  SetSplitting.WellFormed i ∧ IsLinearTripleSystem (tripleFamily i)

open Classical in
/-- SET SPLITTING for partial Steiner triple systems as a decision problem over bitstrings. -/
noncomputable def setSplittingPartialSteinerTripleSystemsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetSplitting.SetSplittingInstance) x with
  | some i => decide (WellFormed i ∧ SetSplitting.SetSplittingFeasible i)
  | none => false

/-- **SET SPLITTING is NP-complete for partial Steiner triple systems.** Source: Johnson (1982),
recording Phelps; Garey and Johnson (1979), [SP4]. -/
public theorem_wanted setSplittingPartialSteinerTripleSystems_npComplete :
    setSplittingPartialSteinerTripleSystemsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setSplittingPartialSteinerTripleSystemsDec

end MetaMathlibExt.Complexity.NPComplete.SetSplittingPartialSteinerTripleSystems
