/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNORDERED TREE EDIT DISTANCE is NP-complete

Source:
K. Zhang, R. Statman and D. Shasha, "On the editing distance between unordered labeled trees",
Information Processing Letters 42(3) (1992), 133-139, doi:10.1016/0020-0190(92)90136-J
(NP-complete even for binary trees over a two-letter label alphabet);
R. D. M. Page and G. Valiente, "An edit script for taxonomic classifications", BMC
Bioinformatics 6 (2005), 208, doi:10.1186/1471-2105-6-208 (records the result for the least
number of operations);
R. Sridharamurthy, T. B. Masood, A. Kamakshidasan and V. Natarajan, "Edit distance between merge
trees", IEEE Transactions on Visualization and Computer Graphics 26(3) (2020), 1518-1531,
doi:10.1109/TVCG.2018.2873612, arXiv:2207.08511 (Section 2.3 and Section 3.1: the edit
operations, and the edit distance as the cost of a cheapest one-to-one, ancestor-preserving
mapping).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnorderedTreeEditDistanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnorderedTreeEditDistance

/-!
# UNORDERED TREE EDIT DISTANCE is NP-complete

INSTANCE: two rooted unordered node-labeled trees `T₁`, `T₂` and an integer `K`; the edit
operations, each of unit cost, are: relabel a node; delete a node `v` (the children of `v` become
children of the parent of `v`); insert a node (the inverse of a deletion).
QUESTION: can `T₁` be transformed into `T₂` with at most `K` edit operations?

A tree on `n` nodes is given by a list of `n` pairs `(parent code, label)`: code `0` marks the
root and code `k + 1` names node `k` as the parent; labels are natural numbers. Trees are
unordered: the children of a node form a set, so trees, and the forests met along an edit
sequence, are compared up to renaming of nodes (`Iso`), and each edit step relates two
forests up to renaming. Deleting the root makes its children roots, so an edit sequence may
pass through forests; this is the model in which the edit distance equals the cost of a
cheapest one-to-one, ancestor-preserving mapping between the node sets, with no condition on
the roots (Zhang, Statman and Shasha; Sridharamurthy et al., Section 3.1). Inserting a node
`v` under a node `w` (or as a new root) makes `v` the parent of any subset of the children of
`w` (of the roots).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNORDERED TREE EDIT DISTANCE is NP-complete.** Source: Zhang, Statman and Shasha (1992). -/
public theorem_wanted unorderedTreeEditDistance_npComplete :
    unorderedTreeEditDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unorderedTreeEditDistanceDec

end MetaMathlibExt.Complexity.NPComplete.UnorderedTreeEditDistance
