/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CORE STABLE PARTITION EXISTENCE in hedonic games is NP-complete

Source:
C. Ballester, "NP-completeness in hedonic games", Games and Economic Behavior 49 (2004), 1-30,
doi:10.1016/j.geb.2003.10.003;
G. J. Woeginger, "Core stability in hedonic coalition formation", SOFSEM 2013, Lecture Notes in
Computer Science 7741, 33-50, doi:10.1007/978-3-642-35843-2_4 (Definition 2.1 and
Theorem 3.2, restating Ballester's result under the individually rational encoding).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HedonicCoreStablePartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HedonicCoreStablePartition

/-!
# CORE STABLE PARTITION EXISTENCE in hedonic games is NP-complete

INSTANCE: a hedonic game: a finite set `N` of players and, for each player `i`, a preference
relation `⪯ᵢ` (reflexive, transitive and complete; ties allowed) over the coalitions `S ⊆ N`
with `i ∈ S`, given in the individually rational encoding: player `i` lists exactly the
coalitions `S` with `{i} ⪯ᵢ S`, ranked. QUESTION: is there a core stable partition of `N`,
i.e., a partition `Π` such that no coalition `S` blocks `Π`, where `S` blocks `Π` if every
player `i ∈ S` strictly prefers `S` to the coalition `Π(i)` of `Π` containing `i`?

Each player `p` lists pairs `(S, r)`: a listed coalition `S` and its rank `r`, a smaller rank
being better and equal ranks meaning indifference. `WellFormed` says that each listed
coalition consists of players and contains `p`, that no coalition is listed twice by `p`, that
`{p}` is listed, and that every listed coalition is ranked no worse than `{p}` (the listed
coalitions are individually rational). Coalitions that `p` does not list are not individually
rational: `p` strictly prefers `{p}`, hence every listed coalition, to each of them. The
encoding leaves their order among themselves open; core stability does not depend on it, and
they are taken as mutually indifferent: if a coalition of `Π` is not individually rational for
one of its members `p`, then `{p}` blocks `Π`; otherwise a blocking coalition is individually
rational for each of its members, so only listed ranks are compared. Partitions of the
players are Mathlib's `Finpartition` of `Finset.univ`, and `Π(p)` is `Finpartition.part`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CORE STABLE PARTITION EXISTENCE in hedonic games (individually rational encoding) is
NP-complete.** Source: Ballester (2004); Woeginger (2013), Theorem 3.2. -/
public theorem_wanted hedonicCoreStablePartition_npComplete :
    hedonicCoreStablePartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hedonicCoreStablePartitionDec

end MetaMathlibExt.Complexity.NPComplete.HedonicCoreStablePartition
