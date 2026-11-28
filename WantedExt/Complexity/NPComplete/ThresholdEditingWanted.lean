/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THRESHOLD EDITING is NP-complete

Source:
P. G. Drange, M. S. Dregi, D. Lokshtanov and B. D. Sullivan, "On the threshold of
intractability", Journal of Computer and System Sciences 124 (2022), 1-25,
doi:10.1016/j.jcss.2021.09.003 (conference version: ESA 2015, LNCS 9294, 411-423).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThresholdEditingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThresholdEditing

/-!
# THRESHOLD EDITING is NP-complete

INSTANCE: a graph `G = (V, E)` and a nonnegative integer `K`. QUESTION: can `G` be transformed
into a threshold graph by adding and deleting at most `K` edges?

The edited graph is a graph `H` on the same vertex set `V`; the edits are the edges in exactly
one of `G` and `H`, the symmetric difference of the edge sets, so the question is whether some
threshold graph `H` on `V` has `|E(G) ∆ E(H)| ≤ K`. "Threshold graph" is the Chvátal-Hammer
definition shared with `WantedExt.Complexity.NPComplete.ThresholdNumberWanted`
(`ThresholdNumber.IsThresholdGraph`: real weights `a` and a bound `b` such that a vertex set is a
clique exactly when its weight is at most `b`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **THRESHOLD EDITING is NP-complete.** Source: Drange, Dregi, Lokshtanov and Sullivan
(2022). -/
public theorem_wanted thresholdEditing_npComplete :
    thresholdEditingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L thresholdEditingDec

end MetaMathlibExt.Complexity.NPComplete.ThresholdEditing
