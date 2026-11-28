/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-PATH-FREE DOMINATING SET (directed) is NP-complete for every fixed k ≥ 2

Source:
R. Bar-Yehuda and U. Vishkin, "Complexity of finding k-path-free dominating sets in graphs",
Information Processing Letters 14 (1982), 228-232, doi:10.1016/0020-0190(82)90021-7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KPathFreeDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KPathFreeDominatingSet

open Kernel (KernelInstance Graph WellFormed)

/-!
# k-PATH-FREE DOMINATING SET (directed) is NP-complete for every fixed k ≥ 2

Fix an integer `k ≥ 2`. INSTANCE: a digraph `G = (V, E)`. QUESTION: is there a set `K ⊆ V` that
dominates `G` and contains no path of length `k`?

Bar-Yehuda and Vishkin (1982): "A subset `U`, `U ⊂ V` is a dominating set in a digraph `G(V, E)`
if every vertex `y ∈ V - U` has a vertex `x ∈ U` such that `x → y ∈ E`. A path of length `k` in
`G` is a simple directed path that contains `k` vertices", and the condition on `K` is "There is
no (directed) path of length `k` in `G` which uses only vertices of `K`". They prove that "for
every `k` (`k ≥ 2`) the existence problem of a solution which satisfies (1.1) and (1.2)' is
NP-complete". For `k = 2` the condition says that no arc joins two vertices of `K`, and the
problem is KERNEL (`KernelWanted`) with all arcs reversed.

The digraph is that of `KernelWanted` (vertices `Fin n`, given by an arc list with no repeated
arcs and no loops; the instance type, the digraph and `WellFormed` are reused). A path with `k`
vertices in `K` is an injective map `p : Fin k → Fin n` into `K` with an arc `p j → p (j + 1)`
for every `j + 1 < k`. The number `k` is a parameter of the problem, not part of the instance.

Membership in NP: the certificate is `K`; for fixed `k`, the absence of a simple path with `k`
vertices in the subdigraph induced by `K` is checked by trying the `O(n^k)` vertex sequences.
For `k ≥ 2` an isolated vertex has no in-arc, so it lies in every dominating set; isolated
vertices never lie on a path with `k ≥ 2` vertices, so they do not change the answer and the
binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **k-PATH-FREE DOMINATING SET is NP-complete for every fixed `k ≥ 2`.** Source:
Bar-Yehuda and Vishkin (1982). -/
public theorem_wanted kPathFreeDominatingSet_npComplete (k : ℕ) (_hk : 2 ≤ k) :
    kPathFreeDominatingSetDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (kPathFreeDominatingSetDec k)

end MetaMathlibExt.Complexity.NPComplete.KPathFreeDominatingSet
