/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KERNEL is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT57] KERNEL;
V. Chvátal, "On the computational complexity of finding a kernel", Report CRM-300, Centre de
recherches mathématiques, Université de Montréal (1973) (the author's reconstruction of the
proof: https://users.encs.concordia.ca/~chvatal/kernel.html);
A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, d_out ≤ 2, d_in ≤ 2 are NP-complete",
Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KernelDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kernel

/-!
# KERNEL is NP-complete

Given a directed graph `G = (V, A)`, does `G` have a kernel, i.e., a subset `V' ⊆ V` such that
no two vertices of `V'` are joined by an arc, and every vertex `u ∈ V - V'` has an arc
`(u, v)` to some `v ∈ V'`?

The digraph has vertices `Fin n` and is given by its arc list; it is finite, with no loops
and no multiple arcs (`WellFormed`). Opposite arcs `u → v`, `v → u` may both be present.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **KERNEL is NP-complete.** Source: Garey and Johnson (1979), [GT57]; Chvátal (1973);
Fraenkel (1981). -/
public theorem_wanted kernel_npComplete :
    kernelDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kernelDec

end MetaMathlibExt.Complexity.NPComplete.Kernel
