/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP WITH BOUNDED BUFFER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS17] TWO-PROCESSOR
FLOW-SHOP WITH BOUNDED BUFFER (with the definitions of [SS1], [SS14] and [SS15]);
C. H. Papadimitriou and P. C. Kanellakis, "Flowshop scheduling with limited
temporary storage", Journal of the ACM 27 (1980), 533-549,
doi:10.1145/322203.322213.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorFlowShopBoundedBufferDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopBoundedBuffer

/-!
# TWO-PROCESSOR FLOW-SHOP WITH BOUNDED BUFFER is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of two tasks `t₁[j]` and `t₂[j]`
(with `tᵢ[j]` to be executed by processor `i`), a length `l(t) ∈ ℤ₀⁺` for each such task `t`,
an overall deadline `D ∈ ℤ⁺`, and a "buffer bound" `B ∈ ℤ₀⁺` (this is FLOW-SHOP SCHEDULING
with `m = 2`, plus `B`).
QUESTION: is there a flow-shop schedule for `J` that meets the overall deadline and such that,
for all `u ≥ 0`, the number of jobs `j ∈ J` for which both `σ₁(j) + l(t₁[j]) ≤ u` and
`σ₂(j) > u` does not exceed `B`?

Following Garey and Johnson, a flow-shop schedule [SS15] meeting the deadline is an open-shop
schedule [SS14] meeting the deadline, i.e. one-processor schedules `σ₁, σ₂ : J → ℤ₀⁺` (each
one-to-one, with `σᵢ(j) > σᵢ(k)` implying `σᵢ(j) ≥ σᵢ(k) + l(tᵢ[k])` [SS1]) such that for
each `j ∈ J` the intervals `[σ₁(j), σ₁(j) + l(t₁[j]))` and `[σ₂(j), σ₂(j) + l(t₂[j]))` are
disjoint and `σᵢ(j) + l(tᵢ[j]) ≤ D`, with the additional constraint
`σ₂(j) ≥ σ₁(j) + l(t₁[j])` for each `j ∈ J`. A job counted at time `u` has finished on
processor 1 but not yet started on processor 2, so it occupies the buffer.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR FLOW-SHOP WITH BOUNDED BUFFER is NP-complete.** Source: Garey and
Johnson (1979), [SS17]; Papadimitriou and Kanellakis (1980). -/
public theorem_wanted twoProcessorFlowShopBoundedBuffer_npComplete :
    twoProcessorFlowShopBoundedBufferDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorFlowShopBoundedBufferDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopBoundedBuffer
