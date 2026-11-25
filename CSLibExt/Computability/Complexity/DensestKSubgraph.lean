/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Defs
import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Canonical
import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Hardness.Reduction

namespace MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph

open Cslib.Complexity.DensestKSubgraph.Internal in
/-- **DENSEST k-SUBGRAPH is NP-complete.** The decision problem DENSEST k-SUBGRAPH belongs to the
class NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Source: U. Feige, G. Kortsarz, and D. Peleg, "The
dense k-subgraph problem" (2001); M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), DENSEST k-SUBGRAPH. -/
public theorem densestKSubgraph_npComplete :
    densestKSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L densestKSubgraphDec :=
  ⟨VerifierMachine.mem_NP, CliqueReduction.densest_npHard⟩

end MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
