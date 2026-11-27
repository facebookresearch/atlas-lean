/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.CliqueHardness
public import CSLibExt.Computability.Complexity.Parameterized.CliqueTable
public import CSLibExt.Computability.Complexity.Parameterized.WeftMachine

/-!
# Parameterized Clique is W[1]-complete

The membership reduction uses depth-three circuits and preserves the clique
size. For hardness, each fixed depth gives a TM2 transformation from
weighted weft-one circuit satisfiability to a single clique query. The
construction counts all input and output bits in the ATLAS machine model.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

/-- **Parameterized complexity: FPT and W[1]-completeness of Clique.** Write $W[t]$ for the
$t$-th level of the W-hierarchy. The parameterized $k$-Clique problem lies in $W[1]$, and every
parameterized problem in $W[1]$ has an FPT-reduction to it. Every fixed-parameter tractable
parameterized problem lies in $W[1]$. For every $t \in \mathbb{N}$, $W[t] \subseteq W[t + 1]$.

Source: R. G.
Downey and M. R. Fellows, Parameterized Complexity, Springer, 1999 (W[1]-completeness of
Clique); J. Flum and M. Grohe, Parameterized Complexity Theory, Springer, 2006. -/
theorem parameterized_clique_w1_complete :
    (CliqueParam ∈ WLevel 1 ∧ ∀ P ∈ WLevel 1, FPTReduces P CliqueParam) ∧
    (∀ P : ParamProblem, FPT P → P ∈ WLevel 1) ∧
    ∀ t : ℕ, WLevel t ⊆ WLevel (t + 1) :=
  ⟨⟨CliqueMembership.clique_mem_wLevel, clique_wOne_hard⟩,
    fun _ h => h.mem_wLevel 1, wLevel_subset_succ⟩

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
