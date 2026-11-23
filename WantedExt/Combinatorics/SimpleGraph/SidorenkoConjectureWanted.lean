/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.Graphon
public import WantedExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted

/-!
# Sidorenko's conjecture

The open conjecture of Sidorenko (and, in a weaker form, Erdős–Simonovits) that among all graphons
of a given edge density the constant one minimizes the density of every bipartite graph, in the
graphon form of Lovász, *Subgraph densities in signed graphons and the local Sidorenko conjecture*,
Electron. J. Combin. 18 (2011), §1, inequality (1). The four-cycle case is proved for finite
weighted graphs in `MathlibExt.Combinatorics.SimpleGraph.GraphLimits.SidorenkoFourCycle`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.SidorenkoConjectureWanted

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)

/-- **Sidorenko's conjecture** (open). For every bipartite simple graph `F` and every graphon `W`
(symmetric, values in `[0, 1]`), `t(F, W) ≥ t(K₂, W) ^ |E(F)|`. This is the graph form
`t(F, G) ≥ t(K₂, G) ^ |E(F)|` of Lovász, *Subgraph densities in signed graphons and the local
Sidorenko conjecture*, Electron. J. Combin. 18 (2011), §1, extended to graphons, which are limits of
graphs. Sidorenko's analytic form, inequality (1) there, is more general: it allows bounded
measurable `W ≥ 0` that need not be symmetric, and it implies the form stated here. Known cases
listed there include trees, bigraphs with a colour class of at most four nodes, and cubes. -/
def SidorenkoConjecture : Prop :=
  ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj], F.IsBipartite →
    ∀ W : ℝ → ℝ → ℝ, IsGraphon W →
      graphonHomDensity (⊤ : SimpleGraph (Fin 2)) W ^ F.edgeFinset.card ≤ graphonHomDensity F W

/-- **Sidorenko's inequality for the four-cycle, graphon form.** For every graphon `W`,
`t(C₄, W) ≥ t(K₂, W) ^ 4` (Lovász, *Subgraph densities in signed graphons and the local Sidorenko
conjecture*, Electron. J. Combin. 18 (2011), §1: Sidorenko proved inequality (1) for bigraphs with
a colour class of at most four nodes, a class containing `C₄ = K_{2,2}`). The finite weighted-graph
case is `homDensity_cycleGraph_four_ge`. -/
public theorem_wanted graphonHomDensity_cycleGraph_four_ge {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) :
    graphonHomDensity (⊤ : SimpleGraph (Fin 2)) W ^ 4 ≤
      graphonHomDensity (SimpleGraph.cycleGraph 4) W

end MathlibExt.Combinatorics.SimpleGraph.SidorenkoConjectureWanted
