/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.LimitTheorem
import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.SidorenkoFourCycle

namespace MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits.LimitTheorem

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted
open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)
open Filter Topology
open _root_.SimpleGraph (cycleGraph)

-- A constant sequence converges, so the homomorphism densities of every graph with a vertex are
-- the homomorphism densities of a graphon.
example {m : ℕ} (hm : 0 < m) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] :
    ∃ W : ℝ → ℝ → ℝ, IsGraphon W ∧ ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
      graphonHomDensity F W = homDensity F (adjWeight G) := by
  obtain ⟨W, hW, h⟩ := exists_graphon_limit (N := fun _ => m) (fun _ => G) (fun _ => hm)
    (fun k F _ => ⟨_, tendsto_const_nhds⟩)
  exact ⟨W, hW, fun k F _ => tendsto_nhds_unique (h k F) tendsto_const_nhds⟩

-- Sidorenko's inequality `t(C₄, G) ≥ t(K₂, G) ^ 4` for finite graphs passes to the limit graphon of
-- every convergent graph sequence.
example {N : ℕ → ℕ} (G : ∀ n, SimpleGraph (Fin (N n))) [∀ n, DecidableRel (G n).Adj]
    (hN : ∀ n, 0 < N n) (hG : IsConvergentGraphSequence G) :
    ∃ W : ℝ → ℝ → ℝ, IsGraphon W ∧
      graphonHomDensity (⊤ : SimpleGraph (Fin 2)) W ^ 4 ≤
        graphonHomDensity (cycleGraph 4) W := by
  obtain ⟨W, hW, h⟩ := exists_graphon_limit G hN hG
  exact ⟨W, hW, le_of_tendsto_of_tendsto' ((h 2 ⊤).pow 4) (h 4 (cycleGraph 4))
    fun n => homDensity_cycleGraph_four_ge (adjWeight (G n))⟩

end MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits.LimitTheorem
