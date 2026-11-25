/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.GraphonSampling

namespace MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits.GraphonSampling

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted
open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)
open MeasureTheory Filter Topology

-- In the constant graphon `c`, the edge has density `c` and the triangle density `c ^ 3`.
private lemma graphonHomDensity_top_two (c : ℝ) :
    graphonHomDensity (⊤ : SimpleGraph (Fin 2)) (fun _ _ => c) = c := by
  simp (config := { decide := true }) [graphonHomDensity, Fin.prod_univ_two, measureReal_def,
    Real.volume_Icc_pi]

private lemma graphonHomDensity_top_three (c : ℝ) :
    graphonHomDensity (⊤ : SimpleGraph (Fin 3)) (fun _ _ => c) = c ^ 3 := by
  simp (config := { decide := true }) [graphonHomDensity, Fin.prod_univ_three, measureReal_def,
    Real.volume_Icc_pi]
  ring

-- Quasirandom graphs exist: for every `p ∈ [0, 1]` there are nonempty graphs whose edge density
-- tends to `p` and whose triangle density tends to `p ^ 3`.
example {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (N : ℕ → ℕ) (G : ∀ n, SimpleGraph (Fin (N n))) (_ : ∀ n, DecidableRel (G n).Adj),
      (∀ n, 0 < N n) ∧
      Tendsto (fun n => homDensity (⊤ : SimpleGraph (Fin 2)) (adjWeight (G n))) atTop (𝓝 p) ∧
      Tendsto (fun n => homDensity (⊤ : SimpleGraph (Fin 3)) (adjWeight (G n))) atTop
        (𝓝 (p ^ 3)) := by
  obtain ⟨N, G, inst, hN, h⟩ := exists_graph_sequence_tendsto (W := fun _ _ => p)
    ⟨measurable_const, fun _ _ => rfl, fun _ _ => hp⟩
  refine ⟨N, G, inst, hN, ?_, ?_⟩
  · simpa [graphonHomDensity_top_two] using h 2 ⊤
  · simpa [graphonHomDensity_top_three] using h 3 ⊤

-- The graphs of the sequence are nonempty, so the edgeless graph on `k` vertices has density `1`
-- along the sequence, as in every graphon.
example {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) (k : ℕ) :
    ∃ (N : ℕ → ℕ) (G : ∀ n, SimpleGraph (Fin (N n))) (_ : ∀ n, DecidableRel (G n).Adj),
      ∀ n, homDensity (⊥ : SimpleGraph (Fin k)) (adjWeight (G n)) = 1 := by
  obtain ⟨N, G, inst, hN, -⟩ := exists_graph_sequence_tendsto hW
  refine ⟨N, G, inst, fun n => ?_⟩
  have : Nonempty (Fin (N n)) := ⟨⟨0, hN n⟩⟩
  exact homDensity_bot _

end MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits.GraphonSampling
