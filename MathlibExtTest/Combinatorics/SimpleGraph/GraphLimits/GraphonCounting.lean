/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.GraphonCounting

namespace MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits.GraphonCounting

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted
open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)
open MeasureTheory

-- With no edges, changing every weight leaves the density unchanged, even with no vertices.
example (k : ℕ) {U W : ℝ → ℝ → ℝ} (hU : IsGraphon U) (hW : IsGraphon W) :
    graphonHomDensity (⊥ : SimpleGraph (Fin k)) U = graphonHomDensity (k := k) ⊥ W := by
  have h := abs_graphonHomDensity_sub_le (⊥ : SimpleGraph (Fin k)) hU hW
  rw [Finset.card_eq_zero.mpr ?_, Nat.cast_zero, zero_mul] at h
  · exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  · exact (@SimpleGraph.edgeFinset_eq_empty _ _ (SimpleGraph.fintypeEdgeSet _)).mpr rfl

-- A single edge detects the full difference of two constant graphons, in either order.
example {p q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |p - q| ≤ graphonCutNorm (fun _ _ => p - q) := by
  have density (c : ℝ) : graphonHomDensity (⊤ : SimpleGraph (Fin 2)) (fun _ _ => c) = c := by
    simp (config := { decide := true }) [graphonHomDensity, Fin.prod_univ_two,
      measureReal_def, Real.volume_Icc_pi]
  have h := abs_graphonHomDensity_sub_le (⊤ : SimpleGraph (Fin 2))
    (U := fun _ _ => p) (W := fun _ _ => q)
    ⟨measurable_const, fun _ _ => rfl, fun _ _ => hp⟩
    ⟨measurable_const, fun _ _ => rfl, fun _ _ => hq⟩
  rw [density, density, SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at h
  simpa using h

end MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits.GraphonCounting
