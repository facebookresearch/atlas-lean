/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.ArrayCrossingContradiction

/-!
# Tests for `Sheffield.ArrayCrossingContradiction`

Module under test: `Sheffield.ArrayCrossingContradiction` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

The two real-array lemmas conclude `False`; they are exercised on explicit tables where all other
hypotheses hold, so each refutes its remaining hypothesis:
* `adjacent_height_array_contradiction_of_endpoint_and_uniform_limits`: all-one tables cannot
  satisfy the uniform limits;
* `adjacent_height_array_contradiction_of_primal_dual_limits`: all-one primal and zero dual
  tables cannot satisfy the dual limits;
* `PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_max_limits` elaborates
  (check-only; no concrete planar dual pair is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace ArrayCrossingContradiction

open _root_.StatMech.FK.PeriodicPlanar Filter

-- All-one tables: the uniform limits (which force vanishing minima) fail.
example : ¬ ∀ k : ℕ → ℕ, (∀ n, k n < 0 + 1) →
    Tendsto (fun _ : ℕ => max (1 : ℝ) 1) atTop (nhds 1) ∧
      Tendsto (fun _ : ℕ => min (1 : ℝ) 1) atTop (nhds 0) ∧
      Tendsto (fun _ : ℕ => min (1 : ℝ) 1) atTop (nhds 0) := fun h =>
  adjacent_height_array_contradiction_of_endpoint_and_uniform_limits (fun _ _ => 1)
    (fun _ _ => 1) (fun _ => 0) (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) tendsto_const_nhds tendsto_const_nhds h

-- All-one primal tables with zero dual tables: the dual limits fail.
example : ¬ ((ℕ → ℕ) → Tendsto (fun _ : ℕ => max (0 : ℝ) 0) atTop (nhds 1)) := fun h =>
  adjacent_height_array_contradiction_of_primal_dual_limits (fun _ _ => 1) (fun _ _ => 1)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) tendsto_const_nhds tendsto_const_nhds
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by simp) h

-- `PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_max_limits` elaborates.
example := @PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_max_limits

end ArrayCrossingContradiction
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
