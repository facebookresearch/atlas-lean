/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.GlobalAssembly

/-!
# Tests for `Sheffield.GlobalAssembly`

Module under test: `Sheffield.GlobalAssembly` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `exists_adjacent_approximate_balanced_height_sequence` with explicit crossing tables: horizontal
  probability `0` at height `0` and `1` above, vertical the reverse, zero error, `K = 1`.
* `approximate_balanced_height_sequence_contradiction` concludes `False`; its `hlimits` hypothesis
  is the crossing dichotomy, so it is exercised by refuting `hlimits` for the all-zero tables
  (applied as a proof by contradiction: the dichotomy fails there).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace GlobalAssembly

open _root_.StatMech.FK.PeriodicPlanar Filter

/-- Horizontal crossing table: `0` at height `0`, `1` above. -/
noncomputable def hor (_ k : ℕ) : ℝ := if k = 0 then 0 else 1

/-- Vertical crossing table: `1` at height `0`, `0` above. -/
noncomputable def ver (_ k : ℕ) : ℝ := if k = 0 then 1 else 0

-- An adjacent pair of heights at which the preference switches.
example : ∃ k : ℕ → ℕ, ∀ n, k n < 1 + 1 ∧ hor n (k n) ≤ ver n (k n) + 0 ∧
    ver n (k n + 1) ≤ hor n (k n + 1) + 0 :=
  exists_adjacent_approximate_balanced_height_sequence hor ver (fun _ => 0) (fun _ => 1)
    (fun _ => le_rfl) (fun n => by norm_num [hor, ver]) (fun n => by norm_num [hor, ver])

-- For the all-zero tables the crossing dichotomy `hlimits` fails, as the theorem forces.
example : ¬ ∀ k : ℕ → ℕ, (∀ n, k n < 0 + 1) →
    Tendsto (fun _ : ℕ => max (0 : ℝ) 0) atTop (nhds 1) ∧
      Tendsto (fun _ : ℕ => min (0 : ℝ) 0) atTop (nhds 0) ∧
      Tendsto (fun _ : ℕ => min (0 : ℝ) 0) atTop (nhds 0) := fun h =>
  approximate_balanced_height_sequence_contradiction (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ => le_rfl) tendsto_const_nhds
    (fun _ => by norm_num) (fun _ => by norm_num) h

end GlobalAssembly
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
