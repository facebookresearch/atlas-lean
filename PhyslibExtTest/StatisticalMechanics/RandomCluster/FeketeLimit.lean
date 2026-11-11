/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.StatisticalMechanics.RandomCluster.FeketeLimit
import Mathlib.Tactic.NormNum

/-!
# Scalar Fekete normalization regression

All hypotheses are instantiated together by `u n = n`, `e n = 2n`, with limit `1/2`.
The zero denominator at index zero is harmless. This is not a graph-family witness.
-/

open Filter Topology
open _root_.StatMech.FK

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FeketeLimit

private lemma nat_subadditive : Subadditive (fun n : ℕ => (n : ℝ)) := by
  intro m n
  simp

private lemma ratio_tendsto_one :
    Tendsto (fun n : ℕ => (n : ℝ) / n) atTop (𝓝 1) := by
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)))
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [h]

example : Tendsto (fun n : ℕ => (n : ℝ) / (2 * n)) atTop (𝓝 (1 / 2)) := by
  have hbdd : BddBelow (Set.range fun n : ℕ => (n : ℝ) / n) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n)
  have hlim : nat_subadditive.lim = 1 :=
    tendsto_nhds_unique (nat_subadditive.tendsto_lim hbdd) ratio_tendsto_one
  have he : Tendsto (fun n : ℕ => (2 * (n : ℝ)) / n) atTop (𝓝 2) := by
    simpa only [mul_div_assoc, mul_one] using ratio_tendsto_one.const_mul 2
  have h := fkl_tendsto_div_of_subadditive (fun n => (n : ℝ)) nat_subadditive hbdd
    (fun n => 2 * (n : ℝ)) 2 (by norm_num) he
  simpa only [hlim] using h

-- Both removed graph wrappers must stay absent; scalar normalization stays available.
run_cmd do
  for name in [`StatMech.FK.fkl_tiltFreeEnergy_tendsto, `StatMech.FK.fkl_fekete_limit] do
    if (← Lean.getEnv).contains name then
      throwError "Retired graph wrapper is still present: {name}"

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FeketeLimit
