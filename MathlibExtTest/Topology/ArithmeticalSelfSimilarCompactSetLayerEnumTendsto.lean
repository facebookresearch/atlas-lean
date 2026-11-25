/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSetLayerEnumTendsto

namespace MetaMathlibExt.isSelfSimilarCompactSet_layer_enum_tendsto

open Ordinal Filter Topology

variable {K : Set ℝ} {μ : ℕ} {ρ : ℝ} (hK : IsSelfSimilarCompactSet K μ ρ)
  {t : ℕ → Ordinal.{0} → ℝ} (ht : ∀ u, StrictAntiOn (t u) (Set.Iio (ω ^ ω)))
  (htK : ∀ u, t u '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)

-- At the first index, the block is the whole initial segment of naturals.
example (u : ℕ) : Tendsto (fun n : ℕ => t u n) atTop (𝓝 (t (u + 1) 0)) := by
  have h0 : (0 : Ordinal.{0}) < ω ^ ω := by
    calc (0 : Ordinal.{0}) < ω := omega0_pos
      _ ≤ ω ^ ω := by
        calc ω = ω ^ (1 : Ordinal) := (opow_one _).symm
          _ ≤ ω ^ ω := opow_le_opow_right omega0_pos one_lt_omega0.le
  simpa using isSelfSimilarCompactSet_layer_enum_tendsto hK ht htK u h0

-- The statement itself, applied at a general index.
example (u : ℕ) {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    Tendsto (fun n : ℕ => t u (ω * α + n)) atTop (𝓝 (t (u + 1) α)) :=
  isSelfSimilarCompactSet_layer_enum_tendsto hK ht htK u hα

-- At the first infinite index, the block starts at `ω ^ 2`.
example (u : ℕ) (hω : (ω : Ordinal.{0}) < ω ^ ω) :
    Tendsto (fun n : ℕ => t u ((ω : Ordinal.{0}) * ω + n)) atTop
      (𝓝 (t (u + 1) (ω : Ordinal.{0}))) :=
  isSelfSimilarCompactSet_layer_enum_tendsto hK ht htK u hω

end MetaMathlibExt.isSelfSimilarCompactSet_layer_enum_tendsto
