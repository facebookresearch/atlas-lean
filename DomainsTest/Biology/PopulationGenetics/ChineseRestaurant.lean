/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.ChineseRestaurant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! The Ewens block-size law and expected number of tables for two customers. -/

@[expose] public section

open Finset

namespace MathlibExtTest.Biology.PopulationGenetics.ChineseRestaurant

open MathlibExt.Biology.PopulationGenetics.ChineseRestaurant
open MathlibExt.Biology.PopulationGenetics.Ewens

/-- The block sizes of two customers: one allele carried by both genes with probability
`1 / (θ + 1)` (the Ewens sampling formula). -/
example (θ : ℝ) (hθ : 0 < θ) :
    (crp θ hθ 2).map blockSizes (Nat.Partition.indiscrete 2) =
      ENNReal.ofReal (1 / (θ + 1)) := by
  rw [crp_map_blockSizes hθ]
  congr 1
  have : θ * (θ + 1) ≠ 0 := by positivity
  simp [ewensProb, ascPochhammer_succ_eval]
  field_simp

/-- The expected number of tables for two customers is `1 + θ / (θ + 1)`. -/
example (θ : ℝ) (hθ : 0 < θ) :
    ∑ π : Finpartition (univ : Finset (Fin 2)), (crp θ hθ 2 π).toReal * #π.parts =
      1 + θ / (θ + 1) := by
  rw [sum_crp_toReal_mul_card_parts hθ]
  have : θ ≠ 0 := hθ.ne'
  simp [sum_range_succ, div_self this]

end MathlibExtTest.Biology.PopulationGenetics.ChineseRestaurant
