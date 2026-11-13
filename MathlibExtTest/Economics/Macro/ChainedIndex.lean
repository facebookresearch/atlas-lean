/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.ChainedIndex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open MathlibExt.Economics.Macro.ChainedIndex
/-!
# Tests for chained-index non-additivity

With unchanged period-2 quantities the second link is `1` and the chained
components (`50 + 100`) add up to the chained total `150`. The endpoint
simplification is applied to a component of the concrete basket, and zero
period-0 or period-1 quantities show why its nonzero hypotheses are needed.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.ChainedIndex

/-- One-link growth of the concrete basket: `3/4`. -/
theorem one_link_growth :
    laspeyresVolumeGrowth (![1, 1] : Fin 2 → ℚ) ![100, 100] ![50, 100] = 3 / 4 := by
  unfold laspeyresVolumeGrowth
  simp [Fin.sum_univ_two]
  norm_num

/-- One-link additivity: with unchanged period-2 quantities the second link is
`1`, and the chained components `50 + 100` add up to the chained total `150`. -/
theorem one_link_additive :
    ∑ j, chainedComponentValue (![1, 1] : Fin 2 → ℚ) ![100, 100] ![1, 4] ![50, 100]
        ![50, 100] j =
      chainedValueTwoLinks (![1, 1] : Fin 2 → ℚ) ![100, 100] ![1, 4] ![50, 100]
        ![50, 100] := by
  unfold chainedComponentValue chainedValueTwoLinks chainedRealValue chainedIndexTwoLinks
    laspeyresVolumeGrowth
  simp [Fin.sum_univ_two]
  norm_num

/-- Explicit values with unchanged period-2 quantities: total `150`,
components `50` and `100`. -/
theorem one_link_values :
    chainedValueTwoLinks (![1, 1] : Fin 2 → ℚ) ![100, 100] ![1, 4] ![50, 100]
        ![50, 100] = 150 ∧
      chainedComponentValue (![1, 1] : Fin 2 → ℚ) ![100, 100] ![1, 4] ![50, 100]
          ![50, 100] 0 = 50 ∧
        chainedComponentValue (![1, 1] : Fin 2 → ℚ) ![100, 100] ![1, 4] ![50, 100]
          ![50, 100] 1 = 100 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold chainedValueTwoLinks chainedRealValue chainedIndexTwoLinks laspeyresVolumeGrowth
    simp [Fin.sum_univ_two]
    norm_num
  · unfold chainedComponentValue chainedValueTwoLinks chainedRealValue chainedIndexTwoLinks
      laspeyresVolumeGrowth
    norm_num
  · unfold chainedComponentValue chainedValueTwoLinks chainedRealValue chainedIndexTwoLinks
      laspeyresVolumeGrowth
    norm_num

/-- Endpoint simplification on the two-link example: component `1` has chained
value `p₀ 1 * q₂ 1 = 200`. -/
theorem endpoint_example :
    chainedComponentValue (![1, 1] : Fin 2 → ℚ) ![100, 100] ![1, 4] ![50, 100]
      ![50, 200] 1 = 200 := by
  rw [chainedComponentValue_eq _ _ _ _ _ _ (by simp) (by simp) (by simp)]
  simp

/-- Degenerate period-0 quantity: with `q₀ = 0` the base value is `0`, so the
chained value is `0`, not `p₀ * q₂ = 50`; the endpoint equation is not claimed. -/
theorem degenerate_q0_zero_not_claimed :
    chainedComponentValue (fun _ : Unit => (1 : ℚ)) (fun _ => 0) (fun _ => 1) (fun _ => 1)
      (fun _ => 50) () ≠ 1 * 50 := by
  unfold chainedComponentValue chainedValueTwoLinks chainedRealValue chainedIndexTwoLinks
    laspeyresVolumeGrowth
  norm_num

/-- Degenerate period-1 quantity: with `p₀ = p₁ = q₀ = q₂ = 1` and `q₁ = 0`,
both links are `0` under totalized division, so the chained value is `0`, not
`p₀ * q₂ = 1`. -/
theorem degenerate_q1_zero_not_claimed :
    chainedComponentValue (fun _ : Unit => (1 : ℚ)) (fun _ => 1) (fun _ => 1) (fun _ => 0)
      (fun _ => 1) () = 0 := by
  unfold chainedComponentValue chainedValueTwoLinks chainedRealValue chainedIndexTwoLinks
    laspeyresVolumeGrowth
  norm_num
end MathlibExtTest.Economics.Macro.ChainedIndex
