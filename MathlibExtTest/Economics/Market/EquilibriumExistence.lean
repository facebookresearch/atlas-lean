/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Market.EquilibriumExistence

@[expose] public section

/-! Tests for `MathlibExt.Economics.Market.EquilibriumExistence`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Market.EquilibriumExistence

open _root_.Economics.Market

/-- Test helper: excess demand of the linear example is strictly decreasing on `[0, 10]`. -/
theorem test_strictAntiOn_linear : StrictAntiOn
    (excessDemand (fun p : ℝ => 10 - p) (fun p => p)) (Set.Icc (0 : ℝ) 10) := by
  apply strictAntiOn_excessDemand
  · intro x _ y _ hxy
    show 10 - y ≤ 10 - x
    exact sub_le_sub_left hxy 10
  · intro x _ y _ hxy
    show (fun p : ℝ => p) x < (fun p : ℝ => p) y
    exact hxy

/-- Test: linear demand `D p = 10 - p` and supply `S p = p` have a unique equilibrium
price in `[0, 10]`. -/
theorem test_existsUnique_linear : ∃! p,
    p ∈ Set.Icc (0 : ℝ) 10 ∧ IsEquilibrium (fun p : ℝ => 10 - p) (fun p => p) p := by
  apply existsUnique_isEquilibrium (by norm_num)
  · exact (continuous_const.sub continuous_id).continuousOn
  · exact continuous_id.continuousOn
  · show 0 ≤ excessDemand _ _ 0
    simp only [excessDemand]
    norm_num
  · show excessDemand _ _ 10 ≤ 0
    simp only [excessDemand]
    norm_num
  · exact test_strictAntiOn_linear

/-- Test: price 5 clears the linear market. -/
theorem test_isEquilibrium_five :
    IsEquilibrium (fun p : ℝ => 10 - p) (fun p => p) 5 := by
  show (10 : ℝ) - 5 = 5
  norm_num

/-- Test: the unique equilibrium price of the linear market is 5. -/
theorem test_equilibrium_eq_five (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 10)
    (heq : IsEquilibrium (fun p : ℝ => 10 - p) (fun p => p) p) : p = 5 := by
  have h5mem : (5 : ℝ) ∈ Set.Icc (0 : ℝ) 10 := ⟨by norm_num, by norm_num⟩
  exact IsEquilibrium.eq_of_strictAntiOn test_strictAntiOn_linear hp h5mem heq
    test_isEquilibrium_five

end MathlibExtTest.Economics.Market.EquilibriumExistence
