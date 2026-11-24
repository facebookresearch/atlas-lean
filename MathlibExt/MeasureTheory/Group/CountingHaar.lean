/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Topology.Instances.Discrete

/-!
# Counting Haar measure on arbitrary discrete groups

Counting measure is regular on a discrete Borel space: compact sets are
finite, every set is open, and finite subsets approximate the infinite
counting mass. Individual group translations preserve the counting measure,
so it is an actual regular Haar measure and has trivial modular character.
The group need not be countable, and no global sigma-finiteness or joint
measurability of multiplication is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory.Measure

noncomputable section

universe uX uG

/-- Counting measure on any discrete Borel space is regular, including uncountable spaces. -/
instance regular_count_of_discrete
    {X : Type uX} [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [BorelSpace X] :
    (count : Measure X).Regular where
  lt_top_of_isCompact K hK := count_apply_lt_top.mpr hK.finite_of_discrete
  outerRegular S _ r hr := ⟨S, Subset.rfl, isOpen_discrete S, hr⟩
  innerRegular U _ r hr := by
    by_cases hU : U.Finite
    · exact ⟨U, Subset.rfl, hU.isCompact, hr⟩
    · have hInfinite : U.Infinite := hU
      have hrTop : r < (⊤ : ℝ≥0∞) := hr.trans_le le_top
      have hNat : ∀ᶠ n : ℕ in atTop, r < (n : ℝ≥0∞) :=
        ENNReal.tendsto_nat_nhds_top.eventually (eventually_gt_nhds hrTop)
      obtain ⟨n, hn⟩ := hNat.exists
      obtain ⟨K, hKU, hCard⟩ := hInfinite.exists_subset_card_eq n
      refine ⟨(K : Set X), hKU, K.finite_toSet.isCompact, ?_⟩
      simpa only [count_apply_finset, hCard] using hn

variable {G : Type uG} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Each discrete left translation preserves counting measure without joint measurability. -/
instance isMulLeftInvariant_count_of_discrete : (count : Measure G).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    have hm : Measurable (fun x : G => g * x) :=
      (continuous_of_discreteTopology : Continuous (fun x : G => g * x)).measurable
    ext S hS
    rw [map_apply hm hS, count_apply hS, count_apply (hS.preimage hm),
      encard_preimage_of_bijective (Group.mulLeft_bijective g)]

/-- Each discrete right translation preserves counting measure without joint measurability. -/
instance isMulRightInvariant_count_of_discrete : (count : Measure G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have hm : Measurable (fun x : G => x * g) :=
      (continuous_of_discreteTopology : Continuous (fun x : G => x * g)).measurable
    ext S hS
    rw [map_apply hm hS, count_apply hS, count_apply (hS.preimage hm),
      encard_preimage_of_bijective (Group.mulRight_bijective g)]

/-- The actual counting measure is a Haar measure on any discrete Borel group. -/
instance isHaarMeasure_count_of_discrete : (count : Measure G).IsHaarMeasure where
  lt_top_of_isCompact _ hK := count_apply_lt_top.mpr hK.finite_of_discrete
  map_mul_left_eq_self := isMulLeftInvariant_count_of_discrete.map_mul_left_eq_self
  open_pos _ _ hU := count_ne_zero_iff.mpr hU

/-- Every discrete group has trivial modular character, as witnessed by actual counting Haar. -/
theorem modularCharacter_eq_one_of_discrete (g : G) : modularCharacter g = 1 := by
  change modularCharacterFun g = 1
  rw [modularCharacterFun_eq_haarScalarFactor (count : Measure G) g]
  simp only [map_mul_right_eq_self, haarScalarFactor_self]

end

end MeasureTheory.Measure
