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
# Regular counting Haar measure on arbitrary discrete groups

Counting measure is regular on every discrete Borel space. For a discrete Borel group, each left
and right translation preserves it, so counting measure is Haar and the modular character is
one.

The space or group may be uncountable. No sigma-finiteness or joint measurability of
multiplication is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory.Measure

noncomputable section

universe uX uG

/-- **Regularity of counting measure on a discrete Borel space.** Let `X` be a discrete
topological space with its Borel measurable structure. Counting measure on `X` is regular,
even when `X` is uncountable. -/
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

/-- **Counting measure invariant under each left group translation.** Let `G` be any discrete
group with a topology and its Borel measurable structure; no countability assumption is
imposed. for every `g∈G`, the map `x ↦ gx` preserves counting measure. -/
instance isMulLeftInvariant_count_of_discrete : (count : Measure G).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    have hm : Measurable (fun x : G => g * x) :=
      (continuous_of_discreteTopology : Continuous (fun x : G => g * x)).measurable
    ext S hS
    rw [map_apply hm hS, count_apply hS, count_apply (hS.preimage hm),
      encard_preimage_of_bijective (Group.mulLeft_bijective g)]

/-- **Counting measure invariant under each right group translation.** Let `G` be any discrete
group with a topology and its Borel measurable structure; no countability assumption is
imposed. for every `g∈G`, the map `x ↦ xg` preserves counting measure. -/
instance isMulRightInvariant_count_of_discrete : (count : Measure G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have hm : Measurable (fun x : G => x * g) :=
      (continuous_of_discreteTopology : Continuous (fun x : G => x * g)).measurable
    ext S hS
    rw [map_apply hm hS, count_apply hS, count_apply (hS.preimage hm),
      encard_preimage_of_bijective (Group.mulRight_bijective g)]

/-- **Counting Haar measure of a discrete Borel group.** Let `G` be any discrete group with a
topology and its Borel measurable structure; no countability assumption is imposed.
counting measure is Haar: it is left invariant, finite on compact sets, and positive on
every nonempty open set. -/
instance isHaarMeasure_count_of_discrete : (count : Measure G).IsHaarMeasure where
  lt_top_of_isCompact _ hK := count_apply_lt_top.mpr hK.finite_of_discrete
  map_mul_left_eq_self := isMulLeftInvariant_count_of_discrete.map_mul_left_eq_self
  open_pos _ _ hU := count_ne_zero_iff.mpr hU

/-- **Trivial modular character of a discrete group.** Let `G` be any discrete group with a
topology and its Borel measurable structure; no countability assumption is imposed. for
every `g∈G`, `modularCharacter g=1`. -/
theorem modularCharacter_eq_one_of_discrete (g : G) : modularCharacter g = 1 := by
  change modularCharacterFun g = 1
  rw [modularCharacterFun_eq_haarScalarFactor (count : Measure G) g]
  simp only [map_mul_right_eq_self, haarScalarFactor_self]

end

end MeasureTheory.Measure
