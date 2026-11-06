/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthQStabilizerExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! Exact orbit counting with the actual unresolved projected-stabilizer index retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full-axis projection image inside the genuine counted flag stabilizer. -/
def generatedFourthProjectedAxisStabilizer := generatedFourthLocalAxisProjection.range

/-- The actual H stabilizer has 128 elements for every element of its actual projection image. -/
theorem generatedFourth_local_stabilizer_card_range :
    Nat.card generatedFourthLocalAxisStabilizer =
      128 * Nat.card generatedFourthProjectedAxisStabilizer := by
  have h := generatedFourthLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedFourth_local_axis_projection_kernel_card] at h
  exact h.symm

/-- The genuine fourth-axis H orbit size retains precisely the actual missing projection index. -/
theorem generatedFourth_local_stabilizer_index_projection :
    generatedFourthLocalAxisStabilizer.index =
      1466587938816000 * generatedFourthProjectedAxisStabilizer.index := by
  have ha := generatedFourthLocalAxisStabilizer.card_mul_index
  rw [generatedFourth_local_stabilizer_card_range, local_h_card_exact] at ha
  rw [mul_assoc] at ha
  have hb := generatedFourthProjectedAxisStabilizer.card_mul_index
  rw [generatedAxisE8Co1ShortFlagStabilizer_card _ _ generatedFourth_flag_incident] at hb
  have hc : Nat.card generatedFourthProjectedAxisStabilizer *
      generatedFourthLocalAxisStabilizer.index = 1089936243174502563840000 := by
    omega
  have hr : 0 < Nat.card generatedFourthProjectedAxisStabilizer := by
    by_contra h
    have hz : Nat.card generatedFourthProjectedAxisStabilizer = 0 := by omega
    rw [hz, zero_mul] at hb
    contradiction
  apply Nat.eq_of_mul_eq_mul_left hr
  calc
    Nat.card generatedFourthProjectedAxisStabilizer *
        generatedFourthLocalAxisStabilizer.index = 1089936243174502563840000 := hc
    _ = 1466587938816000 * 743178240 := by decide
    _ = 1466587938816000 * (Nat.card generatedFourthProjectedAxisStabilizer *
        generatedFourthProjectedAxisStabilizer.index) := by rw [hb]
    _ = Nat.card generatedFourthProjectedAxisStabilizer *
        (1466587938816000 * generatedFourthProjectedAxisStabilizer.index) := by ring

/-- Exact cardinality of the genuine H orbit, without assuming any remaining projected lift. -/
theorem generatedFourth_local_axis_orbit_card_projection :
    Nat.card (MulAction.orbit H generatedFourthAxis) =
      1466587938816000 * generatedFourthProjectedAxisStabilizer.index := by
  have h := generatedFourth_local_stabilizer_index_projection
  rw [generatedFourthLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- The numerical fourth orbit count is equivalent to actual full-projection surjectivity. -/
theorem generatedFourth_local_axis_orbit_card_iff_surjective :
    Nat.card (MulAction.orbit H generatedFourthAxis) = 1466587938816000 ↔
      Function.Surjective generatedFourthLocalAxisProjection := by
  rw [generatedFourth_local_axis_orbit_card_projection]
  constructor
  · intro h
    have hi : generatedFourthProjectedAxisStabilizer.index = 1 := by omega
    exact MonoidHom.range_eq_top.mp (Subgroup.index_eq_one.mp hi)
  · intro h
    have hi : generatedFourthProjectedAxisStabilizer.index = 1 :=
      Subgroup.index_eq_one.mpr (MonoidHom.range_eq_top.mpr h)
    rw [hi, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
