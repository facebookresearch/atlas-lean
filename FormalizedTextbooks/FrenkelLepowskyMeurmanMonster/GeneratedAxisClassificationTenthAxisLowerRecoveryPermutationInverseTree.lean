/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryInverseCoordinates15

/-! All 720 exact original inverse roundtrips assembled from complete finite blocks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Complete roundtrip for every original entry, with no quadratic pair comparison. -/
theorem generatedTenth_axis_lower_recovery_permutation_inverse_roundtrip :
    ∀ r : Fin 720, generatedTenthAxisLowerRecoveryPermutationInverseLookup
      (generatedTenthAxisLowerRecoveryPermutationKey r) = some r := by
  intro r
  have hblocks : ∀ b : Fin 16, ∀ u : Fin 45,
      generatedTenthAxisLowerRecoveryPermutationInverseLookup
        (generatedTenthAxisLowerRecoveryPermutationKey ⟨45 * b.val + u.val, by omega⟩) =
          some (⟨45 * b.val + u.val, by omega⟩ : Fin 720) := by
    intro b
    fin_cases b
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_00
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_01
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_02
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_03
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_04
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_05
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_06
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_07
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_08
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_09
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_10
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_11
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_12
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_13
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_14
    · exact generatedTenth_axis_lower_recovery_inverse_coordinates_15
  let b : Fin 16 := ⟨r.val / 45, by omega⟩
  let u : Fin 45 := ⟨r.val % 45, Nat.mod_lt _ (by decide)⟩
  have hr : (⟨45 * b.val + u.val, by omega⟩ : Fin 720) = r := by
    apply Fin.ext
    dsimp only [b, u]
    omega
  have h := hblocks b u
  simpa only [hr] using h

/-- The exact complete tree certificate implies full-table injectivity. -/
theorem generatedTenth_axis_lower_recovery_traversal_injective_from_tree :
    Function.Injective generatedTenthAxisLowerRecoveryTraversalForward := by
  intro r s h
  have hk : generatedTenthAxisLowerRecoveryPermutationKey r =
      generatedTenthAxisLowerRecoveryPermutationKey s := by
    simp only [generatedTenthAxisLowerRecoveryPermutationKey, h]
  have hl := congrArg generatedTenthAxisLowerRecoveryPermutationInverseLookup hk
  simpa only [generatedTenth_axis_lower_recovery_permutation_inverse_roundtrip,
    Option.some.injEq] using hl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
