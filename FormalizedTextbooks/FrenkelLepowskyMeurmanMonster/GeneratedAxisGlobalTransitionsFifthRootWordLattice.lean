/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRootWordData
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

/-! The checked original normalization stages act on actual integral Leech vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual integral intermediate states of the fourteen explicit normalization words. -/
def generatedAxisGlobalFifthNormalizationLattice (k : Fin 14) (j : Fin 8) :
    leechIntegral := leechExplicitCoordinateMap
      (generatedAxisGlobalFifthNormalizationCoordinates k j)

/-- Each intermediate lattice state has exactly its checked physical coordinates. -/
theorem generatedAxisGlobalFifthNormalizationLattice_physical (k : Fin 14) (j : Fin 8) :
    (generatedAxisGlobalFifthNormalizationLattice k j).val =
      generatedAxisGlobalFifthNormalizationPhysical k j :=
  generatedAxisGlobalFifthNormalization_coordinates k j

/-- Actual Golay permutation of a literal original signed permutation word. -/
def generatedAxisGlobalFifthNormalizationPermutation (k : Fin 14) (j : Fin 7) :
    golayAutomorphismSubgroup := ((generatedAxisGlobalFifthNormalizationWords k j).map
      generatedFourthMonomialPermutationLetter).prod

/-- Genuine spatial action of one original normalization stage. -/
def generatedAxisGlobalFifthNormalizationSpatial (k : Fin 14) (j : Fin 7) :
    leechIsomSubgroup :=
  (if generatedAxisGlobalFifthNormalizationXi k j then co1XiIsometry else 1) *
    (golaySignIsometry
      (sourceGeneratedSignCode (generatedAxisGlobalFifthNormalizationSigns k j)) *
    golayPermutationIsometry (generatedAxisGlobalFifthNormalizationPermutation k j))

/-- Every literal stage carries its actual lattice input to its checked lattice output. -/
theorem generatedAxisGlobalFifthNormalizationSpatial_step (k : Fin 14) (j : Fin 7) :
    leechIntegralAction (generatedAxisGlobalFifthNormalizationSpatial k j)
      (generatedAxisGlobalFifthNormalizationLattice k j.castSucc) =
        generatedAxisGlobalFifthNormalizationLattice k j.succ := by
  let u := leechIntegralAction
    (golaySignIsometry
      (sourceGeneratedSignCode (generatedAxisGlobalFifthNormalizationSigns k j)) *
      golayPermutationIsometry (generatedAxisGlobalFifthNormalizationPermutation k j))
    (generatedAxisGlobalFifthNormalizationLattice k j.castSucc)
  have hu : u.val = golayIntegerSign
      (sourceGeneratedSignCode (generatedAxisGlobalFifthNormalizationSigns k j)).val
      (golayIntegerPermute (generatedAxisGlobalFifthNormalizationPermutation k j).val
        (generatedAxisGlobalFifthNormalizationPhysical k j.castSucc)) := by
    dsimp [u]
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation, generatedAxisGlobalFifthNormalizationLattice_physical]
  have hs : (if generatedAxisGlobalFifthNormalizationXi k j then
      co1XiNumerator *ᵥ u.val = 2 • generatedAxisGlobalFifthNormalizationPhysical k j.succ
    else u.val = generatedAxisGlobalFifthNormalizationPhysical k j.succ) := by
    simpa only [hu, generatedAxisGlobalFifthNormalizationPermutation] using
      generatedAxisGlobalFifthNormalization_steps k j
  rw [generatedAxisGlobalFifthNormalizationSpatial, map_mul, LinearEquiv.mul_apply]
  change leechIntegralAction
    (if generatedAxisGlobalFifthNormalizationXi k j then co1XiIsometry else 1) u = _
  cases hx : generatedAxisGlobalFifthNormalizationXi k j with
  | false =>
    simp only [hx, Bool.false_eq_true, ↓reduceIte, map_one] at hs ⊢
    apply Subtype.ext
    exact hs.trans (generatedAxisGlobalFifthNormalizationLattice_physical k j.succ).symm
  | true =>
    simp only [hx, ↓reduceIte] at hs ⊢
    apply Subtype.ext
    have hh := co1Xi_integral_double u
    rw [hs, ← generatedAxisGlobalFifthNormalizationLattice_physical] at hh
    funext i
    have hi := congrFun hh i
    change 2 * _ = 2 * _ at hi
    omega

/-- The checked chain starts at the actual root and ends at positive coordinate frame zero. -/
theorem generatedAxisGlobalFifthNormalizationLattice_endpoints (k : Fin 14) :
    generatedAxisGlobalFifthNormalizationLattice k 0 = generatedAxisGlobalFifthRootLattice k ∧
    generatedAxisGlobalFifthNormalizationLattice k 7 = leechCoordinateFrameLattice 0 := by
  constructor
  · apply Subtype.ext
    rw [generatedAxisGlobalFifthNormalizationLattice_physical,
      generatedAxisGlobalFifthRootLattice_physical]
    exact (generatedAxisGlobalFifthNormalization_endpoints k).1
  · apply Subtype.ext
    rw [generatedAxisGlobalFifthNormalizationLattice_physical]
    change generatedAxisGlobalFifthNormalizationPhysical k 7 = leechCoordinateFrameVector 0
    exact (generatedAxisGlobalFifthNormalization_endpoints k).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
