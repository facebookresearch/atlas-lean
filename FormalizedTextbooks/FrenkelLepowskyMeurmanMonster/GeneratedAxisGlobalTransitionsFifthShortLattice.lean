/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortWordData
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

/-! The checked original normalization stages act on actual integral Leech vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual integral intermediate states of the fourteen explicit normalization words. -/
def generatedAxisGlobalFifthShortNormalizationLattice (k : Fin 14) (j : Fin 8) :
    leechIntegral := leechExplicitCoordinateMap
      (generatedAxisGlobalFifthShortNormalizationCoordinates k j)

/-- Each intermediate lattice state has exactly its checked physical coordinates. -/
theorem generatedAxisGlobalFifthShortNormalizationLattice_physical (k : Fin 14) (j : Fin 8) :
    (generatedAxisGlobalFifthShortNormalizationLattice k j).val =
      generatedAxisGlobalFifthShortNormalizationPhysical k j :=
  generatedAxisGlobalFifthShortNormalization_coordinates k j

/-- Actual Golay permutation of a literal original signed permutation word. -/
def generatedAxisGlobalFifthShortNormalizationPermutation (k : Fin 14) (j : Fin 7) :
    golayAutomorphismSubgroup := ((generatedAxisGlobalFifthShortNormalizationWords k j).map
      generatedFourthMonomialPermutationLetter).prod

/-- Genuine spatial action of one original normalization stage. -/
def generatedAxisGlobalFifthShortNormalizationSpatial (k : Fin 14) (j : Fin 7) :
    leechIsomSubgroup :=
  (if generatedAxisGlobalFifthShortNormalizationXi k j then co1XiIsometry else 1) *
    (golaySignIsometry
      (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns k j)) *
    golayPermutationIsometry (generatedAxisGlobalFifthShortNormalizationPermutation k j))

/-- Every literal stage carries its actual lattice input to its checked lattice output. -/
theorem generatedAxisGlobalFifthShortNormalizationSpatial_step (k : Fin 14) (j : Fin 7) :
    leechIntegralAction (generatedAxisGlobalFifthShortNormalizationSpatial k j)
      (generatedAxisGlobalFifthShortNormalizationLattice k j.castSucc) =
        generatedAxisGlobalFifthShortNormalizationLattice k j.succ := by
  let u := leechIntegralAction
    (golaySignIsometry
      (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns k j)) *
      golayPermutationIsometry (generatedAxisGlobalFifthShortNormalizationPermutation k j))
    (generatedAxisGlobalFifthShortNormalizationLattice k j.castSucc)
  have hu : u.val = golayIntegerSign
      (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns k j)).val
      (golayIntegerPermute (generatedAxisGlobalFifthShortNormalizationPermutation k j).val
        (generatedAxisGlobalFifthShortNormalizationPhysical k j.castSucc)) := by
    dsimp [u]
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation,
      generatedAxisGlobalFifthShortNormalizationLattice_physical]
  have hs : (if generatedAxisGlobalFifthShortNormalizationXi k j then
      co1XiNumerator *ᵥ u.val = 2 • generatedAxisGlobalFifthShortNormalizationPhysical k j.succ
    else u.val =
      generatedAxisGlobalFifthShortNormalizationPhysical k j.succ) := by
    simpa only [hu, generatedAxisGlobalFifthShortNormalizationPermutation] using
      generatedAxisGlobalFifthShortNormalization_steps k j
  rw [generatedAxisGlobalFifthShortNormalizationSpatial, map_mul, LinearEquiv.mul_apply]
  change leechIntegralAction
    (if generatedAxisGlobalFifthShortNormalizationXi k j then co1XiIsometry else 1) u = _
  cases hx : generatedAxisGlobalFifthShortNormalizationXi k j with
  | false =>
    simp only [hx, Bool.false_eq_true, ↓reduceIte, map_one] at hs ⊢
    apply Subtype.ext
    exact hs.trans (generatedAxisGlobalFifthShortNormalizationLattice_physical k j.succ).symm
  | true =>
    simp only [hx, ↓reduceIte] at hs ⊢
    apply Subtype.ext
    have hh := co1Xi_integral_double u
    rw [hs, ← generatedAxisGlobalFifthShortNormalizationLattice_physical] at hh
    funext i
    have hi := congrFun hh i
    change 2 * _ = 2 * _ at hi
    omega

/-- The alternative first vector has precisely the previously proved genuine root class. -/
theorem generatedAxisGlobalFifthShortNormalizationLattice_binary (k : Fin 14) :
    leechHyperbolicCoordinates
      (leechReduction (generatedAxisGlobalFifthShortNormalizationLattice k 0)) =
        generatedAxisGlobalFifthRootBinary k := by
  rw [leechHyperbolicCoordinates_explicit]
  have hc : leechExplicitCoordinates
      (generatedAxisGlobalFifthShortNormalizationLattice k 0) =
      generatedAxisGlobalFifthShortNormalizationCoordinates k 0 :=
    leechExplicitCoordinates.apply_symm_apply _
  rw [hc]
  exact (generatedAxisGlobalFifthShortNormalization_endpoints k).1

/-- The checked shorter chain ends at the actual positive coordinate frame zero. -/
theorem generatedAxisGlobalFifthShortNormalizationLattice_frame (k : Fin 14) :
    generatedAxisGlobalFifthShortNormalizationLattice k 7 = leechCoordinateFrameLattice 0 := by
  apply Subtype.ext
  rw [generatedAxisGlobalFifthShortNormalizationLattice_physical]
  change generatedAxisGlobalFifthShortNormalizationPhysical k 7 = leechCoordinateFrameVector 0
  exact (generatedAxisGlobalFifthShortNormalization_endpoints k).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
