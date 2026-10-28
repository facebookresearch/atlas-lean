/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneLiftWord

/-! The thirteen original simultaneous lifts have the stated actual coordinate permutation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Golay permutations corresponding to the original forward and inverse source letters. -/
def generatedSeventhXiPlanePermutationFactor (k : Fin 4) : golayAutomorphismSubgroup :=
  if h : k.val < 2 then omegaOrbitGolayPermutation ⟨k.val, h⟩
  else (omegaOrbitGolayPermutation ⟨k.val - 2, by omega⟩)⁻¹

/-- Physical permutation prefixes use exactly the simultaneous source lift application order. -/
def generatedSeventhXiPlanePermutationPrefix : ℕ → golayAutomorphismSubgroup
  | 0 => 1
  | r + 1 => generatedSeventhXiPlanePermutationFactor
      (generatedSeventhXiPlaneLetters ⟨r % 13, Nat.mod_lt _ (by decide)⟩) *
        generatedSeventhXiPlanePermutationPrefix r

/-- The actual code-preserving spatial permutation of the original source word. -/
def generatedSeventhXiPlanePermutation : golayAutomorphismSubgroup :=
  generatedSeventhXiPlanePermutationPrefix 13

/-- All forward coordinate images are certified on the genuine original permutations. -/
theorem generatedSeventhXiPlanePermutation_forward (i : Fin 24) :
    generatedSeventhXiPlanePermutation.val i = generatedSeventhXiPlaneForward i := by
  fin_cases i <;> decide +kernel

private def spatialMap : localFiberSubgroup →* leechIsomSubgroup :=
  (MonoidHom.snd SpinHolomorph leechIsomSubgroup).comp localFiberSubgroup.subtype

private theorem factor_spatial (k : Fin 4) :
    spatialMap (generatedSeventhXiPlaneFactor k) =
      golayPermutationHom (generatedSeventhXiPlanePermutationFactor k) := by
  by_cases hk : k.val < 2
  · simp only [generatedSeventhXiPlaneFactor, generatedSeventhXiPlanePermutationFactor,
      hk, dite_true]
    rfl
  · simp only [generatedSeventhXiPlaneFactor, generatedSeventhXiPlanePermutationFactor,
      hk, dite_false, map_inv]
    rfl

private theorem prefix_spatial (r : ℕ) :
    spatialMap (generatedSeventhXiPlanePrefix r) =
      golayPermutationHom (generatedSeventhXiPlanePermutationPrefix r) := by
  induction r with
  | zero => simp only [generatedSeventhXiPlanePrefix,
      generatedSeventhXiPlanePermutationPrefix, map_one]
  | succ r ih =>
      rw [generatedSeventhXiPlanePrefix, generatedSeventhXiPlanePermutationPrefix,
        map_mul, map_mul, factor_spatial, ih]

/-- The original simultaneous lift has this exact physical lattice isometry. -/
theorem generatedSeventhXiPlanePermutationFiber_spatial :
    generatedSeventhXiPlanePermutationFiber.val.2 =
      golayPermutationIsometry generatedSeventhXiPlanePermutation :=
  prefix_spatial 13

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
