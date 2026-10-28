/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthMateCoordinate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitPermutations

/-! An explicit genuine spatial transport of the original one-eighth frame.
The discovery word is checked against the original integral action, not assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original Golay permutation letters and their original inverses. -/
def generatedFeasibleEighthFramePermutationLetter (k : Fin 4) : golayAutomorphismSubgroup :=
  if h : k.val < 2 then omegaOrbitGolayPermutation ⟨k.val, h⟩
  else (omegaOrbitGolayPermutation ⟨k.val - 2, by omega⟩)⁻¹

/-- Three discovered finite words in the original Golay generators. -/
def generatedFeasibleEighthFramePermutationWords : Fin 3 → List (Fin 4) :=
![
  [0, 0, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 0, 1, 2, 2],
  [0, 1, 2, 2, 1, 0, 1, 2, 2, 2, 1, 2, 1, 0, 0, 1, 2, 2, 2],
  [1, 0, 1, 2]
]

/-- Genuine code automorphisms in the discovered order of application. -/
def generatedFeasibleEighthFramePermutation (k : Fin 3) : golayAutomorphismSubgroup :=
  ((generatedFeasibleEighthFramePermutationWords k).map
    generatedFeasibleEighthFramePermutationLetter).reverse.prod

/-- Independently recorded complete forward arrays. -/
def generatedFeasibleEighthFramePermutationForward : Fin 3 → Fin 24 → Fin 24 :=
![
  ![0, 1, 19, 17, 11, 10, 23, 20, 9, 8, 22, 21, 2, 3, 16, 18, 7, 13, 15, 4, 6, 12, 5, 14],
  ![19, 0, 1, 2, 23, 8, 7, 12, 11, 21, 13, 5, 18, 3, 16, 17, 6, 22, 10, 15, 14, 20, 4, 9],
  ![0, 16, 20, 1, 12, 22, 19, 13, 3, 10, 6, 14, 2, 7, 11, 15, 8, 23, 18, 9, 4, 21, 17, 5]
]

/-- Independently recorded complete inverse arrays. -/
def generatedFeasibleEighthFramePermutationInverse : Fin 3 → Fin 24 → Fin 24 :=
![
  ![0, 1, 12, 13, 19, 22, 20, 16, 9, 8, 5, 4, 21, 17, 23, 18, 14, 3, 15, 2, 7, 11, 10, 6],
  ![1, 2, 3, 13, 22, 11, 16, 6, 5, 23, 18, 8, 7, 10, 20, 19, 14, 15, 12, 0, 21, 9, 17, 4],
  ![0, 3, 12, 8, 20, 23, 10, 13, 16, 19, 9, 14, 4, 7, 11, 15, 1, 22, 18, 6, 2, 21, 5, 17]
]

/-- The complete arrays are exactly the actual generator words, in both directions. -/
theorem generatedFeasibleEighthFramePermutation_arrays : ∀ k : Fin 3, ∀ i : Fin 24,
    (generatedFeasibleEighthFramePermutation k).val i =
      generatedFeasibleEighthFramePermutationForward k i ∧
    (generatedFeasibleEighthFramePermutation k).val.symm i =
      generatedFeasibleEighthFramePermutationInverse k i := by
  decide +kernel

/-- Actual Golay signs selected by their original code labels. -/
def generatedFeasibleEighthFrameSign (n : Fin 4096) : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients n), ⟨_, rfl⟩⟩

/-- The exact finite coordinate action of the spatial word. -/
def generatedFeasibleEighthFrameIntegerPermutation (k : Fin 3) (v : Fin 24 → ℤ) :=
  fun i => v (generatedFeasibleEighthFramePermutationInverse k i)

/-- The integral coordinate sign action of the original Golay word with label `n`. -/
def generatedFeasibleEighthFrameIntegerSign (n : Fin 4096) (v : Fin 24 → ℤ) :=
  golayIntegerSign (golayEncoder (golayLabelCoefficients n)) v

/-- The integral Xi numerator divided by two, used in the explicit frame word. -/
def generatedFeasibleEighthFrameIntegerXi (v : Fin 24 → ℤ) :=
  fun i => (co1XiNumerator *ᵥ v) i / 2

/-- The original integral Xi action equals its exact even numerator divided by two. -/
theorem generatedFeasibleEighthFrameIntegerXi_actual (u : leechIntegral) :
    (leechIntegralAction co1XiIsometry u).val =
      generatedFeasibleEighthFrameIntegerXi u.val := by
  funext i
  have h := congrFun (co1Xi_integral_double u) i
  change 2 * (leechIntegralAction co1XiIsometry u).val i = (co1XiNumerator *ᵥ u.val) i at h
  dsimp only [generatedFeasibleEighthFrameIntegerXi]
  omega

/-- The original permutation action equals the certified inverse array. -/
theorem generatedFeasibleEighthFrameIntegerPermutation_actual (k : Fin 3) (u : leechIntegral) :
    (leechIntegralAction (golayPermutationIsometry
      (generatedFeasibleEighthFramePermutation k)) u).val =
        generatedFeasibleEighthFrameIntegerPermutation k u.val := by
  rw [leechIntegralAction_golayPermutation]
  funext i
  change u.val ((generatedFeasibleEighthFramePermutation k).val.symm i) = _
  rw [(generatedFeasibleEighthFramePermutation_arrays k i).2]
  rfl

/-- Two genuine Xi steps, with genuine Golay permutations and signs, followed by root normalization.
-/
def generatedFeasibleEighthExplicitSpatialWord : leechIsomSubgroup :=
  golayPermutationIsometry (generatedFeasibleEighthFramePermutation 2) *
    golaySignIsometry (generatedFeasibleEighthFrameSign 2048) *
    co1XiIsometry * golaySignIsometry (generatedFeasibleEighthFrameSign 2816) *
    golayPermutationIsometry (generatedFeasibleEighthFramePermutation 1) *
    co1XiIsometry * golaySignIsometry (generatedFeasibleEighthFrameSign 1280) *
    golayPermutationIsometry (generatedFeasibleEighthFramePermutation 0)

/-- Complete finite coordinate formula, retaining integral division only at genuine Xi steps. -/
def generatedFeasibleEighthExplicitIntegerAction (v : Fin 24 → ℤ) :=
  generatedFeasibleEighthFrameIntegerPermutation 2
    (generatedFeasibleEighthFrameIntegerSign 2048
      (generatedFeasibleEighthFrameIntegerXi
        (generatedFeasibleEighthFrameIntegerSign 2816
          (generatedFeasibleEighthFrameIntegerPermutation 1
            (generatedFeasibleEighthFrameIntegerXi
              (generatedFeasibleEighthFrameIntegerSign 1280
                (generatedFeasibleEighthFrameIntegerPermutation 0 v)))))))

/-- The entire actual integral action has the exact checked finite coordinate formula. -/
theorem generatedFeasibleEighthExplicitIntegerAction_actual (u : leechIntegral) :
    (leechIntegralAction generatedFeasibleEighthExplicitSpatialWord u).val =
      generatedFeasibleEighthExplicitIntegerAction u.val := by
  simp only [generatedFeasibleEighthExplicitSpatialWord, map_mul, LinearEquiv.mul_apply]
  simp only [generatedFeasibleEighthFrameIntegerPermutation_actual,
    leechIntegralAction_golaySign, generatedFeasibleEighthFrameIntegerXi_actual]
  rfl

/-- All original frame coordinates are transported to the positive coordinate frame. -/
theorem generatedFeasibleEighthExplicitSpatialWord_frame :
    leechIntegralAction generatedFeasibleEighthExplicitSpatialWord
      generatedFeasibleContainingNewFrame = leechCoordinateFrameLattice 0 := by
  apply Subtype.ext
  rw [generatedFeasibleEighthExplicitIntegerAction_actual]
  change generatedFeasibleEighthExplicitIntegerAction
    generatedFeasibleContainingNewFrameCoordinates = Pi.single 0 8
  decide +kernel

/-- All original preferred first-root coordinates are fixed positively. -/
theorem generatedFeasibleEighthExplicitSpatialWord_first :
    leechIntegralAction generatedFeasibleEighthExplicitSpatialWord
      (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
        griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  apply Subtype.ext
  rw [generatedFeasibleEighthExplicitIntegerAction_actual]
  simp only [griessShortLatticeVector, griessShortIntegral,
    generatedFeasiblePhysicalRootPair_coordinates]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
