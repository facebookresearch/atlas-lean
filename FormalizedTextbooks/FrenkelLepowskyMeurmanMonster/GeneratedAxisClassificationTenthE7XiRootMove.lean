/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7XiCorrectionFlag

/-! A genuine original matrix-flag fixer moves a genuine root to a distinct root line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Coordinate multiples of four with balanced total belong to the actual lattice. -/
theorem generatedTenth_e7_xi_integral_of_balanced_four (u : Fin 24 → ℤ)
    (h : ∀ i, (u i : ZMod 4) = 0)
    (hs : ((∑ i, u i : ℤ) : ZMod 8) = 0) : u ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro i
    change (u i : ZMod 4) = 0
    exact h i
  · change ((∑ i, u i : ℤ) : ZMod 8) = 0
    exact hs

/-- The original pair root is a genuine integral Leech lattice vector. -/
def generatedTenthE7XiIntegralRoot : leechIntegral :=
  ⟨generatedTenthE7XiRoot, generatedTenth_e7_xi_integral_of_balanced_four _
    (by decide +kernel) (by decide +kernel)⟩

/-- The distinct corrected pair root is a genuine integral Leech lattice vector. -/
def generatedTenthE7XiIntegralNextRoot : leechIntegral :=
  ⟨generatedTenthE7XiNextRoot, generatedTenth_e7_xi_integral_of_balanced_four _
    (by decide +kernel) (by decide +kernel)⟩

/-- Both original integral vectors have the actual norm-four square sum thirty-two. -/
theorem generatedTenth_e7_xi_integral_root_squares :
    leechSquareSum generatedTenthE7XiIntegralRoot.val = 32 ∧
      leechSquareSum generatedTenthE7XiIntegralNextRoot.val = 32 := by
  decide +kernel

private theorem standard_integral_image :
    leechIntegralAction generatedTenthE7XiCorrection generatedTenthE7XiIntegralRoot =
      generatedTenthE7XiIntegralNextRoot := by
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  exact generatedTenth_e7_xi_correction_root

/-- The source root transported into the original axis coordinates by genuine isometries. -/
def generatedTenthE7XiOriginalRoot : leechIntegral :=
  leechIntegralAction (generatedTenthE7Isometry⁻¹ *
    golayPermutationIsometry generatedTenthE8StandardPermutation) generatedTenthE7XiIntegralRoot

/-- Its target root transported into those same original coordinates. -/
def generatedTenthE7XiOriginalNextRoot : leechIntegral :=
  leechIntegralAction (generatedTenthE7Isometry⁻¹ *
    golayPermutationIsometry generatedTenthE8StandardPermutation)
      generatedTenthE7XiIntegralNextRoot

private theorem conjugate_image (p e : leechIsomSubgroup) (u v : leechIntegral)
    (h : leechIntegralAction e u = v) :
    leechIntegralAction (p * e * p⁻¹) (leechIntegralAction p u) = leechIntegralAction p v := by
  rw [map_mul, map_mul, map_inv]
  change leechIntegralAction p (leechIntegralAction e
    ((leechIntegralAction p).symm (leechIntegralAction p u))) = _
  rw [LinearEquiv.symm_apply_apply, h]

/-- The genuine full original matrix fixer attains the displayed new root exactly. -/
theorem generatedTenth_e7_xi_original_root_image :
    leechIntegralAction generatedTenthE7XiOriginal generatedTenthE7XiOriginalRoot =
      generatedTenthE7XiOriginalNextRoot := by
  have hg : generatedTenthE7XiOriginal =
      (generatedTenthE7Isometry⁻¹ *
        golayPermutationIsometry generatedTenthE8StandardPermutation) *
          generatedTenthE7XiCorrection *
            (generatedTenthE7Isometry⁻¹ *
              golayPermutationIsometry generatedTenthE8StandardPermutation)⁻¹ := by
    simp [generatedTenthE7XiOriginal, generatedTenthE7XiActual, mul_assoc]
  rw [hg]
  exact conjugate_image _ _ _ _ standard_integral_image

/-- Neither orientation of the source root equals the genuinely attained target. -/
theorem generatedTenth_e7_xi_original_root_line_moves :
    generatedTenthE7XiOriginalNextRoot ≠ generatedTenthE7XiOriginalRoot ∧
      generatedTenthE7XiOriginalNextRoot ≠ -generatedTenthE7XiOriginalRoot := by
  constructor
  · intro h
    have he := (leechIntegralAction (generatedTenthE7Isometry⁻¹ *
      golayPermutationIsometry generatedTenthE8StandardPermutation)).injective h
    exact generatedTenth_e7_xi_root_moves.1 (congrArg Subtype.val he)
  · intro h
    change leechIntegralAction _ generatedTenthE7XiIntegralNextRoot =
      -leechIntegralAction _ generatedTenthE7XiIntegralRoot at h
    rw [← map_neg] at h
    have he := (leechIntegralAction (generatedTenthE7Isometry⁻¹ *
      golayPermutationIsometry generatedTenthE8StandardPermutation)).injective h
    exact generatedTenth_e7_xi_root_moves.2 (congrArg Subtype.val he)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
