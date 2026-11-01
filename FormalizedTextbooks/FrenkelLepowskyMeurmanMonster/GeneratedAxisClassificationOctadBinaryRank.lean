/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadBinaryData
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The certificate's eight binary columns are actual preferred-short bases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The supplied integer coordinates are the actual integral-basis coordinates. -/
theorem generatedOctadBasis_actual_coordinates (j : Fin 8) :
    leechExplicitCoordinates (griessShortLatticeVector (generatedOctadBasisLabel j)) =
      generatedOctadBasisIntegerCoordinates.col j := by
  apply leechBasisMatrix_injective
  change leechBasisMatrix *ᵥ
      leechExplicitCoordinates (griessShortLatticeVector (generatedOctadBasisLabel j)) = _
  rw [leechExplicitCoordinates_vector]
  exact (generatedOctadBasis_integer_certificate j).symm

/-- The binary certificate's columns are the genuine preferred-short bases. -/
theorem generatedOctadBasis_actual_base (j : Fin 8) :
    toAdd (griessShortQ (generatedOctadBasisLabel j)).base =
      generatedOctadBasisBinaryMatrix.col j := by
  change leechHyperbolicCoordinates
    (leechReduction (griessShortLatticeVector (generatedOctadBasisLabel j))) = _
  rw [leechHyperbolicCoordinates_explicit, generatedOctadBasis_actual_coordinates]
  ext i
  simp only [generatedOctadBasisBinaryMatrix, Matrix.col_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, integerParity, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Matrix.map_apply]
  rfl

/-- The actual binary map on these eight preferred-short columns is injective. -/
theorem generatedOctadBasis_binary_injective :
    Function.Injective generatedOctadBasisBinaryMatrix.mulVecLin := by
  intro a b h
  have hc := congrArg (fun x => generatedOctadBasisLeftInverse *ᵥ x) h
  change generatedOctadBasisLeftInverse *ᵥ (generatedOctadBasisBinaryMatrix *ᵥ a) =
    generatedOctadBasisLeftInverse *ᵥ (generatedOctadBasisBinaryMatrix *ᵥ b) at hc
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    generatedOctadBasis_left_inverse, Matrix.one_mulVec, Matrix.one_mulVec] at hc
  exact hc

/-- Eight independent actual preferred-short bases span a binary space of dimension eight. -/
theorem generatedOctadBasis_binary_rank :
    Module.finrank (ZMod 2) generatedOctadBasisBinaryMatrix.mulVecLin.range = 8 := by
  rw [LinearMap.finrank_range_of_inj generatedOctadBasis_binary_injective]
  simp

/-- The actual span of these checked columns has exactly 256 binary elements. -/
theorem generatedOctadBasis_binary_range_card :
    Nat.card generatedOctadBasisBinaryMatrix.mulVecLin.range = 256 := by
  rw [Nat.card_congr (LinearEquiv.ofInjective generatedOctadBasisBinaryMatrix.mulVecLin
    generatedOctadBasis_binary_injective).toEquiv.symm]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
