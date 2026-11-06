/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The source three-bases spin operator as an actual orthogonal normalizer. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinOrthogonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinOrderThree

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An involution with a verified conjugation formula normalizes the actual image. -/
theorem xiSpinImage_normalizer_of_involution (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hsq : e * e = 1) (f : Q → Q)
    (hf : ∀ q, e * spinRepresentation q * e = spinRepresentation (f q)) :
    e ∈ Subgroup.normalizer (spinImage : Set (SpinSpace ≃ₗ[ℝ] SpinSpace)) := by
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hsq
  apply Subgroup.mem_normalizer_iff.mpr
  intro h
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨f q, by rw [hei]; exact (hf q).symm⟩
  · rintro ⟨q, hq⟩
    refine ⟨f q, ?_⟩
    rw [← hf q, hq, hei]
    calc
      _ = (e * e) * h * (e * e) := by simp only [mul_assoc]
      _ = h := by rw [hsq, one_mul, mul_one]

@[simp] theorem xiSpinGammaEquiv_square : xiSpinGammaEquiv * xiSpinGammaEquiv = 1 := by
  apply LinearEquiv.ext
  intro f
  exact congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f) xiSpinGamma_square

@[simp] theorem xiSpinGEquiv_square : xiSpinGEquiv * xiSpinGEquiv = 1 := by
  apply LinearEquiv.ext
  intro f
  exact congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f) xiSpinG_square

/-- The first 64-term Gaussian is a genuine orthogonal normalizer of Q. -/
noncomputable def xiSpinGammaHolomorph : SpinHolomorph :=
  ⟨xiSpinGammaEquiv,
    xiSpinImage_normalizer_of_involution _ xiSpinGammaEquiv_square xiSpinGammaImage (fun q => by
      apply LinearEquiv.ext
      intro f
      exact congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f) (xiSpinGamma_conjugation q)),
    xiSpinGamma_pairing⟩

/-- The second 64-term Gaussian is a genuine orthogonal normalizer of Q. -/
noncomputable def xiSpinGHolomorph : SpinHolomorph :=
  ⟨xiSpinGEquiv,
    xiSpinImage_normalizer_of_involution _ xiSpinGEquiv_square xiSpinGImage (fun q => by
      apply LinearEquiv.ext
      intro f
      exact congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f) (xiSpinG_conjugation q)),
    xiSpinG_pairing⟩

/-- The actual source spin factor ξ4096 in column convention. -/
noncomputable def xiSpinHolomorph : SpinHolomorph := xiSpinGHolomorph * xiSpinGammaHolomorph

/-- Forgetting the normalizer and invertibility proofs gives the actual spin operator. -/
noncomputable def xiSpinEndHom : SpinHolomorph →* (SpinSpace →ₗ[ℝ] SpinSpace) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp spinHolomorphSubgroup.subtype

theorem xiSpinEndHom_injective : Function.Injective xiSpinEndHom := by
  intro a b h
  apply Subtype.ext
  exact LinearEquiv.toLinearMap_injective h

@[simp] theorem xiSpinEndHom_gamma : xiSpinEndHom xiSpinGammaHolomorph = xiSpinGamma := rfl
@[simp] theorem xiSpinEndHom_g : xiSpinEndHom xiSpinGHolomorph = xiSpinG := rfl

/-- The normalizer's concrete endomorphism is precisely the published product of sums. -/
@[simp] theorem xiSpinEndHom_xi : xiSpinEndHom xiSpinHolomorph = xiSpinOperator := by
  rw [xiSpinHolomorph, map_mul, xiSpinEndHom_g, xiSpinEndHom_gamma]
  rfl

/-- The actual orthogonal normalizer constructed from the source sums satisfies ξ³=1. -/
@[simp] theorem xiSpinHolomorph_cube : xiSpinHolomorph ^ 3 = 1 := by
  apply xiSpinEndHom_injective
  rw [map_pow, map_one, xiSpinEndHom_xi, xiSpinOperator_cube]

/-- The actual first Gaussian normalizer has the proved coordinate conjugation. -/
theorem xiSpinGammaHolomorph_conjugation (q : Q) :
    spinConjugation xiSpinGammaHolomorph q = xiSpinGammaImage q := by
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  have hi : xiSpinGammaEquiv⁻¹ = xiSpinGammaEquiv :=
    inv_eq_of_mul_eq_one_right xiSpinGammaEquiv_square
  change xiSpinGammaEquiv * spinRepresentation q * xiSpinGammaEquiv⁻¹ =
    spinRepresentation (xiSpinGammaImage q)
  rw [hi]
  apply LinearEquiv.toLinearMap_injective
  simp only [LinearEquiv.coe_toLinearMap_mul, xiSpinGammaEquiv_toLinearMap,
    xiSpinRepresentation_toLinearMap]
  exact xiSpinGamma_conjugation q

/-- The actual second Gaussian normalizer has the proved coordinate conjugation. -/
theorem xiSpinGHolomorph_conjugation (q : Q) :
    spinConjugation xiSpinGHolomorph q = xiSpinGImage q := by
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  have hi : xiSpinGEquiv⁻¹ = xiSpinGEquiv := inv_eq_of_mul_eq_one_right xiSpinGEquiv_square
  change xiSpinGEquiv * spinRepresentation q * xiSpinGEquiv⁻¹ = spinRepresentation (xiSpinGImage q)
  rw [hi]
  apply LinearEquiv.toLinearMap_injective
  simp only [LinearEquiv.coe_toLinearMap_mul, xiSpinGEquiv_toLinearMap,
    xiSpinRepresentation_toLinearMap]
  exact xiSpinG_conjugation q

/-- Its conjugation automorphism is determined by the proved coordinate formulas. -/
theorem xiSpinHolomorph_conjugation (q : Q) :
    spinConjugation xiSpinHolomorph q = xiSpinGImage (xiSpinGammaImage q) := by
  rw [xiSpinHolomorph, map_mul]
  change spinConjugation xiSpinGHolomorph (spinConjugation xiSpinGammaHolomorph q) = _
  rw [xiSpinGammaHolomorph_conjugation, xiSpinGHolomorph_conjugation]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
