/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source-coordinate formula for the actual octad cubic Griess pairing. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCrossPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SameOctadTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Pairing against a signed-octad basis vector extracts its actual octad coordinate. -/
theorem griessForm_octadBasis (x : GriessSpace) (u : Fin 759) (g : Fin 64) :
    griessForm x (trialityOctadBasis u g) = (trialityBlocksEquiv x).2.2.1 u g := by
  rw [trialityOctadBasis_eq_vector, griessForm_octadVector]
  simp [Pi.single_apply]

/-- The sparse raw short product gives its octad cubic coefficient directly. -/
theorem griessForm_shortBasisProduct_octad (r s : GriessShortIndex) (u : Fin 759) (g : Fin 64) :
    griessForm (griessConwayDecode (conwayRawProduct (conwayShortBasis r) (conwayShortBasis s)))
      (trialityOctadBasis u g) =
        if (griessShortQ r * griessShortQ s).base = (griessShortQ (Sum.inr (Sum.inl (u,g)))).base
        then qSign (toAdd (griessShortQ r * griessShortQ s).coeff) else 0 := by
  rw [griessForm_octadBasis, conwayRawProduct_shortBasis, griessConwayDecode_octad_block]

/-- Exact octad cubic in the actual preferred-Q model. -/
theorem griessForm_octad_cubic (o p u : Fin 759) (e f g : Fin 64) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
      (trialityOctadBasis u g) =
        if (griessShortQ (Sum.inr (Sum.inl (o,e))) *
          griessShortQ (Sum.inr (Sum.inl (p,f)))).base =
            (griessShortQ (Sum.inr (Sum.inl (u,g)))).base then
          qSign (toAdd (griessShortQ (Sum.inr (Sum.inl (o,e))) *
            griessShortQ (Sum.inr (Sum.inl (p,f)))).coeff) else 0 := by
  rw [griessProd_octadBasis, griessForm_shortBasisProduct_octad]

/-- When the three code labels add, the actual octad cubic is given by the
intrinsic Ω parity, intersection syndrome and cross-character sign. -/
theorem griessForm_octad_cubic_source (o p u : Fin 759) (e f g : Fin 64)
    (hcode : golayLabelCoefficients (golayOctadLabel u) =
      golayLabelCoefficients (golayOctadLabel o) + golayLabelCoefficients (golayOctadLabel p)) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
      (trialityOctadBasis u g) =
        if (griessOctadOmegaCoefficient e + griessOctadOmegaCoefficient f +
              griessOctadOmegaCoefficient g = 0) ∧
          golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
            integerParity (griessOctadNegativeInteger p f) +
            integerParity (griessOctadNegativeInteger u g)) =
              golaySyndrome (fun i => golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i *
                golayEncoder (golayLabelCoefficients (golayOctadLabel p)) i) then
          qSign (spinDot (sourceWordTheta (golayOctadLabel p))
            (golayLabelCoefficients (golayOctadLabel o)) +
            ∑ i, integerParity (griessOctadNegativeInteger p f) i *
              golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i) else 0 := by
  rw [griessForm_octad_cubic]
  simp only [griessOctadQ_triple_base_iff o p u e f g hcode,
    griessOctadQ_cross_product_coeff]

/-- Actual Fourier-transformed octad cubics are a finite triple contraction. -/
theorem griessForm_transformed_octad_cubic (o p u : Fin 759) (e f g : Fin 64) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityOctadBasis p f))) (sExtra (trialityOctadBasis u g)) =
        ∑ a, ∑ b, ∑ c,
          (trialityRealMatrix a e * trialityRealMatrix b f * trialityRealMatrix c g) *
            griessForm (griessProd (trialityOctadBasis o a) (trialityOctadBasis p b))
              (trialityOctadBasis u c) := by
  rw [griessProd_transformed_octad_sum, sExtra_octad_basis]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext a
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
