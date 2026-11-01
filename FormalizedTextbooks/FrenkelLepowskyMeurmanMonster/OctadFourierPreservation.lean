/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual octad cubic Fourier identity from its physical syndrome kernel. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadFourierContraction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadKernelIsotropy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.BinarySelfAnnihilator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LagrangianFourier

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The canonical triple sign space contains exactly 2^18 vectors. -/
theorem octadTripleSignSpace_card : Fintype.card OctadTripleSignSpace = 262144 := by
  simp [OctadTripleSignSpace, OctadSignSpace, ZMod.card]

/-- The physical isotropic kernel is self-annihilating once its 512 elements
have been identified with the compatible tetrad signs. -/
theorem octadTripleSyndromeKernel_self_annihilator_of_card (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (hc : Fintype.card (octadTripleSyndromeKernel o p u) = 512) :
    ∀ w : OctadTripleSignSpace,
      (∀ x : octadTripleSyndromeKernel o p u, octadTripleForm x.val w = 0) ↔
        w ∈ octadTripleSyndromeKernel o p u := by
  apply binary_self_annihilator_of_card octadTripleForm octadTripleForm_symmetric
    octadTripleForm_nondegenerate (octadTripleSyndromeKernel o p u)
    (octadTripleSyndromeKernel_isotropic o p u hfour hu)
  rw [hc, octadTripleSignSpace_card]
  norm_num

/-- The actual triality cubic follows from the counted physical syndrome kernel. -/
theorem griessForm_transformed_octad_cubic_four_of_card (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (hc : Fintype.card (octadTripleSyndromeKernel o p u) = 512) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityOctadBasis p f))) (sExtra (trialityOctadBasis u g)) =
      griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
        (trialityOctadBasis u g) := by
  have hsqrt : Real.sqrt (Fintype.card OctadTripleSignSpace : ℝ) = 512 := by
    rw [octadTripleSignSpace_card]
    norm_num [show (262144 : ℝ) = (512 : ℝ)^2 by norm_num]
  have hsize : (Fintype.card (octadTripleSyndromeKernel o p u) : ℝ) =
      Real.sqrt (Fintype.card OctadTripleSignSpace : ℝ) := by rw [hc, hsqrt]; norm_num
  have hf := lagrangianFourier_indicator octadTripleForm octadTripleForm_symmetric
    (octadTripleSyndromeKernel o p u)
    (octadTripleSyndromeKernel_self_annihilator_of_card o p u hfour hu hc) hsize
    (octadTripleCosetShift o p) (octadTripleSignLabel e f g)
    (octadTripleForm_alternating (octadTripleCosetShift o p))
  rw [hsqrt] at hf
  rw [griessForm_transformed_octad_coset_four o p u e f g hfour hu,
    griessForm_octad_cubic_four_coset o p u e f g hfour hu]
  calc
    _ = qSign (spinDot (sourceWordTheta (golayOctadLabel p))
        (golayLabelCoefficients (golayOctadLabel o))) *
        ((∑ x : OctadTripleSignSpace,
          (if octadTripleCosetShift o p + x ∈ octadTripleSyndromeKernel o p u then
            qSign (octadTripleForm (octadTripleCosetShift o p) x) else 0) *
            qSign (octadTripleForm x (octadTripleSignLabel e f g))) / 512) := by ring
    _ = _ := by rw [hf]

/-- The actual triality operator preserves every three-octad cubic on a
four-point intersection, with all physical support and cardinality checks proved. -/
theorem griessForm_transformed_octad_cubic_four (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityOctadBasis p f))) (sExtra (trialityOctadBasis u g)) =
      griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
        (trialityOctadBasis u g) := by
  apply griessForm_transformed_octad_cubic_four_of_card o p u e f g hfour hu
  simpa only [Nat.card_eq_fintype_card] using octadTripleSyndromeKernel_card o p u hfour hu

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
