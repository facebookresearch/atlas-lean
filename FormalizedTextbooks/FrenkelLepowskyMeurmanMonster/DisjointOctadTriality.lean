/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Triality preservation for distinct octads with at most two common coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Common physical support of two Golay octads. -/
def golayOctadIntersection (o p : Fin 759) : Finset (Fin 24) :=
  golayMaskSupport (golayEncodedMask (golayOctadLabel o).val) ∩
    golayMaskSupport (golayEncodedMask (golayOctadLabel p).val)

/-- Every nonzero product of two physical octad coordinates is ±4. -/
theorem griessOctad_pair_term_bounds (o p : Fin 759) (e f : Fin 64) (i : Fin 24) :
    -4 ≤ griessShortIntegral (Sum.inr (Sum.inl (o,e))) i *
      griessShortIntegral (Sum.inr (Sum.inl (p,f))) i ∧
    griessShortIntegral (Sum.inr (Sum.inl (o,e))) i *
      griessShortIntegral (Sum.inr (Sum.inl (p,f))) i ≤ 4 := by
  simp only [griessShortIntegral]
  split_ifs <;> norm_num

/-- Pairing of two octads is bounded by four times their common support size. -/
theorem griessOctad_pairing_intersection_bounds (o p : Fin 759) (e f : Fin 64) :
    -4 * (golayOctadIntersection o p).card ≤
      leechIntegralPairing (griessShortIntegral (Sum.inr (Sum.inl (o,e))))
        (griessShortIntegral (Sum.inr (Sum.inl (p,f)))) ∧
      leechIntegralPairing (griessShortIntegral (Sum.inr (Sum.inl (o,e))))
        (griessShortIntegral (Sum.inr (Sum.inl (p,f)))) ≤
          4 * (golayOctadIntersection o p).card := by
  let g : Fin 24 → ℤ := fun i => griessShortIntegral (Sum.inr (Sum.inl (o,e))) i *
    griessShortIntegral (Sum.inr (Sum.inl (p,f))) i
  have hs : (∑ i, g i) = ∑ i ∈ golayOctadIntersection o p, g i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp only [golayOctadIntersection, golayMaskSupport, Finset.mem_inter,
      Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
    dsimp only [g]
    by_cases ho : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
    · have hp := hi ho
      simp [griessShortIntegral, hp]
    · simp [griessShortIntegral, ho]
  change -4 * _ ≤ ∑ i, g i ∧ (∑ i, g i) ≤ 4 * _
  rw [hs]
  constructor
  · calc
      _ = ∑ i ∈ golayOctadIntersection o p, (-4 : ℤ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (griessOctad_pair_term_bounds o p e f i).1)
  · calc
      _ ≤ ∑ i ∈ golayOctadIntersection o p, (4 : ℤ) :=
        Finset.sum_le_sum (fun i _ => (griessOctad_pair_term_bounds o p e f i).2)
      _ = _ := by simp; ring

/-- Distinct octads with at most two common positions have zero actual product. -/
theorem griessProd_octadBasis_small_intersection (o p : Fin 759) (e f : Fin 64)
    (hne : o ≠ p) (hsmall : (golayOctadIntersection o p).card ≤ 2) :
    griessProd (trialityOctadBasis o e) (trialityOctadBasis p f) = 0 := by
  have hb := griessOctad_pairing_intersection_bounds o p e f
  have hc : ((golayOctadIntersection o p).card : ℤ) ≤ 2 := by exact_mod_cast hsmall
  have hp : leechIntegralPairing (griessShortIntegral (Sum.inr (Sum.inl (o,e))))
      (griessShortIntegral (Sum.inr (Sum.inl (p,f)))) ≠ 16 := by omega
  have hm : leechIntegralPairing (griessShortIntegral (Sum.inr (Sum.inl (o,e))))
      (griessShortIntegral (Sum.inr (Sum.inl (p,f)))) ≠ -16 := by omega
  have hr : (Sum.inr (Sum.inl (o,e)) : GriessShortIndex) ≠ Sum.inr (Sum.inl (p,f)) := by
    intro h
    simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    exact hne h.1
  rw [griessProd_octadBasis, conwayRawProduct_shortBasis_of_pairing _ _ hp hm]
  simp only [hr, ite_false]
  change griessConwayDecodeLinear (0 : ConwayRawSpace) = 0
  exact griessConwayDecodeLinear.map_zero

/-- Finite bilinear combinations vanish when all constituent products vanish. -/
theorem bilinear_sum_smul_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : GriessSpace →ₗ[ℝ] GriessSpace →ₗ[ℝ] GriessSpace)
    (x : ι → GriessSpace) (y : κ → GriessSpace) (a : ι → ℝ) (b : κ → ℝ)
    (h : ∀ i j, B (x i) (y j) = 0) :
    B (∑ i, a i • x i) (∑ j, b j • y j) = 0 := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    h, smul_zero, Finset.sum_const_zero]

/-- Actual octad triality preserves every pair of distinct octads whose
physical intersection has cardinality at most two. -/
theorem sExtra_octad_product_small_intersection (o p : Fin 759) (e f : Fin 64)
    (hne : o ≠ p) (hsmall : (golayOctadIntersection o p).card ≤ 2) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis p f) := by
  unfold TrialityProductPreserved
  rw [griessProd_octadBasis_small_intersection o p e f hne hsmall, map_zero,
    sExtra_octad_basis, sExtra_octad_basis]
  symm
  exact bilinear_sum_smul_zero griessProd (trialityOctadBasis o) (trialityOctadBasis p)
    (fun i => trialityRealMatrix i e) (fun j => trialityRealMatrix j f)
      (fun i j => griessProd_octadBasis_small_intersection o p i j hne hsmall)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
