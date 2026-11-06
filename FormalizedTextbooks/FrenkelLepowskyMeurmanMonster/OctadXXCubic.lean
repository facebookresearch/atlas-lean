/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXXPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddBaseSelector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddBaseCases

/-! Actual OXX cubic coefficients in terms of preferred-Q base selection.
The physical Q selectors are proved separately. Here they feed the exact
Conway short product coefficient and the proved phase comparison with
the actual Y spin constant, yielding sparse normalized-label formulas. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- An absent preferred-Q base match gives an actual zero OXX cubic coefficient. -/
theorem octadXXCubic_zero_of_no_match (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base ≠
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, i))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, j))) = 0 := by
  rw [trialityOctadXYZ_cubic_XX_coefficient, ite_eq_right hb]

/-- A selected outside diagonal OXX coefficient is the actual Y spin constant. -/
theorem octadXXCubic_outside_of_match (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, i)))).base)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d)
    (hs : golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k) +
      Pi.single i 1 + Pi.single i 1) = 0)
    (hi : i ∉ golayOctadSupport o) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, i))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, i))) = octadYSpinConstant o d f i i := by
  rw [trialityOctadXYZ_cubic_XX_coefficient, ite_eq_left hb]
  exact griessOctadOdd_phase_eq_YConstant o e d f i hb hd hs hi

/-- A selected OXX coefficient inside the octad is minus the actual Y spin constant. -/
theorem octadXXCubic_inside_of_match (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d)
    (hs : golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k) +
      Pi.single i 1 + Pi.single j 1) = 0)
    (hi : i ∈ golayOctadSupport o) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, i))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, j))) = -octadYSpinConstant o d f i j := by
  rw [trialityOctadXYZ_cubic_XX_coefficient, ite_eq_left hb]
  exact griessOctadOdd_phase_eq_neg_YConstant o e d f i j hb hd hs hi

/-- The outside diagonal formula once its actual normalized-label selector is supplied. -/
theorem octadXXCubic_outside_of_selector (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d)
    (hi : i ∉ golayOctadSupport o)
    (hsel : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, i)))).base ↔ e = octadTensorCharacterLabel o f)
    (hs : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, i)))).base →
      golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
        (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k) +
        Pi.single i 1 + Pi.single i 1) = 0) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, i))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, i))) =
      octadYSpinConstant o d f i i * (if e = octadTensorCharacterLabel o f then 1 else 0) := by
  by_cases hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, i)))).base
  · rw [octadXXCubic_outside_of_match o e d f i hb hd (hs hb) hi,
      ite_eq_left (hsel.mp hb), mul_one]
  · rw [octadXXCubic_zero_of_no_match o e d f i i hb,
      ite_eq_right (hsel.not.mp hb), mul_zero]

/-- The inside distinct-pair formula once its actual normalized flip selector is supplied. -/
theorem octadXXCubic_pair_of_selector (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (a b : Fin 8)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d)
    (hsel : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, golayOctadCoordinate o a)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, golayOctadCoordinate o b)))).base ↔
      e = trialityOctadPairFlip a b (octadTensorCharacterLabel o f))
    (hs : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, golayOctadCoordinate o a)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, golayOctadCoordinate o b)))).base →
      golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
        (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k) +
        Pi.single (golayOctadCoordinate o a) 1 + Pi.single (golayOctadCoordinate o b) 1) = 0) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, golayOctadCoordinate o a))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, golayOctadCoordinate o b))) =
      -octadYSpinConstant o d f (golayOctadCoordinate o a) (golayOctadCoordinate o b) *
        (if e = trialityOctadPairFlip a b (octadTensorCharacterLabel o f) then 1 else 0) := by
  have hi : golayOctadCoordinate o a ∈ golayOctadSupport o := by
    simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] using golayOctadCoordinate_mem o a
  by_cases hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, golayOctadCoordinate o a)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, golayOctadCoordinate o b)))).base
  · rw [octadXXCubic_inside_of_match o e d f _ _ hb hd (hs hb) hi,
      ite_eq_left (hsel.mp hb), mul_one]
  · rw [octadXXCubic_zero_of_no_match o e d f _ _ hb,
      ite_eq_right (hsel.not.mp hb), mul_zero]

lemma octadXXCubic_match_syndrome (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base) :
    golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k) +
      Pi.single i 1 + Pi.single j 1) = 0 := by
  exact ((griessOctadOdd_base_iff_coordinates o e d f i j).mp hb).2.1

/-- Failure of the actual dictionary selector forces the actual OXX coefficient to vanish. -/
theorem octadXXCubic_zero_of_code_selector (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) ≠ d) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, i))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, j))) = 0 := by
  apply octadXXCubic_zero_of_no_match
  intro hb
  exact hd (griessOctadOdd_base_code_selector o e d f i j hb)

lemma octadXXCubic_YConstant_zero_of_code_selector (o : Fin 759)
    (d f : Fin 2048) (i j : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) ≠ d) :
    octadYSpinConstant o d f i j = 0 := by
  simp only [octadYSpinConstant, octadSpinSelector, hd, ite_false, mul_zero]

/-- The actual outside diagonal OXX coefficient selects the unshifted character label. -/
theorem octadXXCubic_outside_diagonal (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i : Fin 24) (hi : i ∉ golayOctadSupport o) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, i))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, i))) =
      octadYSpinConstant o d f i i * (if e = octadTensorCharacterLabel o f then 1 else 0) := by
  by_cases hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d
  · apply octadXXCubic_outside_of_selector o e d f i hd hi
    · simpa only [hi, not_false_eq_true, true_and] using griessOctadOdd_base_same o e d f i hd
    · exact octadXXCubic_match_syndrome o e d f i i
  · rw [octadXXCubic_zero_of_code_selector o e d f i i hd,
      octadXXCubic_YConstant_zero_of_code_selector o d f i i hd, zero_mul]

/-- Two distinct positions inside the octad select the actual pair-shifted character label. -/
theorem octadXXCubic_inside_pair (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (a b : Fin 8) (hab : a ≠ b) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, golayOctadCoordinate o a))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, golayOctadCoordinate o b))) =
      -octadYSpinConstant o d f (golayOctadCoordinate o a) (golayOctadCoordinate o b) *
        (if e = trialityXor (octadTensorCharacterLabel o f) (trialityOctadPairShift a b)
          then 1 else 0) := by
  by_cases hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d
  · have hsel : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
        griessShortQ (Sum.inr (Sum.inr (d, golayOctadCoordinate o a)))).base =
          (griessShortQ (Sum.inr (Sum.inr (f, golayOctadCoordinate o b)))).base ↔
        e = trialityOctadPairFlip a b (octadTensorCharacterLabel o f) := by
      simpa only [trialityOctadPairFlip_xor] using griessOctadOdd_base_inside o e d f a b hab hd
    have h := octadXXCubic_pair_of_selector o e d f a b hd hsel
      (octadXXCubic_match_syndrome o e d f (golayOctadCoordinate o a) (golayOctadCoordinate o b))
    simpa only [trialityOctadPairFlip_xor] using h
  · rw [octadXXCubic_zero_of_code_selector o e d f _ _ hd,
      octadXXCubic_YConstant_zero_of_code_selector o d f _ _ hd, neg_zero, zero_mul]

/-- The actual diagonal OXX coefficient vanishes at every position inside the octad. -/
theorem octadXXCubic_inside_diagonal (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (a : Fin 8) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, golayOctadCoordinate o a))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, golayOctadCoordinate o a))) = 0 := by
  apply octadXXCubic_zero_of_no_match
  intro hb
  have hd := griessOctadOdd_base_code_selector o e d f _ _ hb
  have hi := ((griessOctadOdd_base_same o e d f (golayOctadCoordinate o a) hd).mp hb).1
  apply hi
  apply (golayOctadWord_ne_zero_iff o _).mp
  rw [golayOctadWord_local]
  exact one_ne_zero

/-- Different positions give no actual OXX coefficient if either lies outside the octad. -/
theorem octadXXCubic_outside_offdiagonal (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) (hij : i ≠ j)
    (hout : i ∉ golayOctadSupport o ∨ j ∉ golayOctadSupport o) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d, i))))
        (trialityXYZBasis 0 (finProdFinEquiv (f, j))) = 0 :=
  octadXXCubic_zero_of_no_match o e d f i j
    (griessOctadOdd_base_other_zero o e d f i j hij hout)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
