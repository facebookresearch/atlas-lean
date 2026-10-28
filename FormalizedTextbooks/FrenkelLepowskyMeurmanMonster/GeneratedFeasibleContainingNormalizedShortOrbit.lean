/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingE7ProjectionTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8FullLineOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSourceQPhaseFlip

/-! Oriented actual norm-twelve transport in the complete positive pointwise E8 group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

/-- Positive fixation of the original norm-twelve vector has trivial actual pointwise kernel. -/
theorem generatedFeasibleContaining_norm_twelve_positive_kernel
    (g : generatedTenthE8PointwiseSpatial)
    (hg : leechIntegralAction g.val generatedTenthE7NormTwelveLine =
      generatedTenthE7NormTwelveLine) : g = 1 := by
  rcases (generatedTenth_e8_full_unsigned_line_kernel g.val g.property).mp (Or.inl hg) with
    h | h
  · exact Subtype.ext h
  · rw [h] at hg
    exact False.elim (generatedTenth_e7_complement_not_positive_point hg)

/-- The actual oriented-vector stabilizer is exactly the identity subgroup. -/
theorem generatedFeasibleContaining_norm_twelve_positive_stabilizer :
    MulAction.stabilizer generatedTenthE8PointwiseSpatial generatedTenthE7NormTwelveLine =
      ⊥ := by
  apply le_antisymm
  · intro g hg
    change g = 1
    exact generatedFeasibleContaining_norm_twelve_positive_kernel g hg
  · exact bot_le

/-- The entire genuine positive pointwise group has a 512-vector oriented norm-twelve orbit.
This follows from the actual trivial stabilizer and the proved whole group order. -/
theorem generatedFeasibleContaining_norm_twelve_positive_orbit_card :
    Nat.card (MulAction.orbit generatedTenthE8PointwiseSpatial
      generatedTenthE7NormTwelveLine) = 512 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite generatedTenthE8PointwiseSpatial
  let _ := Fintype.ofFinite
    (MulAction.stabilizer generatedTenthE8PointwiseSpatial generatedTenthE7NormTwelveLine)
  let f : generatedTenthE8PointwiseSpatial →
      MulAction.orbit generatedTenthE8PointwiseSpatial generatedTenthE7NormTwelveLine :=
    fun g => ⟨g • generatedTenthE7NormTwelveLine, ⟨g, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨s, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite (MulAction.orbit generatedTenthE8PointwiseSpatial
    generatedTenthE7NormTwelveLine) := Finite.of_surjective f hf
  let _ := Fintype.ofFinite (MulAction.orbit generatedTenthE8PointwiseSpatial
    generatedTenthE7NormTwelveLine)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedTenthE8PointwiseSpatial generatedTenthE7NormTwelveLine
  simp only [← Nat.card_eq_fintype_card] at h
  rw [generatedFeasibleContaining_norm_twelve_positive_stabilizer,
    Subgroup.card_bot, generatedTenth_e8_pointwise_spatial_card] at h
  simpa using h

set_option maxHeartbeats 16000000 in
-- Check the complete sixteen genuine source words on all twenty-four anchor support coordinates.
/-- No nonidentity actual pointwise-octad representative preserves the original anchor octad. -/
theorem generatedFeasibleContaining_normalized_permutation_support (j : Fin 16) :
    (∀ i : Fin 24, (golayEncodedMask 2306).testBit i.val = true →
      (golayEncodedMask 2306).testBit
        ((generatedNinthStandardOctadRepresentative j).val i).val = true) → j = 0 := by
  have h : ∀ j : Fin 16,
      (∀ i : Fin 24, (golayEncodedMask 2306).testBit i.val = true →
        (golayEncodedMask 2306).testBit
          ((generatedNinthStandardOctadRepresentative j).val i).val = true) → j = 0 := by
    decide +kernel
  exact h j

set_option maxHeartbeats 4000000 in
-- Bind all twenty-four coordinates of the original identity representative.
/-- The original source representative at zero is the genuine identity permutation. -/
theorem generatedFeasibleContaining_normalized_permutation_zero :
    generatedNinthStandardOctadRepresentative 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  have h : ∀ i : Fin 24, (generatedNinthStandardOctadRepresentative 0).val i = i := by
    decide +kernel
  exact h

/-- The actual original companion codeword, retaining all its source coordinates. -/
def generatedFeasibleContainingNormalizedCompanionCode : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients 2306), ⟨_, rfl⟩⟩

/-- A genuine Golay sign vanishing on both actual source and companion octads is zero.
The proof uses the actual allowed Golay weights, including exclusion of weight twenty. -/
theorem generatedFeasibleContaining_normalized_sign_zero (c : golayCode)
    (hS : ∀ i : Fin 24, i.val < 8 → c.val i = 0)
    (hO : ∀ i : Fin 24, generatedFeasibleContainingNormalizedCompanionCode.val i = 1 →
      c.val i = 0) : c = 0 := by
  by_contra hc
  have hc0 : c.val ≠ 0 := by intro h; exact hc (Subtype.ext h)
  have hlo := golayCode_weight_ge_eight c.val c.property hc0
  have hbound (i : Fin 24) : (c.val i).val ≤
      if ¬ i.val < 8 ∧ generatedFeasibleContainingNormalizedCompanionCode.val i ≠ 1 then
        (1 : ℕ) else 0 := by
    by_cases hi : i.val < 8
    · simp [hi, hS i hi]
    · by_cases ho : generatedFeasibleContainingNormalizedCompanionCode.val i = 1
      · simp [ho, hO i ho]
      · rw [ite_eq_left ⟨hi, ho⟩]
        have h := (c.val i).val_lt
        omega
  have hcount : (∑ i : Fin 24,
      if ¬ i.val < 8 ∧ generatedFeasibleContainingNormalizedCompanionCode.val i ≠ 1 then
        (1 : ℕ) else 0) = 10 := by decide +kernel
  have hhi := (Finset.sum_le_sum (fun i _ => hbound i)).trans hcount.le
  have hw := golayCode_weights c.val c.property
  have hc8 : (∑ i : Fin 24, (c.val i).val) = 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    omega
  let d := golayStandardOctad - generatedFeasibleContainingNormalizedCompanionCode.val
  have hd : d ∈ golayCode :=
    golayCode.sub_mem golayStandardOctad_mem
      generatedFeasibleContainingNormalizedCompanionCode.property
  have hd12 : (∑ i : Fin 24, (d i).val) = 12 := by decide +kernel
  have hz (i : Fin 24) : (c.val i).val * (d i).val = 0 := by
    by_cases hi : i.val < 8
    · rw [hS i hi]
      simp
    · by_cases ho : generatedFeasibleContainingNormalizedCompanionCode.val i = 1
      · rw [hO i ho]
        simp
      · have hb : generatedFeasibleContainingNormalizedCompanionCode.val i = 0 := by
          have h : ∀ b : ZMod 2, b ≠ 1 → b = 0 := by decide
          exact h _ ho
        simp [d, golayStandardOctad, hi, hb]
  have he := golayBinary_difference_weight c.val d
  simp only [hz, Finset.sum_const_zero, mul_zero, add_zero, hc8, hd12] at he
  have hbad := golayCode_weights (c.val - d) (golayCode.sub_mem c.property hd)
  simp only [Pi.sub_apply] at hbad
  rw [he] at hbad
  norm_num at hbad

/-- The entire positive source-section pointwise group, identified by genuine conjugation
with the already counted complete original pointwise E8 group. -/
def generatedFeasibleContainingSourcePointwiseSpatial : Subgroup leechIsomSubgroup :=
  generatedTenthE8PointwiseSpatial.comap
    (MulAut.conj (golayPermutationIsometry generatedTenthE8StandardPermutation)).toMonoidHom

/-- Genuine conjugation identifies the entire actual source pointwise group, not a generated subset.
-/
def generatedFeasibleContainingSourcePointwiseEquiv :
    generatedFeasibleContainingSourcePointwiseSpatial ≃ generatedTenthE8PointwiseSpatial := by
  let f (e : leechIsomSubgroup ≃* leechIsomSubgroup) (K : Subgroup leechIsomSubgroup) :
      K.comap e.toMonoidHom ≃ K := {
    toFun := fun g => ⟨e g.val, g.property⟩
    invFun := fun h => ⟨e.symm h.val, by
      change e (e.symm h.val) ∈ K
      rw [e.apply_symm_apply]
      exact h.property⟩
    left_inv := fun g => Subtype.ext (e.symm_apply_apply g.val)
    right_inv := fun h => Subtype.ext (e.apply_symm_apply h.val) }
  exact f (MulAut.conj (golayPermutationIsometry generatedTenthE8StandardPermutation))
    generatedTenthE8PointwiseSpatial

/-- The whole genuine source-section positive pointwise group has order512. -/
theorem generatedFeasibleContainingSourcePointwiseSpatial_card :
    Nat.card generatedFeasibleContainingSourcePointwiseSpatial = 512 := by
  rw [Nat.card_congr generatedFeasibleContainingSourcePointwiseEquiv]
  exact generatedTenth_e8_pointwise_spatial_card

private theorem permutation_unit (p : golayAutomorphismSubgroup) (i : Fin 24) :
    (golayPermutationIsometry p).val (Pi.single i 1) = Pi.single (p.val i) 1 := by
  ext j
  change golayRealPermute p.val (Pi.single i 1) j = _
  simp only [golayRealPermute_apply, Pi.single_apply, p.val.symm_apply_eq]

private theorem permutation_inverse_unit (p : golayAutomorphismSubgroup) (i : Fin 24) :
    (golayPermutationIsometry p).val.symm (Pi.single i 1) = Pi.single (p.val.symm i) 1 := by
  have h := congrArg (golayPermutationIsometry p).val.symm
    (permutation_unit p (p.val.symm i))
  simpa only [LinearEquiv.symm_apply_apply, Equiv.apply_symm_apply] using h.symm

/-- Original source group membership is exactly positive fixation of all first-eight coordinate
vectors, with the entire actual Co0 action. -/
theorem generatedFeasibleContainingSourcePointwiseSpatial_mem (g : leechIsomSubgroup) :
    g ∈ generatedFeasibleContainingSourcePointwiseSpatial ↔
      ∀ i : Fin 24, i.val < 8 → g.val (Pi.single i 1) = Pi.single i 1 := by
  let p := generatedTenthE8StandardPermutation
  let t := golayPermutationIsometry p
  change t * g * t⁻¹ ∈ generatedTenthE8PointwiseSpatial ↔ _
  constructor
  · intro h i hi
    have hp : p.val i ∈ generatedTenthE7OctadSupport :=
      (generatedTenth_e8_standard_permutation_support i).mpr hi
    have hh := h (p.val i) hp
    change t.val (g.val (t.val.symm (Pi.single (p.val i) 1))) = Pi.single (p.val i) 1 at hh
    rw [permutation_inverse_unit, p.val.symm_apply_apply] at hh
    rw [← permutation_unit p i] at hh
    exact t.val.injective hh
  · intro h i hi
    have hj : (p.val.symm i).val < 8 := by
      apply (generatedTenth_e8_standard_permutation_support (p.val.symm i)).mp
      rwa [p.val.apply_symm_apply]
    change t.val (g.val (t.val.symm (Pi.single i 1))) = Pi.single i 1
    rw [permutation_inverse_unit, h _ hj, permutation_unit, p.val.apply_symm_apply]

/-- Every member of the whole actual source pointwise group has a genuine monomial decomposition
with its original permutation and sign fixed on the entire source octad. -/
theorem generatedFeasibleContainingSourcePointwiseSpatial_decomposition
    (g : generatedFeasibleContainingSourcePointwiseSpatial) :
    ∃ c : golayCode, ∃ p : generatedNinthStandardOctadPointwise,
      (∀ i : Fin 24, i.val < 8 → c.val i = 0) ∧
      g.val = golaySignIsometry c * golayPermutationIsometry p.val := by
  have hg := (generatedFeasibleContainingSourcePointwiseSpatial_mem g.val).mp g.property
  have hm : g.val ∈ golayMonomialSubgroup := by
    apply leech_fix_frame_mem_monomial
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding]
    have he : leechCoordinateEmbedding (leechCoordinateFrameLattice 0).val =
        (8 / Real.sqrt 8 : ℝ) • (Pi.single 0 1 : Fin 24 → ℝ) := by
      ext j
      by_cases hj : j = 0 <;>
        simp [leechCoordinateEmbedding, leechCoordinateFrameLattice,
          leechCoordinateFrameVector, hj]
    rw [he, map_smul, hg 0 (by decide)]
  obtain ⟨c, p, hcp⟩ := hm
  have hp (i : Fin 24) (hi : i.val < 8) : p.val i = i := by
    have h := congrFun (hg i hi) (p.val i)
    rw [hcp] at h
    change qSign (c.val (p.val i)) * (Pi.single i 1 : Fin 24 → ℝ)
      (p.val.symm (p.val i)) = (Pi.single i 1 : Fin 24 → ℝ) (p.val i) at h
    rw [p.val.symm_apply_apply] at h
    by_contra hn
    simp only [Pi.single_apply, ite_true, hn, ite_false, mul_one] at h
    have hs := qSign_sq (c.val (p.val i))
    rw [h, zero_mul] at hs
    norm_num at hs
  have hc (i : Fin 24) (hi : i.val < 8) : c.val i = 0 := by
    have h := congrFun (hg i hi) i
    rw [hcp] at h
    change qSign (c.val i) * (Pi.single i 1 : Fin 24 → ℝ) (p.val.symm i) =
      (Pi.single i 1 : Fin 24 → ℝ) i at h
    have hpi : p.val.symm i = i := p.val.symm_apply_eq.mpr (hp i hi).symm
    simp only [hpi, Pi.single_apply, ite_true, mul_one] at h
    exact (qSign_eq_one_iff _).mp h
  refine ⟨c, ⟨p, ?_⟩, hc, hcp⟩
  intro i
  exact hp (Fin.castAdd 16 i) (by simp)

private theorem octad_zero_sign (d : Fin 759) (i : Fin 24) :
    (griessOctadSignMask d 0).testBit i.val = false := by
  by_contra h
  have ht : (griessOctadSignMask d 0).testBit i.val = true := by
    cases hb : (griessOctadSignMask d 0).testBit i.val <;> simp_all
  obtain ⟨k, hk, _⟩ := (griessOctadSignMask_testBit d 0 i).mp ht
  have hz : ∀ k : Fin 8, (trialityEvenMask 0).testBit k.val = false := by decide +kernel
  rw [hz k] at hk
  contradiction

/-- Every physical coordinate of the original all-positive companion short vector. -/
theorem generatedFeasibleContaining_normalized_anchor_coordinate (i : Fin 24) :
    griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i =
      if (golayEncodedMask 2306).testBit i.val then 2 else 0 := by
  change (if (golayEncodedMask
    (golayOctadLabel generatedFeasibleContainingNormalizedOctadIndex).val).testBit i.val then
      if (griessOctadSignMask generatedFeasibleContainingNormalizedOctadIndex 0).testBit i.val
        then -2 else 2 else 0) = _
  rw [generatedFeasibleContainingNormalizedOctadIndex_label, octad_zero_sign]
  rfl

/-- The original companion code and original anchor support have identical coordinates. -/
theorem generatedFeasibleContaining_normalized_companion_support : ∀ i : Fin 24,
    generatedFeasibleContainingNormalizedCompanionCode.val i = 1 ↔
      (golayEncodedMask 2306).testBit i.val = true := by decide +kernel

private theorem monomial_coordinate (c : golayCode) (p : golayAutomorphismSubgroup)
    (u : leechIntegral) (i : Fin 24) :
    (leechIntegralAction (golaySignIsometry c * golayPermutationIsometry p) u).val
      (p.val i) = if c.val (p.val i) = 0 then u.val i else -u.val i := by
  rw [map_mul]
  change (leechIntegralAction (golaySignIsometry c)
    (leechIntegralAction (golayPermutationIsometry p) u)).val (p.val i) = _
  rw [leechIntegralAction_golaySign, leechIntegralAction_golayPermutation]
  simp only [golayIntegerSign, golayIntegerPermute, p.val.symm_apply_apply]

/-- Actual unsigned anchor fixation forces preservation of the whole original companion support. -/
theorem generatedFeasibleContaining_normalized_unsigned_support (c : golayCode)
    (p : golayAutomorphismSubgroup)
    (h : leechIntegralAction (golaySignIsometry c * golayPermutationIsometry p)
        (griessShortLatticeVector generatedFeasibleContainingNormalizedShortLabel) =
          griessShortLatticeVector generatedFeasibleContainingNormalizedShortLabel ∨
      leechIntegralAction (golaySignIsometry c * golayPermutationIsometry p)
        (griessShortLatticeVector generatedFeasibleContainingNormalizedShortLabel) =
          -griessShortLatticeVector generatedFeasibleContainingNormalizedShortLabel) :
    ∀ i : Fin 24, (golayEncodedMask 2306).testBit i.val = true →
      (golayEncodedMask 2306).testBit (p.val i).val = true := by
  intro i hi
  by_contra hn
  have hz : (golayEncodedMask 2306).testBit (p.val i).val = false := by
    cases hb : (golayEncodedMask 2306).testBit (p.val i).val <;> simp_all
  rcases h with h | h
  · have hh := congrArg (fun u : leechIntegral => u.val (p.val i)) h
    rw [monomial_coordinate] at hh
    change (if c.val (p.val i) = 0 then
        griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i else
          -griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i) =
            griessShortIntegral generatedFeasibleContainingNormalizedShortLabel (p.val i) at hh
    rw [generatedFeasibleContaining_normalized_anchor_coordinate,
      generatedFeasibleContaining_normalized_anchor_coordinate, hi, hz] at hh
    by_cases hc : c.val (p.val i) = 0 <;> simp [hc] at hh
  · have hh := congrArg (fun u : leechIntegral => u.val (p.val i)) h
    rw [monomial_coordinate] at hh
    change (if c.val (p.val i) = 0 then
        griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i else
          -griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i) =
            -griessShortIntegral generatedFeasibleContainingNormalizedShortLabel (p.val i) at hh
    rw [generatedFeasibleContaining_normalized_anchor_coordinate,
      generatedFeasibleContaining_normalized_anchor_coordinate, hi, hz] at hh
    by_cases hc : c.val (p.val i) = 0 <;> simp [hc] at hh

/-- Every genuine source pointwise element fixing the original preferred anchor is identity. -/
theorem generatedFeasibleContaining_normalized_preferred_kernel
    (g : generatedFeasibleContainingSourcePointwiseSpatial)
    (hg : griessShortPermutation g.val generatedFeasibleContainingNormalizedShortLabel =
      generatedFeasibleContainingNormalizedShortLabel) : g = 1 := by
  obtain ⟨c, p, hc, hcp⟩ :=
    generatedFeasibleContainingSourcePointwiseSpatial_decomposition g
  have hs := generatedE8Short_integral_sign g.val
    generatedFeasibleContainingNormalizedShortLabel
  rw [hg, hcp] at hs
  have hp := generatedFeasibleContaining_normalized_unsigned_support c p.val hs
  obtain ⟨j, hj⟩ := generatedTenth_e8_standard_affine_surjective p
  have hpj : p.val = generatedNinthStandardOctadRepresentative j := congrArg Subtype.val hj.symm
  rw [hpj] at hp
  have hj0 := generatedFeasibleContaining_normalized_permutation_support j hp
  have hp1 : p.val = 1 := by
    rw [hpj, hj0, generatedFeasibleContaining_normalized_permutation_zero]
  have hperm : golayPermutationIsometry (1 : golayAutomorphismSubgroup) = 1 :=
    golayPermutationHom.map_one
  rw [hp1, hperm, mul_one] at hcp
  have hs' := generatedE8Short_integral_sign g.val
    generatedFeasibleContainingNormalizedShortLabel
  rw [hg, hcp] at hs'
  have hpos : leechIntegralAction (golaySignIsometry c)
      (griessShortLatticeVector generatedFeasibleContainingNormalizedShortLabel) =
        griessShortLatticeVector generatedFeasibleContainingNormalizedShortLabel := by
    rcases hs' with h | h
    · exact h
    · have hh := congrArg (fun u : leechIntegral => u.val 0) h
      rw [leechIntegralAction_golaySign] at hh
      change (if c.val 0 = 0 then
          griessShortIntegral generatedFeasibleContainingNormalizedShortLabel 0 else
            -griessShortIntegral generatedFeasibleContainingNormalizedShortLabel 0) =
              -griessShortIntegral generatedFeasibleContainingNormalizedShortLabel 0 at hh
      rw [hc 0 (by decide), generatedFeasibleContaining_normalized_anchor_coordinate] at hh
      have hb : (golayEncodedMask 2306).testBit 0 = true := by decide +kernel
      simp only [Fin.val_zero, hb, ite_true] at hh
      norm_num at hh
  have hcO (i : Fin 24)
      (hi : generatedFeasibleContainingNormalizedCompanionCode.val i = 1) : c.val i = 0 := by
    have hh := congrArg (fun u : leechIntegral => u.val i) hpos
    rw [leechIntegralAction_golaySign] at hh
    change (if c.val i = 0 then
        griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i else
          -griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i) =
            griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i at hh
    rw [generatedFeasibleContaining_normalized_anchor_coordinate,
      (generatedFeasibleContaining_normalized_companion_support i).mp hi] at hh
    by_contra hn
    rw [ite_eq_right hn] at hh
    norm_num at hh
  have hc0 := generatedFeasibleContaining_normalized_sign_zero c hc hcO
  apply Subtype.ext
  rw [hcp, hc0]
  exact golaySignHom.map_one

/-- The faithful preferred-label orbit map of the entire actual source pointwise group. -/
def generatedFeasibleContainingNormalizedPointwiseOrbitMap
    (g : generatedFeasibleContainingSourcePointwiseSpatial) : GriessShortIndex :=
  griessShortPermutation g.val generatedFeasibleContainingNormalizedShortLabel

/-- Distinct actual pointwise elements have distinct preferred anchor images. -/
theorem generatedFeasibleContainingNormalizedPointwiseOrbitMap_injective :
    Function.Injective generatedFeasibleContainingNormalizedPointwiseOrbitMap := by
  intro g h he
  have hk : griessShortPermutation (g⁻¹ * h).val
      generatedFeasibleContainingNormalizedShortLabel =
        generatedFeasibleContainingNormalizedShortLabel := by
    change griessShortPermutation (g.val⁻¹ * h.val) _ = _
    rw [map_mul, map_inv]
    change (griessShortPermutation g.val).symm
      (griessShortPermutation h.val generatedFeasibleContainingNormalizedShortLabel) = _
    change griessShortPermutation g.val generatedFeasibleContainingNormalizedShortLabel =
      griessShortPermutation h.val generatedFeasibleContainingNormalizedShortLabel at he
    rw [← he, Equiv.symm_apply_apply]
  have h1 := generatedFeasibleContaining_normalized_preferred_kernel (g⁻¹ * h) hk
  exact inv_mul_eq_one.mp h1

/-- The complete genuine preferred source pointwise orbit has exactly512 labels, with no
transitivity or numerical stabilizer premise. -/
theorem generatedFeasibleContainingNormalizedPointwiseOrbitMap_card :
    Nat.card (Set.range generatedFeasibleContainingNormalizedPointwiseOrbitMap) = 512 := by
  rw [← Nat.card_congr (Equiv.ofInjective
    generatedFeasibleContainingNormalizedPointwiseOrbitMap
      generatedFeasibleContainingNormalizedPointwiseOrbitMap_injective)]
  exact generatedFeasibleContainingSourcePointwiseSpatial_card

/-- The entire original normalized preferred octad catalogue, including every perpendicular sign.
-/
def generatedFeasibleContainingNormalizedOctadPairs : Finset (Fin 759 × Fin 64) :=
  ((generatedFeasibleContainingSelectedIncidentOctads 0) ×ˢ Finset.univ).filter fun z =>
    griessShortIntegral (Sum.inr (Sum.inl z)) 0 =
      griessShortIntegral (Sum.inr (Sum.inl z)) 1

private theorem product_filter_card {α β : Type*} [Fintype β]
    (s : Finset α) (P : α → β → Prop) [∀ a, DecidablePred (P a)] :
    ((s ×ˢ Finset.univ).filter fun z => P z.1 z.2).card =
      ∑ a ∈ s, (Finset.univ.filter (P a)).card := by
  classical
  have he : ((s ×ˢ Finset.univ).filter fun z => P z.1 z.2) =
      s.biUnion (fun a => (Finset.univ.filter (P a)).map
        ⟨fun b => (a, b), fun b c h => Prod.mk.inj h |>.2⟩) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk, true_and]
    constructor
    · rintro ⟨ha, hp⟩
      exact ⟨z.1, ha, z.2, hp, Prod.eta z⟩
    · rintro ⟨a, ha, b, hb, hz⟩
      cases hz
      exact ⟨ha, hb⟩
  rw [he, Finset.card_biUnion]
  · simp only [Finset.card_map]
  · intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro z ha hb
    obtain ⟨u, _, hu⟩ := Finset.mem_map.mp ha
    obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hb
    exact hab (congrArg Prod.fst (hu.trans hv.symm))

/-- All sixteen actual normalized incident octads contribute their genuine thirty-two signs. -/
theorem generatedFeasibleContainingNormalizedOctadPairs_card :
    generatedFeasibleContainingNormalizedOctadPairs.card = 512 := by
  have hc := product_filter_card (generatedFeasibleContainingSelectedIncidentOctads 0)
    (fun o e => griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1)
  change generatedFeasibleContainingNormalizedOctadPairs.card = _ at hc
  rw [hc]
  have he (o : Fin 759) (ho : o ∈ generatedFeasibleContainingSelectedIncidentOctads 0) :
      (Finset.univ.filter fun e : Fin 64 =>
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
          griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1).card = 32 := by
    apply generatedFeasibleOctadContaining_physical_count
    exact (Finset.mem_filter.mp ho).1
  rw [Finset.sum_congr rfl (fun o ho => he o ho), Finset.sum_const, nsmul_eq_mul,
    generatedFeasibleContainingSelectedIncidentOctads_card]
  rfl

/-- The normalized actual labels are the genuine embeddings of the complete octad-sign catalogue.
-/
def generatedFeasibleContainingNormalizedShortLabels : Finset GriessShortIndex :=
  generatedFeasibleContainingNormalizedOctadPairs.map
    ⟨fun z => Sum.inr (Sum.inl z), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩

/-- The complete normalized preferred short catalogue contains exactly512 actual labels. -/
theorem generatedFeasibleContainingNormalizedShortLabels_card :
    generatedFeasibleContainingNormalizedShortLabels.card = 512 := by
  rw [generatedFeasibleContainingNormalizedShortLabels, Finset.card_map,
    generatedFeasibleContainingNormalizedOctadPairs_card]

/-- Positive pointwise source fixation retains every actual integral first-eight coordinate. -/
theorem generatedFeasibleContainingSourcePointwiseSpatial_coordinate
    (g : generatedFeasibleContainingSourcePointwiseSpatial) (u : leechIntegral)
    (i : Fin 24) (hi : i.val < 8) : (leechIntegralAction g.val u).val i = u.val i := by
  obtain ⟨c, p, hc, hcp⟩ :=
    generatedFeasibleContainingSourcePointwiseSpatial_decomposition g
  have hp : p.val.val i = i := by
    let j : Fin 8 := ⟨i.val, hi⟩
    have h := p.property j
    have hj : Fin.castAdd 16 j = i := Fin.ext rfl
    rwa [hj] at h
  have hpi : p.val.val.symm i = i := p.val.val.symm_apply_eq.mpr hp.symm
  rw [hcp, map_mul]
  change (leechIntegralAction (golaySignIsometry c)
    (leechIntegralAction (golayPermutationIsometry p.val) u)).val i = _
  rw [leechIntegralAction_golaySign, leechIntegralAction_golayPermutation]
  simp only [golayIntegerSign, golayIntegerPermute, hpi, hc i hi, ite_true]

/-- The anchor occupies exactly source coordinates zero and one inside the genuine first octad.
-/
theorem generatedFeasibleContaining_normalized_anchor_source (i : Fin 24) (hi : i.val < 8) :
    griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i =
      if i = 0 ∨ i = 1 then 2 else 0 := by
  rw [generatedFeasibleContaining_normalized_anchor_coordinate]
  have h : ∀ i : Fin 24, i.val < 8 →
      ((golayEncodedMask 2306).testBit i.val = true ↔ i = 0 ∨ i = 1) := by decide +kernel
  simp only [h i hi]

private theorem short_coordinate_two_octad (r : GriessShortIndex)
    (h : (griessShortIntegral r 0) ^ 2 = 4) :
    ∃ z : Fin 759 × Fin 64, r = Sum.inr (Sum.inl z) := by
  rcases r with z | z
  · rcases z with ⟨s, p⟩
    change (4 * (if (0 : Fin 24) = (griessCoordinatePair p).1 then (1 : ℤ) else 0) +
      (if s = 0 then -4 else 4) *
        (if (0 : Fin 24) = (griessCoordinatePair p).2 then 1 else 0)) ^ 2 = 4 at h
    split_ifs at h <;> norm_num at h
  · rcases z with z | z
    · exact ⟨z, rfl⟩
    · rcases z with ⟨d, j⟩
      change ((if (golayEncodedMask d.val).testBit 0 then (-1 : ℤ) else 1) *
        (if (0 : Fin 24) = j then -3 else 1)) ^ 2 = 4 at h
      split_ifs at h <;> norm_num at h

/-- Every actual preferred orbit image retains the complete source coordinates up to its actual
preferred orientation. -/
theorem generatedFeasibleContainingNormalizedPointwiseOrbitMap_coordinates
    (g : generatedFeasibleContainingSourcePointwiseSpatial) :
    (∀ i : Fin 24, i.val < 8 →
      griessShortIntegral (generatedFeasibleContainingNormalizedPointwiseOrbitMap g) i =
        griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i) ∨
    (∀ i : Fin 24, i.val < 8 →
      griessShortIntegral (generatedFeasibleContainingNormalizedPointwiseOrbitMap g) i =
        -griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i) := by
  rcases generatedE8Short_integral_sign g.val
      generatedFeasibleContainingNormalizedShortLabel with h | h
  · left
    intro i hi
    have hh := congrArg (fun u : leechIntegral => u.val i) h
    rw [generatedFeasibleContainingSourcePointwiseSpatial_coordinate g _ i hi] at hh
    exact hh.symm
  · right
    intro i hi
    have hh := congrArg (fun u : leechIntegral => u.val i) h
    rw [generatedFeasibleContainingSourcePointwiseSpatial_coordinate g _ i hi] at hh
    change griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i =
      -griessShortIntegral (generatedFeasibleContainingNormalizedPointwiseOrbitMap g) i at hh
    omega

private theorem selected_square_of_squares (r : GriessShortIndex)
    (hs : ∀ i : Fin 24, i.val < 8 →
      (griessShortIntegral r i)^2 =
        (griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i)^2) :
    generatedFeasibleContainingSelectedShortSquare r = 8 := by
  rw [generatedFeasibleContainingSelectedShortSquare,
    generatedFeasibleContaining_selected_source_word]
  unfold generatedFeasibleContainingSelectedSquare
  have he (i : Fin 24) : ((golayStandardOctad i).val : ℤ) *
      (griessShortIntegral r i)^2 = if i = 0 ∨ i = 1 then (4 : ℤ) else 0 := by
    by_cases hi : i.val < 8
    · rw [hs i hi, generatedFeasibleContaining_normalized_anchor_source i hi]
      simp only [golayStandardOctad, hi, ite_true]
      rw [show ((1 : ZMod 2).val : ℤ) = 1 from by decide +kernel]
      by_cases hn : i = 0 ∨ i = 1 <;> simp [hn]
    · have hn : ¬(i = 0 ∨ i = 1) := by
        rintro (h | h) <;> subst i <;> norm_num at hi
      simp [golayStandardOctad, hi, hn]
  simp_rw [he]
  decide +kernel

/-- Every genuine source pointwise orbit image belongs to the entire original normalized catalogue.
-/
theorem generatedFeasibleContainingNormalizedPointwiseOrbitMap_mem
    (g : generatedFeasibleContainingSourcePointwiseSpatial) :
    generatedFeasibleContainingNormalizedPointwiseOrbitMap g ∈
      generatedFeasibleContainingNormalizedShortLabels := by
  let r := generatedFeasibleContainingNormalizedPointwiseOrbitMap g
  have hc := generatedFeasibleContainingNormalizedPointwiseOrbitMap_coordinates g
  have hs (i : Fin 24) (hi : i.val < 8) : (griessShortIntegral r i)^2 =
      (griessShortIntegral generatedFeasibleContainingNormalizedShortLabel i)^2 := by
    rcases hc with h | h
    · rw [h i hi]
    · rw [h i hi]
      ring
  have h01 : griessShortIntegral r 0 = griessShortIntegral r 1 := by
    rcases hc with h | h
    · rw [h 0 (by decide), h 1 (by decide),
        generatedFeasibleContaining_normalized_anchor_source 0 (by decide),
        generatedFeasibleContaining_normalized_anchor_source 1 (by decide)]
      norm_num
    · rw [h 0 (by decide), h 1 (by decide),
        generatedFeasibleContaining_normalized_anchor_source 0 (by decide),
        generatedFeasibleContaining_normalized_anchor_source 1 (by decide)]
      norm_num
  have h0 : (griessShortIntegral r 0)^2 = 4 := by
    rw [hs 0 (by decide), generatedFeasibleContaining_normalized_anchor_source 0 (by decide)]
    norm_num
  obtain ⟨⟨o, e⟩, hr⟩ := short_coordinate_two_octad r h0
  have ho : o ∈ generatedFeasibleOctadContainingLabels := by
    have h1 : (griessShortIntegral r 1)^2 = 4 := by rw [← h01]; exact h0
    rw [hr] at h0 h1
    have hb0 : (golayEncodedMask (golayOctadLabel o).val).testBit 0 = true := by
      by_contra hn
      have hb : (golayEncodedMask (golayOctadLabel o).val).testBit 0 = false := by
        cases h : (golayEncodedMask (golayOctadLabel o).val).testBit 0 <;> simp_all
      simp only [griessShortIntegral, Fin.val_zero, hb, Bool.false_eq_true, ite_false] at h0
      norm_num at h0
    have hb1 : (golayEncodedMask (golayOctadLabel o).val).testBit 1 = true := by
      by_contra hn
      have hb : (golayEncodedMask (golayOctadLabel o).val).testBit 1 = false := by
        cases h : (golayEncodedMask (golayOctadLabel o).val).testBit 1 <;> simp_all
      simp only [griessShortIntegral, Fin.val_one, hb, Bool.false_eq_true, ite_false] at h1
      norm_num at h1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0, hb1⟩
  have hw : generatedFeasibleContainingOctadSelectedWeight o = 2 := by
    have hh := selected_square_of_squares r hs
    rw [hr, generatedFeasibleContainingSelectedShortSquare_octad_weight] at hh
    omega
  apply Finset.mem_map.mpr
  refine ⟨(o, e), ?_, hr.symm⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
  · exact Finset.mem_filter.mpr ⟨ho, hw⟩
  · exact hr ▸ h01

/-- The complete original normalized catalogue is reached by genuine whole-source pointwise
Co0 elements; its transitivity follows from the actual faithful512-element orbit. -/
theorem generatedFeasibleContaining_normalized_short_transitive
    (r : GriessShortIndex) (hr : r ∈ generatedFeasibleContainingNormalizedShortLabels) :
    ∃ g : generatedFeasibleContainingSourcePointwiseSpatial,
      griessShortPermutation g.val generatedFeasibleContainingNormalizedShortLabel = r := by
  let f : generatedFeasibleContainingSourcePointwiseSpatial →
      {r : GriessShortIndex // r ∈ generatedFeasibleContainingNormalizedShortLabels} :=
    fun g => ⟨generatedFeasibleContainingNormalizedPointwiseOrbitMap g,
      generatedFeasibleContainingNormalizedPointwiseOrbitMap_mem g⟩
  have hi : Function.Injective f := by
    intro g h he
    exact generatedFeasibleContainingNormalizedPointwiseOrbitMap_injective
      (congrArg Subtype.val he)
  have hc : Nat.card generatedFeasibleContainingSourcePointwiseSpatial =
      Nat.card {r : GriessShortIndex // r ∈ generatedFeasibleContainingNormalizedShortLabels} := by
    rw [generatedFeasibleContainingSourcePointwiseSpatial_card,
      Nat.card_eq_fintype_card, Fintype.card_coe,
      generatedFeasibleContainingNormalizedShortLabels_card]
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi, hc⟩).surjective
  obtain ⟨g, hg⟩ := hsurj ⟨r, hr⟩
  exact ⟨g, congrArg Subtype.val hg⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
