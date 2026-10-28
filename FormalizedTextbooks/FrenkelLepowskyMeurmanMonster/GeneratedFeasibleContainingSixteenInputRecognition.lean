/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenProjectionNormalization

/-! Genuine signed recognition of the original selected-square-sixteen transition inputs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual original dictionary index of the unordered physical pair (2,8). -/
def generatedFeasibleContainingSixteenPair : Fin 276 :=
  griessCoordinatePairEquiv.symm ⟨(2, 8), by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by decide⟩⟩

/-- Its complete original preferred pair coordinates. -/
theorem generatedFeasibleContainingSixteenPair_coordinates :
    griessCoordinatePair generatedFeasibleContainingSixteenPair = (2, 8) :=
  congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply _)

/-- The preferred positive original pair crossing the third coordinate and the octad complement. -/
def generatedFeasibleContainingSixteenShortLabel : GriessShortIndex :=
  Sum.inl (1, generatedFeasibleContainingSixteenPair)

private theorem coordinate_four_pair (r : GriessShortIndex)
    (h : (griessShortIntegral r 2)^2 = 16) :
    ∃ s : Fin 2, ∃ p : Fin 276, r = Sum.inl (s, p) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · exact ⟨s, p, rfl⟩
  · change (if (golayEncodedMask (golayOctadLabel o).val).testBit 2 then
        if (griessOctadSignMask o e).testBit 2 then (-2 : ℤ) else 2 else 0)^2 = 16 at h
    split_ifs at h <;> norm_num at h
  · change ((if (golayEncodedMask d.val).testBit 2 then (-1 : ℤ) else 1) *
        (if (2 : Fin 24) = j then -3 else 1))^2 = 16 at h
    split_ifs at h <;> norm_num at h

/-- Complete coordinate normalization forces the actual preferred label to cross the source
at coordinate two and its complement at one genuine outside coordinate. -/
theorem generatedFeasibleContaining_sixteen_normalized_pair (r : GriessShortIndex)
    (h2 : (griessShortIntegral r 2)^2 = 16)
    (hz : ∀ i : Fin 24, i.val < 8 → i ≠ 2 → griessShortIntegral r i = 0) :
    ∃ s : Fin 2, ∃ p : Fin 276, r = Sum.inl (s, p) ∧
      (griessCoordinatePair p).1 = 2 ∧ 8 ≤ (griessCoordinatePair p).2.val := by
  obtain ⟨s, p, hr⟩ := coordinate_four_pair r h2
  subst r
  have hlt : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
    (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  have hne : (griessCoordinatePair p).1 ≠ (griessCoordinatePair p).2 := ne_of_lt hlt
  have hhit : (2 : Fin 24) = (griessCoordinatePair p).1 ∨
      (2 : Fin 24) = (griessCoordinatePair p).2 := by
    by_contra hn
    push Not at hn
    simp [griessShortIntegral, hn.1, hn.2] at h2
  have hp1 : (griessCoordinatePair p).1 = 2 := by
    rcases hhit with h | h
    · exact h.symm
    · have hp : (griessCoordinatePair p).1 ≠ 2 := by rw [h]; exact hne
      have hi : (griessCoordinatePair p).1.val < 8 := by
        change (griessCoordinatePair p).1.val < (griessCoordinatePair p).2.val at hlt
        rw [← h] at hlt
        omega
      have hh := hz (griessCoordinatePair p).1 hi hp
      simp [griessShortIntegral, hne] at hh
  refine ⟨s, p, rfl, hp1, ?_⟩
  by_contra hn
  have hi : (griessCoordinatePair p).2.val < 8 := by omega
  have hp : (griessCoordinatePair p).2 ≠ 2 := by
    rw [← hp1]
    exact hne.symm
  have hh := hz (griessCoordinatePair p).2 hi hp
  simp only [griessShortIntegral, hne.symm, ite_false, ite_true, mul_zero,
    zero_add, mul_one] at hh
  split_ifs at hh
  norm_num at hh

/-- Any normalized preferred pair is sent to the original positive (2,8) pair by a genuine
source-section pointwise monomial, retaining the positive first root. -/
theorem generatedFeasibleContaining_sixteen_normalized_spatial_transport
    (s : Fin 2) (p : Fin 276) (hp1 : (griessCoordinatePair p).1 = 2)
    (hp2 : 8 ≤ (griessCoordinatePair p).2.val) :
    ∃ g : leechIsomSubgroup,
      generatedAxisE8ImageSection g
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
          generatedAxisE8CoordinateSection
            (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) ∧
      leechIntegralAction g
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∧
      griessShortPermutation g (Sum.inl (s, p)) = generatedFeasibleContainingSixteenShortLabel := by
  let j : Fin 16 := ⟨(griessCoordinatePair p).2.val - 8, by
    have h := (griessCoordinatePair p).2.isLt
    omega⟩
  let a := (generatedNinthStandardOctadRepresentative j)⁻¹
  have ha (i : Fin 24) (hi : i.val < 8) : a.val i = i := by
    let k : Fin 8 := ⟨i.val, hi⟩
    have h := generatedNinth_standard_octad_representative_fixed j k
    have hk : Fin.castAdd 16 k = i := Fin.ext rfl
    rw [hk] at h
    apply (generatedNinthStandardOctadRepresentative j).val.injective
    change (generatedNinthStandardOctadRepresentative j).val
      ((generatedNinthStandardOctadRepresentative j).val.symm i) = _
    rw [Equiv.apply_symm_apply, h]
  have haj : a.val (griessCoordinatePair p).2 = 8 := by
    have h := generatedNinth_standard_octad_representative_outside j
    have hj : Fin.natAdd 8 j = (griessCoordinatePair p).2 := Fin.ext (by dsimp [j]; omega)
    rw [hj] at h
    change (generatedNinthStandardOctadRepresentative j).val.symm _ = _
    rw [← h, Equiv.symm_apply_apply]
  let d : golayCode := ⟨fun i => if i.val < 8 then 0 else if s = 0 then 1 else 0, by
    by_cases hs : s = 0
    · change (fun i : Fin 24 => if i.val < 8 then 0 else if s = 0 then 1 else 0) ∈ golayCode
      simp only [hs, ite_true]
      have he : (fun i : Fin 24 => if i.val < 8 then (0 : ZMod 2) else 1) =
          (fun _ => 1) - golayStandardOctad := by
        ext i
        by_cases hi : i.val < 8 <;> simp [golayStandardOctad, hi]
      rw [he]
      have hall : (fun _ : Fin 24 => (1 : ZMod 2)) ∈ golayCode := by
        rw [← golay_all_one]
        exact ⟨_, rfl⟩
      exact golayCode.sub_mem hall golayStandardOctad_mem
    · simp only [hs, ite_false, ite_self]
      exact golayCode.zero_mem⟩
  let g := golaySignIsometry d * golayPermutationIsometry a
  have hpoint (i : Fin 24) (hi : i.val < 8) : g.val (Pi.single i 1) = Pi.single i 1 := by
    ext k
    change qSign (d.val k) * (Pi.single i 1 : Fin 24 → ℝ) (a.val.symm k) =
      (Pi.single i 1 : Fin 24 → ℝ) k
    have hk : a.val.symm k = i ↔ k = i := by rw [a.val.symm_apply_eq, ha i hi]
    by_cases hki : k = i
    · subst k
      simp [Pi.single_apply, hk, d, hi]
    · simp [hk, hki]
  have hfixed (v : leechIntegral) (hv : generatedOctadSupported golayStandardOctad v.val) :
      leechIntegralAction g v = v := by
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding]
    rw [pi_eq_sum_univ' (leechCoordinateEmbedding v.val), map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    by_cases hi : i.val < 8
    · rw [hpoint i hi]
    · have hz := hv i (by simp [golayStandardOctad, hi])
      change ((v.val i : ℝ) / Real.sqrt 8) • g.val (Pi.single i 1) =
        ((v.val i : ℝ) / Real.sqrt 8) • (Pi.single i 1)
      rw [hz]
      simp
  have hpres : generatedOctadPreserves golayStandardOctad g := by
    intro v
    constructor
    · intro hv
      have h := hfixed (leechIntegralAction g v) hv
      have hh : leechIntegralAction g v = v := (leechIntegralAction g).injective h
      rwa [hh] at hv
    · intro hv
      rw [hfixed v hv]
      exact hv
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [generatedFeasibleContaining_selected_source_word]
    exact generatedAxisE8_preserving_image _ _ hpres
  · apply hfixed
    intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num [golayStandardOctad] at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num [golayStandardOctad] at hi
    simp [griessShortLatticeVector, griessShortIntegral,
      generatedFeasiblePhysicalRootPair_coordinates, h0, h1]
  · apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
    left
    apply Subtype.ext
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    funext i
    have ha2 : a.val 2 = 2 := ha 2 (by decide)
    have hi2 : a.val.symm i = 2 ↔ i = 2 := by rw [a.val.symm_apply_eq, ha2]
    have hij : a.val.symm i = (griessCoordinatePair p).2 ↔ i = 8 := by
      rw [a.val.symm_apply_eq, haj]
    change golayIntegerSign d.val
      (golayIntegerPermute a.val (griessShortIntegral (Sum.inl (s, p)))) i =
        griessShortIntegral generatedFeasibleContainingSixteenShortLabel i
    simp only [golayIntegerSign, golayIntegerPermute, griessShortIntegral, hp1,
      hi2, hij, generatedFeasibleContainingSixteenShortLabel,
      generatedFeasibleContainingSixteenPair_coordinates]
    by_cases h2 : i = 2
    · subst i
      simp [d]
    · by_cases h8 : i = 8
      · subst i
        by_cases hs : s = 0 <;> simp [d, hs]
      · simp [h2, h8]

private theorem projection_neg (u : leechIntegral) :
    generatedFeasibleContainingDoubledProjection (-u) =
      -generatedFeasibleContainingDoubledProjection u := by
  unfold generatedFeasibleContainingDoubledProjection
  rw [map_neg]
  abel

/-- Every entire original selected-square-sixteen perpendicular preferred short vector reaches
one fixed original preferred anchor under a genuine source-section and positive-first-root fixer.
-/
theorem generatedFeasibleContaining_selected_sixteen_spatial_transport (r : GriessShortIndex)
    (hS : generatedFeasibleContainingSelectedShortSquare r = 16)
    (hP : griessShortIntegral r 0 = griessShortIntegral r 1) :
    ∃ g : leechIsomSubgroup,
      generatedAxisE8ImageSection g
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
          generatedAxisE8CoordinateSection
            (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) ∧
      leechIntegralAction g
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∧
      griessShortPermutation g r = generatedFeasibleContainingSixteenShortLabel := by
  obtain ⟨g, hgS, hgP, hgF⟩ :=
    generatedFeasibleContaining_selected_sixteen_projection_normalize r hS hP
  let v := griessShortPermutation g r
  have hproj : generatedFeasibleContainingDoubledProjection (griessShortLatticeVector v) =
      leechCoordinateFrameLattice 2 ∨
    generatedFeasibleContainingDoubledProjection (griessShortLatticeVector v) =
      -leechCoordinateFrameLattice 2 := by
    have hc := generatedFeasibleContaining_doubled_projection_commutes g hgS
      (griessShortLatticeVector r)
    rw [hgF] at hc
    rcases generatedE8Short_integral_sign g r with h | h
    · rw [h] at hc
      exact Or.inl hc
    · rw [h, projection_neg] at hc
      have hh := congrArg (fun u : leechIntegral => -u) hc
      simp only [neg_neg] at hh
      exact Or.inr hh
  have h2 : (griessShortIntegral v 2)^2 = 16 := by
    rcases hproj with h | h
    all_goals
      have hc := congrArg (fun u : leechIntegral => u.val 2) h
      rw [generatedFeasibleContainingDoubledProjection_coordinate] at hc
      first
      | change 2 * griessShortIntegral v 2 = 8 at hc
      | change 2 * griessShortIntegral v 2 = -8 at hc
      nlinarith
  have hz (i : Fin 24) (hi : i.val < 8) (hne : i ≠ 2) :
      griessShortIntegral v i = 0 := by
    rcases hproj with h | h
    all_goals
      have hc := congrArg (fun u : leechIntegral => u.val i) h
      rw [generatedFeasibleContainingDoubledProjection_coordinate, ite_eq_left hi] at hc
      first
      | change 2 * griessShortIntegral v i =
          (Pi.single (2 : Fin 24) (8 : ℤ) : Fin 24 → ℤ) i at hc
      | change 2 * griessShortIntegral v i =
          -(Pi.single (2 : Fin 24) (8 : ℤ) : Fin 24 → ℤ) i at hc
      simp only [Pi.single_apply, hne, ite_false, neg_zero] at hc
      omega
  obtain ⟨s, p, hv, hp1, hp2⟩ :=
    generatedFeasibleContaining_sixteen_normalized_pair v h2 hz
  obtain ⟨t, htS, htP, htR⟩ :=
    generatedFeasibleContaining_sixteen_normalized_spatial_transport s p hp1 hp2
  refine ⟨t * g, ?_, ?_, ?_⟩
  · apply (generatedAxisE8SectionStabilizer_mem _ _).mp
    exact (generatedAxisE8SectionStabilizer _).mul_mem
      ((generatedAxisE8SectionStabilizer_mem _ _).mpr htS)
      ((generatedAxisE8SectionStabilizer_mem _ _).mpr hgS)
  · rw [map_mul, LinearEquiv.mul_apply, hgP, htP]
  · rw [map_mul]
    change griessShortPermutation t v = _
    rw [hv]
    exact htR

private theorem preferred_short_phase_product (r s : GriessShortIndex) :
    toAdd (localAxisQPhase s (griessShortQ r)) =
      toAdd (griessShortQ r * griessShortQ s).coeff +
        toAdd (griessShortQ s * griessShortQ r).coeff := by
  change qBeta (toAdd (griessShortQ r).base) (toAdd (griessShortQ s).base) +
    qBeta (toAdd (griessShortQ s).base) (toAdd (griessShortQ r).base) =
      (0 + 0 + qBeta (toAdd (griessShortQ r).base) (toAdd (griessShortQ s).base)) +
        (0 + 0 + qBeta (toAdd (griessShortQ s).base) (toAdd (griessShortQ r).base))
  simp only [zero_add]

private theorem prototype_pair_phase (s : Fin 2) (p : Fin 276) :
    toAdd (localAxisQPhase (Sum.inl (s, p))
      (griessShortQ generatedFeasibleContainingOctadPrototypeLabel)) =
        golayEncoder (golayLabelCoefficients 2063) (griessCoordinatePair p).1 +
          golayEncoder (golayLabelCoefficients 2063) (griessCoordinatePair p).2 := by
  rw [generatedFeasibleContainingOctadPrototypeLabel, preferred_short_phase_product,
    griessPairOctadQ_product_coeff, add_zero, griessShortQ_product_coeff_spinDot,
    griessPairQ_modulation, griessOctad_translation,
    generatedFeasibleContainingOctadPrototypeIndex_label]
  have hz : griessOctadOmegaCoefficient 0 = 0 := by decide +kernel
  rw [hz, zero_smul, add_zero, griessPairSyndrome_dot]

/-- The original prototype2063 preferred Q element commutes with every actual nonzero short
coordinate of the entire original containing source. -/
theorem generatedFeasibleContaining_sixteen_phase_source_support (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFeasibleContainingOctadPrototypeIndex r) :
    localShortPhase (localFiberIncl
      (griessShortQ generatedFeasibleContainingOctadPrototypeLabel)) r = 0 := by
  rw [localAxisQPhase_eq_short_phase]
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · rw [prototype_pair_phase]
    change generatedOctadPairSupport generatedFeasibleContainingOctadPrototypeIndex p at hr
    unfold generatedOctadPairSupport at hr
    rw [generatedFeasibleContainingOctadPrototypeIndex_label] at hr
    simp only [golayLabelEncoder_boolean, hr.1, hr.2, golayBooleanCast]
    decide
  · change o = generatedFeasibleContainingOctadPrototypeIndex at hr
    subst o
    rw [generatedFeasibleContainingOctadPrototypeLabel, preferred_short_phase_product,
      griessOctadQ_product_coeff, griessOctadQ_product_coeff]
    rfl
  · exact False.elim hr

/-- The phase word fixes every original matrix, short and tensor coordinate of the source.
The tensor vanishes by the already proved actual triality formula. -/
theorem generatedFeasibleContaining_sixteen_phase_whole_source :
    rhoLocal (inclQ (griessShortQ generatedFeasibleContainingOctadPrototypeLabel))
      generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingOctadDestination := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (localGriessRepresentation
    (localFiberIncl (griessShortQ generatedFeasibleContainingOctadPrototypeLabel)) _) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext
  · change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  · apply Prod.ext
    · ext r
      have hd := localShortOperator_image
        (localFiberIncl (griessShortQ generatedFeasibleContainingOctadPrototypeLabel))
        (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 r
      change localShortOperator _ _ (griessShortPermutation 1 r) = _ at hd
      rw [map_one, Equiv.Perm.one_apply] at hd
      change localShortOperator _ _ r = _
      rw [hd]
      by_cases hr : generatedOctadShortSupport generatedFeasibleContainingOctadPrototypeIndex r
      · rw [generatedFeasibleContaining_sixteen_phase_source_support r hr,
          qSign_zero, one_mul]
      · have hz := not_ne_iff.mp
          (mt (generatedAxis_triality_octad_support_iff
            generatedFeasibleContainingOctadPrototypeIndex 0 0 r).mp hr)
        change (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 r = 0 at hz
        rw [hz, mul_zero]
    · change localTensorRepresentation
        (localFiberIncl (griessShortQ generatedFeasibleContainingOctadPrototypeLabel))
          (griessConwayEncode
        (sExtra (conwayShortAxis
          (Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))) 0))).2.2 =
          (griessConwayEncode (sExtra (conwayShortAxis
            (Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))) 0))).2.2
      rw [generatedAxis_triality_octad_tensor_zero_all, map_zero]

/-- The same genuine original Q element fixes the positive first axis. -/
theorem generatedFeasibleContaining_sixteen_phase_first :
    rhoLocal (inclQ (griessShortQ generatedFeasibleContainingOctadPrototypeLabel))
      (conwayAxis generatedFeasiblePhysicalRootPair) =
        conwayAxis generatedFeasiblePhysicalRootPair := by
  change localFiberIntoH (localFiberIncl
    (griessShortQ generatedFeasibleContainingOctadPrototypeLabel)) ∈
      localAxisStabilizer generatedFeasiblePhysicalRootPair
  rw [localAxisStabilizer_mk_iff]
  constructor
  · change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  · rw [localAxisQPhase_eq_short_phase, prototype_pair_phase,
      generatedFeasiblePhysicalRootPair_coordinates]
    decide +kernel

/-- A faithful actual whole-source phase flip in the entire original positive-first-axis group. -/
def generatedFeasibleContainingSixteenPhaseWord :
    localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  ⟨inclQ (griessShortQ generatedFeasibleContainingOctadPrototypeLabel),
    generatedFeasibleContaining_sixteen_phase_first⟩

/-- Its actual original signed anchor phase is one. -/
theorem generatedFeasibleContainingSixteenPhaseWord_anchor (c : ZMod 2) :
    rhoLocal generatedFeasibleContainingSixteenPhaseWord.val
      (conwayShortAxis generatedFeasibleContainingSixteenShortLabel c) =
        conwayShortAxis generatedFeasibleContainingSixteenShortLabel (1 + c) := by
  have h := generatedAxis_localFiber_image
    (localFiberIncl (griessShortQ generatedFeasibleContainingOctadPrototypeLabel))
      generatedFeasibleContainingSixteenShortLabel c
  have hp : griessShortPermutation
      (localFiberIncl (griessShortQ generatedFeasibleContainingOctadPrototypeLabel)).val.2
        generatedFeasibleContainingSixteenShortLabel =
      generatedFeasibleContainingSixteenShortLabel := by
    change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  rw [hp, localAxisQPhase_eq_short_phase] at h
  have hphase : toAdd (localAxisQPhase generatedFeasibleContainingSixteenShortLabel
      (griessShortQ generatedFeasibleContainingOctadPrototypeLabel)) = 1 := by
    rw [generatedFeasibleContainingSixteenShortLabel, prototype_pair_phase,
      generatedFeasibleContainingSixteenPair_coordinates]
    decide +kernel
  rw [hphase] at h
  exact h

/-- Every genuine signed selected-sixteen perpendicular short axis reaches either specified
phase of the actual original (2,8) anchor under an actual whole-source first-axis fixer. -/
theorem generatedFeasibleContaining_selected_sixteen_signed_transport
    (r : GriessShortIndex) (c d : ZMod 2)
    (hS : generatedFeasibleContainingSelectedShortSquare r = 16)
    (hP : griessShortIntegral r 0 = griessShortIntegral r 1) :
    ∃ u : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      rhoLocal u.val generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingOctadDestination ∧
      rhoLocal u.val (conwayShortAxis r c) =
        conwayShortAxis generatedFeasibleContainingSixteenShortLabel d := by
  obtain ⟨g, hgS, hgP, hgR⟩ :=
    generatedFeasibleContaining_selected_sixteen_spatial_transport r hS hP
  have hgP' : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair) :=
    (leechRootedA2_short_perm_eq_iff _ _ _).mpr (Or.inl hgP)
  obtain ⟨f, hf, hfirst, hsource⟩ :=
    generatedFeasibleContaining_source_flag_whole_lift g hgS hgP'
  let u : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    ⟨localFiberIntoH f, hfirst⟩
  let b := localShortPhase f r + c
  have huR : rhoLocal u.val (conwayShortAxis r c) =
      conwayShortAxis generatedFeasibleContainingSixteenShortLabel b := by
    change localGriessRepresentation f _ = _
    rw [generatedAxis_localFiber_image, hf, hgR]
  by_cases hb : b = d
  · exact ⟨u, hsource, hb ▸ huR⟩
  · have hphase : 1 + b = d := by
      have h : ∀ b d : ZMod 2, b ≠ d → 1 + b = d := by decide +kernel
      exact h b d hb
    refine ⟨generatedFeasibleContainingSixteenPhaseWord * u, ?_, ?_⟩
    · change rhoLocal (generatedFeasibleContainingSixteenPhaseWord.val * u.val) _ = _
      rw [map_mul, LinearEquiv.mul_apply, hsource]
      exact generatedFeasibleContaining_sixteen_phase_whole_source
    · change rhoLocal (generatedFeasibleContainingSixteenPhaseWord.val * u.val) _ = _
      rw [map_mul, LinearEquiv.mul_apply, huR,
        generatedFeasibleContainingSixteenPhaseWord_anchor, hphase]

/-- The original (2,8) anchor is perpendicular to the positive original first root. -/
theorem generatedFeasibleContaining_sixteen_anchor_perpendicular :
    griessShortIntegral generatedFeasibleContainingSixteenShortLabel 0 =
      griessShortIntegral generatedFeasibleContainingSixteenShortLabel 1 := by
  simp [generatedFeasibleContainingSixteenShortLabel, griessShortIntegral,
    generatedFeasibleContainingSixteenPair_coordinates]

/-- The original preferred signed secondary address of the faithful one-quarter anchor. -/
def generatedFeasibleContainingSixteenAnchorAddress : generatedFeasibleOrthogonalSignedShortLabels :=
  ⟨(generatedFeasibleContainingSixteenShortLabel, 0), Finset.mem_product.mpr
    ⟨(generatedFeasibleOrthogonalShortLabels_mem _).mpr generatedFeasibleContaining_sixteen_anchor_perpendicular,
      Finset.mem_univ _⟩⟩

/-- The unique original inverse-secondary coset with this complete specified signed address. -/
def generatedFeasibleContainingSixteenAnchorCoset :
    generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair :=
  generatedFeasibleContainingInverseSecondaryAddresses.symm
    generatedFeasibleContainingSixteenAnchorAddress

/-- A representative in the actual original first-axis group of this fully constrained coset. -/
def generatedFeasibleContainingSixteenAnchorWord :
    localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  Classical.choose (Quotient.mk_surjective generatedFeasibleContainingSixteenAnchorCoset)

/-- The actual word represents exactly the independently specified original inverse coset. -/
theorem generatedFeasibleContainingSixteenAnchorWord_coset :
    Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair))
        generatedFeasibleContainingSixteenAnchorWord =
      generatedFeasibleContainingSixteenAnchorCoset :=
  Classical.choose_spec (Quotient.mk_surjective generatedFeasibleContainingSixteenAnchorCoset)

/-- The entire actual inverse-secondary address, retaining the specified binary phase. -/
theorem generatedFeasibleContainingSixteenAnchorWord_inverse_address :
    generatedFeasibleContainingInverseSecondaryAddresses
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair))
          generatedFeasibleContainingSixteenAnchorWord) =
        generatedFeasibleContainingSixteenAnchorAddress := by
  rw [generatedFeasibleContainingSixteenAnchorWord_coset]
  exact generatedFeasibleContainingInverseSecondaryAddresses.apply_symm_apply _

/-- The actual one-quarter destination axis defined through the faithful original action. -/
def generatedFeasibleContainingSixteenDestination : GriessSpace :=
  sExtra (rhoLocal generatedFeasibleContainingSixteenAnchorWord.val
    generatedFeasibleContainingOctadDestination)

/-- The original anchor word has precisely this actual destination class. -/
theorem generatedFeasibleContainingSixteenAnchorWord_destination :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair))
            generatedFeasibleContainingSixteenAnchorWord) =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination := rfl

/-- Every original selected-sixteen inverse coset address has the same faithful actual
one-quarter destination. The proof uses a genuine full signed source-stabilizer mover. -/
theorem generatedFeasibleContaining_sixteen_word_recognition
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hS : generatedFeasibleContainingSelectedShortSquare
      (generatedFeasibleContainingInverseSecondaryAddresses
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 = 16) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination := by
  let a := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)
  let k := generatedFeasibleContainingSixteenAnchorWord
  let b := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) k)
  have hP : griessShortIntegral a.val.1 0 = griessShortIntegral a.val.1 1 := by
    have hm := a.property
    change a.val ∈ generatedFeasibleOrthogonalShortLabels ×ˢ Finset.univ at hm
    rw [Finset.mem_product] at hm
    exact (generatedFeasibleOrthogonalShortLabels_mem a.val.1).mp hm.1
  obtain ⟨u, huS, huR⟩ := generatedFeasibleContaining_selected_sixteen_signed_transport
    a.val.1 a.val.2 b.val.2 hS hP
  have hb : b.val.1 = generatedFeasibleContainingSixteenShortLabel :=
    congrArg (fun x : generatedFeasibleOrthogonalSignedShortLabels => x.val.1)
      generatedFeasibleContainingSixteenAnchorWord_inverse_address
  have hm : rhoLocal u.val
      (rhoLocal h.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) =
        rhoLocal k.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
    rw [← generatedFeasibleContainingInverseSecondaryAddresses_axis h,
      ← generatedFeasibleContainingInverseSecondaryAddresses_axis k]
    change rhoLocal u.val (conwayShortAxis a.val.1 a.val.2) =
      conwayShortAxis b.val.1 b.val.2
    rw [hb]
    exact huR
  exact (generatedFeasibleContaining_destination_inverse_mover h k u huS hm).trans
    generatedFeasibleContainingSixteenAnchorWord_destination

/-- Every one of the24,192 genuine one-quarter inputs from the complete original containing
transition has the faithful actual one-quarter destination. No class count is assumed. -/
theorem generatedFeasibleContaining_sixteen_input_recognition
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair)
    (hc : c ∈ generatedFeasibleContainingOutgoingCoefficientInputs 2) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination := by
  induction c using Quotient.inductionOn with
  | h h =>
      rw [generatedFeasibleContainingOutgoingCoefficientInputs_word_iff] at hc
      change generatedFeasibleContainingSelectedShortSquare
        (generatedFeasibleContainingInverseSecondaryAddresses
          (Quotient.mk (QuotientGroup.rightRel
            (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 = 16 at hc
      exact generatedFeasibleContaining_sixteen_word_recognition h hc

/-- The actual destination has original first coefficient one quarter. This follows from the
proved nonempty original input fiber and actual recognition, without a class-size premise. -/
theorem generatedFeasibleContainingSixteenDestination_first_coordinate :
    (griessConwayEncode generatedFeasibleContainingSixteenDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = (1 / 4 : ℝ) := by
  have hn : Nat.card (generatedFeasibleContainingOutgoingCoefficientInputs 2) ≠ 0 := by
    rw [generatedFeasibleContainingOutgoingCoefficientInputs_card]
    decide
  obtain ⟨c⟩ := (Nat.card_ne_zero.mp hn).1
  have he := generatedFeasibleContaining_sixteen_input_recognition c.val c.property
  have hh := c.property.2
  change generatedFeasibleContainingAClassFirst
    (generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c.val) = (1 / 4 : ℝ) at hh
  rw [he] at hh
  exact hh

/-- The entire original noncoordinate fiber of this faithful actual destination is exactly the
whole one-quarter input fiber, with all original signed addresses retained. -/
theorem generatedFeasibleContaining_sixteen_noncoordinate_input_iff
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair)
    (hc : c ∈ generatedFeasibleContainingNoncoordinateInputCosets) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c =
        generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination ↔
      c ∈ generatedFeasibleContainingOutgoingCoefficientInputs 2 := by
  constructor
  · intro he
    change c ∈ generatedFeasibleContainingNoncoordinateInputCosets ∧
      generatedFeasibleContainingInputFirst c = (1 / 4 : ℝ)
    refine ⟨hc, ?_⟩
    change generatedFeasibleContainingAClassFirst
      (generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c) = _
    rw [he]
    exact generatedFeasibleContainingSixteenDestination_first_coordinate
  · exact generatedFeasibleContaining_sixteen_input_recognition c

/-- Exactly24,192 original noncoordinate transition cosets reach this actual destination class.
This is an input count, and does not assert the global feasible class size or its stabilizer. -/
theorem generatedFeasibleContaining_sixteen_noncoordinate_class_input_card :
    Nat.card {c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair |
      c ∈ generatedFeasibleContainingNoncoordinateInputCosets ∧
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination} =
      24192 := by
  have he : {c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair |
      c ∈ generatedFeasibleContainingNoncoordinateInputCosets ∧
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination} =
      generatedFeasibleContainingOutgoingCoefficientInputs 2 := by
    ext c
    constructor
    · rintro ⟨hc, hd⟩
      exact (generatedFeasibleContaining_sixteen_noncoordinate_input_iff c hc).mp hd
    · intro hc
      exact ⟨hc.1, generatedFeasibleContaining_sixteen_input_recognition c hc⟩
  rw [he, generatedFeasibleContainingOutgoingCoefficientInputs_card]
  rfl

/-- The actual one-quarter destination is distinct from the actual one-eighth destination under
the entire original first-axis action, by the preserved original first coefficient. -/
theorem generatedFeasibleContaining_sixteen_ne_eighth_class :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination ≠
      generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination := by
  intro he
  have h := congrArg generatedFeasibleContainingAClassFirst he
  change (griessConwayEncode generatedFeasibleContainingSixteenDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
    (griessConwayEncode generatedFeasibleContainingNewDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) at h
  rw [generatedFeasibleContainingSixteenDestination_first_coordinate,
    generatedFeasibleContainingNewDestination_first_coordinate] at h
  norm_num at h

/-- The original prototype source, actual anchor word and triality lie in the genuine global
first-axis stabilizer orbit of the original opposite axis. -/
theorem generatedFeasibleContainingSixteenDestination_feasible :
    generatedFeasibleContainingSixteenDestination ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  let a := conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0
  let b := conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1
  have hclosed (k : generatedVectorStabilizer a) (x : GriessSpace)
      (hx : x ∈ generatedFeasibleVectorOrbit a b) :
      k.val.val x ∈ generatedFeasibleVectorOrbit a b := by
    obtain ⟨h, hh⟩ := hx
    refine ⟨k * h, ?_⟩
    change k.val.val (h.val.val b) = k.val.val x
    change h.val.val b = x at hh
    rw [hh]
  have ht : extraIntoGenerated.val a = a := by
    change sExtra (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0
    rw [conwayShortAxis_pair_zero, conwayAxis_triality]
  let t : generatedVectorStabilizer a := ⟨extraIntoGenerated, ht⟩
  have hs := generatedFeasibleSecondaryNonPair_axis_mem 0
    generatedFeasibleContainingOctadPrototypeLabel
    generatedFeasibleContainingOctadPrototypeLabel_mem 0
  have hbase := generatedFeasibleSecondaryLocalOrbit_subset generatedFeasiblePhysicalRootPair hs
  have hsource := hclosed t _ hbase
  have hw : (localIntoGenerated generatedFeasibleContainingSixteenAnchorWord.val).val a = a := by
    dsimp only [a]
    rw [conwayShortAxis_pair_zero]
    exact generatedFeasibleContainingSixteenAnchorWord.property
  let w : generatedVectorStabilizer a :=
    ⟨localIntoGenerated generatedFeasibleContainingSixteenAnchorWord.val, hw⟩
  have hincoming := hclosed w _ hsource
  exact hclosed t _ hincoming

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
