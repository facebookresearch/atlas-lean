/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingFrameProjectionQuantization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightReduction

/-! An original Golay frame producing a genuinely new containing transition destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original code label 2306 has exactly two points in the original containing octad. -/
def generatedFeasibleContainingNewFrameCoordinates : Fin 24 → ℤ :=
  ![6, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0, 0, 2, 0, 2]

/-- The complete source congruences bind this frame to the original integral Leech lattice. -/
theorem generatedFeasibleContainingNewFrame_mem :
    generatedFeasibleContainingNewFrameCoordinates ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, golayEncoder (golayLabelCoefficients 2306), ⟨_, rfl⟩, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

/-- The genuine integral vector, with its original source membership proof. -/
def generatedFeasibleContainingNewFrame : leechIntegral :=
  ⟨generatedFeasibleContainingNewFrameCoordinates, generatedFeasibleContainingNewFrame_mem⟩

/-- All twenty-four original coordinates give physical norm eight. -/
theorem generatedFeasibleContainingNewFrame_norm :
    leechSquareSum generatedFeasibleContainingNewFrame.val = 64 := by
  decide +kernel

/-- The original preferred minus root pairs with the actual frame by thirty-two. -/
theorem generatedFeasibleContainingNewFrame_pairing :
    (∑ i : Fin 24, generatedFeasibleContainingNewFrame.val i *
      (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))).val i) =
        32 := by
  simp only [griessShortLatticeVector, griessShortIntegral,
    generatedFeasiblePhysicalRootPair_coordinates]
  decide +kernel

/-- Its actual squared projection into the original containing octad is forty. -/
theorem generatedFeasibleContainingNewFrame_selected :
    generatedFeasibleContainingSelectedSquare
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
      generatedFeasibleContainingNewFrame.val = 40 := by
  have hw : golayOctadWord generatedFeasibleContainingOctadPrototypeIndex =
      golayEncoder (golayLabelCoefficients 2063) := by
    unfold golayOctadWord
    rw [generatedFeasibleContainingOctadPrototypeIndex_label]
  rw [hw]
  decide +kernel

/-- A genuine nonzero frame coordinate lies outside the original source section. -/
theorem generatedFeasibleContainingNewFrame_not_supported :
    ¬ generatedStandardOctadSupported generatedFeasibleContainingNewFrame.val := by
  intro h
  have hh := h 12 (by decide)
  norm_num [generatedFeasibleContainingNewFrame, generatedFeasibleContainingNewFrameCoordinates]
    at hh

private theorem short_four_at_zero (r : GriessShortIndex)
    (hr : (griessShortIntegral r 0).natAbs = 4) :
    ∃ s : Fin 2, ∃ p : Fin 276,
      r = Sum.inl (s, p) ∧ (griessCoordinatePair p).1 = 0 := by
  rcases r with ⟨s, p⟩ | (⟨o, a⟩ | ⟨d, j⟩)
  · refine ⟨s, p, rfl, ?_⟩
    have hp := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
    change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hp
    have hn : (griessCoordinatePair p).2 ≠ 0 := by
      intro h
      rw [h] at hp
      exact (Fin.not_lt_zero _) hp
    by_contra h
    simp [griessShortIntegral, Ne.symm h, Ne.symm hn] at hr
  · simp only [griessShortIntegral] at hr
    split_ifs at hr <;> norm_num at hr
  · simp only [griessShortIntegral] at hr
    split_ifs at hr <;> norm_num at hr

private theorem pair_frame_monomial (s : Fin 2) (p : Fin 276)
    (hp : (griessCoordinatePair p).1 = 0) :
    ∃ m : leechIsomSubgroup,
      griessShortPermutation m (Sum.inl (s, p)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) ∧
      leechIntegralAction m (leechCoordinateFrameLattice 0) =
        leechCoordinateFrameLattice 0 := by
  let j := (griessCoordinatePair p).2
  have hj : j ≠ 0 := by
    have h := griessCoordinatePair_ne p
    rw [hp] at h
    exact h.symm
  let a : Fin 2 → Fin 24 := ![0, j]
  have ha : Function.Injective a := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [a]
  obtain ⟨a', ha', haa⟩ := leechShort_extend_tuple (by decide : 2 < 24) a ha
  obtain ⟨q, hq⟩ := leechRootedA2_three_transitive a'
    (fun k : Fin 3 => Fin.castAdd 21 k) ha' (by
      intro x y h
      exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h))
  have ha0 : a' 0 = 0 := haa 0
  have ha1 : a' 1 = j := haa 1
  have hq0 : q.val 0 = 0 := by
    have h := (hq 0).trans (show Fin.castAdd 21 (0 : Fin 3) = 0 from by decide)
    simpa only [ha0] using h
  have hqj : q.val j = 1 := by
    have h := (hq 1).trans (show Fin.castAdd 21 (1 : Fin 3) = 1 from by decide)
    simpa only [ha1] using h
  let b : Fin 2 → Fin 24 := fun k => Fin.castAdd 22 k
  have hb : Function.Injective b := by
    intro x y h
    exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)
  obtain ⟨d, hd⟩ := golayCoordinateProjection_surjective (by decide : 2 < 8) b hb
    ![0, if s = 0 then (0 : ZMod 2) else 1]
  have hd0 : d.val 0 = 0 := congrFun hd 0
  have hd1 : d.val 1 = if s = 0 then 0 else 1 := congrFun hd 1
  let m := golaySignIsometry d * golayPermutationIsometry q
  refine ⟨m, ?_, ?_⟩
  · apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
    left
    apply Subtype.ext
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    funext i
    have h0 : q.val.symm i = 0 ↔ i = 0 := by rw [q.val.symm_apply_eq, hq0]
    have h1 : q.val.symm i = j ↔ i = 1 := by rw [q.val.symm_apply_eq, hqj]
    simp only [golayIntegerSign, golayIntegerPermute, griessShortLatticeVector,
      griessShortIntegral, hp, generatedFeasiblePhysicalRootPair_coordinates,
      show (griessCoordinatePair p).2 = j from rfl, h0, h1]
    by_cases hi0 : i = 0
    · subst i
      simp [hd0]
    · by_cases hi1 : i = 1
      · subst i
        by_cases hs : s = 0 <;> simp [hd1, hs]
      · simp [hi0, hi1]
  · apply Subtype.ext
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    funext i
    have h0 : q.val.symm i = 0 ↔ i = 0 := by rw [q.val.symm_apply_eq, hq0]
    have hi0 : q.val.symm 0 = 0 := by rw [q.val.symm_apply_eq]; exact hq0.symm
    by_cases hi : i = 0 <;>
      simp [golayIntegerSign, golayIntegerPermute, leechCoordinateFrameLattice,
        leechCoordinateFrameVector, h0, hi, hi0, hd0]

/-- The original generators transport this genuine frame while preserving the original root.
-/
theorem generatedFeasibleContainingNewFrame_transport :
    ∃ g : leechIsomSubgroup,
      griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) ∧
      leechIntegralAction g generatedFeasibleContainingNewFrame =
        leechCoordinateFrameLattice 0 := by
  obtain ⟨e, _, he⟩ := leechNormEight_concrete_transitive
    generatedFeasibleContainingNewFrame generatedFeasibleContainingNewFrame_norm
  have hframe : leechIntegralAction e generatedFeasibleContainingNewFrame =
      leechCoordinateFrameLattice 0 := Subtype.ext he
  let r : GriessShortIndex := Sum.inl (0, generatedFeasiblePhysicalRootPair)
  have hpair := generatedFeasibleContaining_integral_action_pairing e
    generatedFeasibleContainingNewFrame (griessShortLatticeVector r)
  rw [hframe, generatedFeasibleContainingNewFrame_pairing] at hpair
  have h0 : (leechIntegralAction e (griessShortLatticeVector r)).val 0 = 4 := by
    simp only [leechCoordinateFrameLattice, leechCoordinateFrameVector, Pi.single_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hpair
    linarith
  have hr : (griessShortIntegral (griessShortPermutation e r) 0).natAbs = 4 := by
    rcases generatedE8Short_integral_sign e r with hp | hn
    · rw [hp] at h0
      change griessShortIntegral (griessShortPermutation e r) 0 = 4 at h0
      rw [h0]
      rfl
    · rw [hn] at h0
      change -griessShortIntegral (griessShortPermutation e r) 0 = 4 at h0
      have hh : griessShortIntegral (griessShortPermutation e r) 0 = -4 := by omega
      rw [hh]
      rfl
  obtain ⟨s, p, hp, hp0⟩ := short_four_at_zero (griessShortPermutation e r) hr
  obtain ⟨m, hm, hmf⟩ := pair_frame_monomial s p hp0
  refine ⟨m * e, ?_, ?_⟩
  · rw [map_mul]
    change griessShortPermutation m (griessShortPermutation e r) = r
    rw [hp]
    exact hm
  · rw [map_mul, LinearEquiv.mul_apply, hframe, hmf]

/-- A fixed original spatial word sending the certified frame to the original coordinate frame.
-/
def generatedFeasibleContainingNewSpatialWord : leechIsomSubgroup :=
  Classical.choose generatedFeasibleContainingNewFrame_transport

theorem generatedFeasibleContainingNewSpatialWord_first :
    griessShortPermutation generatedFeasibleContainingNewSpatialWord
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) :=
  (Classical.choose_spec generatedFeasibleContainingNewFrame_transport).1

theorem generatedFeasibleContainingNewSpatialWord_frame :
    leechIntegralAction generatedFeasibleContainingNewSpatialWord
      generatedFeasibleContainingNewFrame = leechCoordinateFrameLattice 0 :=
  (Classical.choose_spec generatedFeasibleContainingNewFrame_transport).2

private theorem spatial_first_lift (g : leechIsomSubgroup)
    (hg : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair)) :
    ∃ f : localFiberSubgroup, f.val.2 = g ∧
      localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair := by
  let a := qBinaryIsometryLift (leechBinaryAction g) (leechBinaryAction_squareQuad g)
  obtain ⟨s, hs⟩ := exists_spinHolomorph_lift a
    (qBinaryIsometryLift_central (leechBinaryAction g) (leechBinaryAction_squareQuad g))
  have hf : (s, g) ∈ localFiberSubgroup := by
    change qBinaryAction (spinConjugation s) = leechBinaryAction g
    rw [hs]
    exact qBinaryAction_isometryLift (leechBinaryAction g) (leechBinaryAction_squareQuad g)
  let f : localFiberSubgroup := ⟨(s, g), hf⟩
  obtain ⟨q, hq⟩ := localAxisQPhase_surjective
    (Sum.inl (0, generatedFeasiblePhysicalRootPair))
    (ofAdd (localShortPhase f (Sum.inl (0, generatedFeasiblePhysicalRootPair))))
  let f' := localFiberIncl q * f
  have hp : f'.val.2 = g := by change 1 * g = g; exact one_mul g
  refine ⟨f', hp, (localAxisStabilizer_mk_iff _ _).mpr ⟨?_, ?_⟩⟩
  · rw [hp]
    exact hg
  · rw [localShortPhase_mul]
    rw [show f.val.2 = g from rfl, hg, localAxisQPhase_eq_short_phase, hq]
    exact ZModModule.add_self _

/-- An actual full fiber word lifts the spatial transporter and corrects the genuine first phase.
-/
theorem generatedFeasibleContainingNewLift_exists :
    ∃ f : localFiberSubgroup, f.val.2 = generatedFeasibleContainingNewSpatialWord ∧
      localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  spatial_first_lift _ generatedFeasibleContainingNewSpatialWord_first

/-- The genuine whole-axis word; its phase is part of the original fiber product. -/
def generatedFeasibleContainingNewLocalWord : localFiberSubgroup :=
  Classical.choose generatedFeasibleContainingNewLift_exists

theorem generatedFeasibleContainingNewLocalWord_spatial :
    generatedFeasibleContainingNewLocalWord.val.2 = generatedFeasibleContainingNewSpatialWord :=
  (Classical.choose_spec generatedFeasibleContainingNewLift_exists).1

theorem generatedFeasibleContainingNewLocalWord_first_fixed :
    localFiberIntoH generatedFeasibleContainingNewLocalWord ∈
      localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  (Classical.choose_spec generatedFeasibleContainingNewLift_exists).2

/-- The actual incoming vector in the entire original containing orbit. -/
def generatedFeasibleContainingNewIncoming : GriessSpace :=
  localGriessRepresentation generatedFeasibleContainingNewLocalWord
    generatedFeasibleContainingOctadDestination

theorem generatedFeasibleContainingNewIncoming_orbit :
    generatedFeasibleContainingNewIncoming ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination :=
  ⟨⟨localFiberIntoH generatedFeasibleContainingNewLocalWord,
    generatedFeasibleContainingNewLocalWord_first_fixed⟩, rfl⟩

private theorem actual_frame_not_supported :
    ¬ generatedOctadSupported (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
      generatedFeasibleContainingNewFrame.val := by
  have hw : golayOctadWord generatedFeasibleContainingOctadPrototypeIndex =
      golayEncoder (golayLabelCoefficients 2063) := by
    unfold golayOctadWord
    rw [generatedFeasibleContainingOctadPrototypeIndex_label]
  intro h
  have hc : golayOctadWord generatedFeasibleContainingOctadPrototypeIndex 12 = 0 := by
    rw [hw]
    decide +kernel
  have hh := h 12 hc
  norm_num [generatedFeasibleContainingNewFrame, generatedFeasibleContainingNewFrameCoordinates]
    at hh

/-- The actual source mate is absent, since otherwise both roots would put the frame in its section.
-/
theorem generatedFeasibleContainingNewIncoming_mate_zero :
    (griessConwayEncode generatedFeasibleContainingNewIncoming).2.1
      generatedFeasibleMateLabel = 0 := by
  by_contra hm
  let f := generatedFeasibleContainingNewLocalWord
  let S := generatedAxisE8ImageSection f.val.2
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
  have hfirst : griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∈
      S := by
    apply (generatedFeasibleContaining_source_image_short_support f _).mp
    change (griessConwayEncode generatedFeasibleContainingNewIncoming).2.1 _ ≠ 0
    rw [generatedFeasibleContaining_first_coordinate _ generatedFeasibleContainingNewIncoming_orbit]
    norm_num
  have hmate : griessShortLatticeVector generatedFeasibleMateLabel ∈ S :=
    (generatedFeasibleContaining_source_image_short_support f _).mp hm
  have hframe := S.add_mem hfirst hmate
  change griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) +
    griessShortLatticeVector (Sum.inl (1, generatedFeasiblePhysicalRootPair)) ∈ S at hframe
  rw [generatedFeasibleContaining_pair_frame,
    generatedFeasiblePhysicalRootPair_coordinates] at hframe
  change leechCoordinateFrameLattice 0 ∈ S at hframe
  obtain ⟨v, hv, hvg⟩ := (generatedAxisE8ImageSection_mem _ _ _).mp hframe
  have hfg : leechIntegralAction f.val.2 generatedFeasibleContainingNewFrame =
      leechCoordinateFrameLattice 0 := by
    rw [generatedFeasibleContainingNewLocalWord_spatial]
    exact generatedFeasibleContainingNewSpatialWord_frame
  have he : v = generatedFeasibleContainingNewFrame :=
    (leechIntegralAction f.val.2).injective (hvg.trans hfg.symm)
  rw [he] at hv
  exact actual_frame_not_supported hv

/-- This is an actual vector in the complete original mate-zero remainder. -/
theorem generatedFeasibleContainingNewIncoming_noncoordinate :
    generatedFeasibleContainingNewIncoming ∈ generatedFeasibleContainingNoncoordinateAxes :=
  ⟨generatedFeasibleContainingNewIncoming_orbit, generatedFeasibleContainingNewIncoming_mate_zero⟩

/-- The genuine spatial matrix has first diagonal entry five eighths. -/
theorem generatedFeasibleContainingNewIncoming_diagonal :
    (griessConwayEncode generatedFeasibleContainingNewIncoming).1 0 0 = 5 / 8 := by
  let g := generatedFeasibleContainingNewSpatialWord
  have hu : generatedFeasibleContainingPullbackFrame g =
      generatedFeasibleContainingNewFrame :=
    (leechIntegralAction g).injective
      ((generatedFeasibleContainingPullbackFrame_image g).trans
        generatedFeasibleContainingNewSpatialWord_frame.symm)
  have h := generatedFeasibleContaining_projection_frame_diagonal g
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)
  rw [hu, generatedFeasibleContainingNewFrame_selected] at h
  have hm := generatedFeasibleContaining_full_fiber_matrix generatedFeasibleContainingNewLocalWord
  rw [generatedFeasibleContainingNewLocalWord_spatial] at hm
  change (griessConwayEncode generatedFeasibleContainingNewIncoming).1 = _ at hm
  rw [hm]
  norm_num at h ⊢
  linarith

/-- Apply the original triality to the genuine whole-axis incoming vector. -/
def generatedFeasibleContainingNewDestination : GriessSpace :=
  griessTriality generatedFeasibleContainingNewIncoming

/-- The actual outgoing original first coefficient is one eighth. -/
theorem generatedFeasibleContainingNewDestination_first_coordinate :
    (griessConwayEncode generatedFeasibleContainingNewDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 / 8 := by
  have hr := generatedFeasibleContaining_first_diagonal_relation
    _ generatedFeasibleContainingNewIncoming_orbit
  rw [generatedFeasibleContainingNewIncoming_diagonal] at hr
  have ht := generatedFeasibleContaining_noncoordinate_triality_first
    _ generatedFeasibleContainingNewIncoming_noncoordinate
  change (griessConwayEncode generatedFeasibleContainingNewDestination).2.1 _ = _ at ht
  rw [ht]
  linarith

private theorem feasible_word (k : G)
    (hk : k.val (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
    (x : GriessSpace)
    (hx : x ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1)) :
    k.val x ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  obtain ⟨a, ha⟩ := hx
  have hfix := a.property
  change a.val.val (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
    conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 at hfix
  refine ⟨⟨k * a.val, ?_⟩, ?_⟩
  · change k.val (a.val.val _) = _
    rw [hfix, hk]
  · change k.val (a.val.val _) = k.val x
    change a.val.val _ = x at ha
    rw [ha]

/-- The original source, entire local lift and final triality all lie in the genuine global
first stabilizer orbit of the original opposite axis. -/
theorem generatedFeasibleContainingNewDestination_feasible :
    generatedFeasibleContainingNewDestination ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  have hs := generatedFeasibleSecondaryNonPair_axis_mem 0
    generatedFeasibleContainingOctadPrototypeLabel
    generatedFeasibleContainingOctadPrototypeLabel_mem 0
  have hbase := generatedFeasibleSecondaryLocalOrbit_subset generatedFeasiblePhysicalRootPair hs
  have ht : extraIntoGenerated.val
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    change sExtra (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) = _
    rw [conwayShortAxis_pair_zero, conwayAxis_triality]
  have hsource := feasible_word extraIntoGenerated ht _ hbase
  have hlocal : (localIntoGenerated (localFiberIntoH generatedFeasibleContainingNewLocalWord)).val
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    rw [conwayShortAxis_pair_zero]
    exact generatedFeasibleContainingNewLocalWord_first_fixed
  have hincoming := feasible_word
    (localIntoGenerated (localFiberIntoH generatedFeasibleContainingNewLocalWord))
    hlocal _ hsource
  exact feasible_word extraIntoGenerated ht _ hincoming

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
