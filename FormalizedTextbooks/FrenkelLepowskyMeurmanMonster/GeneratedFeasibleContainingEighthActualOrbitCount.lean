/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthFlagRecognition

/-! Exact entire A stabilizer and A orbit of the actual one-eighth feasible destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The entire actual explicit incoming word has mate coefficient zero. -/
theorem generatedFeasibleEighthExplicitIncoming_mate_zero :
    (griessConwayEncode generatedFeasibleEighthExplicitIncoming).2.1
      generatedFeasibleMateLabel = 0 := by
  exact generatedFeasibleEighthExplicitIncoming_pair_zero 1
    generatedFeasiblePhysicalRootPair (by decide)

/-- The complete explicit outgoing word has the original first coefficient one eighth. -/
theorem generatedFeasibleEighthExplicitDestination_first_coordinate :
    (griessConwayEncode generatedFeasibleEighthExplicitDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 / 8 := by
  rw [generatedFeasibleEighthExplicitDestination,
    generatedFeasibleContaining_triality_first_coordinate,
    generatedFeasibleEighthExplicitIncoming_matrix,
    generatedFeasibleContaining_first_coordinate _
      generatedFeasibleEighthExplicitIncoming_orbit,
    generatedFeasibleEighthExplicitIncoming_mate_zero]
  norm_num [generatedFeasibleEighthExplicitProjectionNumerator]

/-- The complete explicit outgoing word has the original preferred mate coefficient seven eighths.
-/
theorem generatedFeasibleEighthExplicitDestination_mate_coordinate :
    (griessConwayEncode generatedFeasibleEighthExplicitDestination).2.1
      generatedFeasibleMateLabel = 7 / 8 := by
  have h := generatedFeasibleContaining_triality_pair_coordinate_sum
    generatedFeasibleEighthExplicitIncoming
  change (griessConwayEncode generatedFeasibleEighthExplicitDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) +
    (griessConwayEncode generatedFeasibleEighthExplicitDestination).2.1
      generatedFeasibleMateLabel = _ at h
  rw [generatedFeasibleEighthExplicitDestination_first_coordinate,
    generatedFeasibleContaining_first_coordinate _
      generatedFeasibleEighthExplicitIncoming_orbit,
    generatedFeasibleEighthExplicitIncoming_mate_zero] at h
  linarith

/-- The explicit source is transported to the independently defined original destination by a
whole genuine simultaneous word. No identification by scalar invariants is used. -/
theorem generatedFeasibleEighthExplicitDestination_actual_N_transport :
    ∃ n : GeneratedFeasibleContainingN,
      rhoLocal n.val generatedFeasibleContainingNewDestination =
        generatedFeasibleEighthExplicitDestination := by
  let h : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    ⟨localFiberIntoH generatedFeasibleEighthExplicitLocalWord,
      generatedFeasibleEighthExplicitLocalWord_first⟩
  have hc : Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h ∈
      generatedFeasibleContainingOutgoingCoefficientInputs 1 := by
    refine ⟨(generatedFeasibleContaining_noncoordinate_input_word_iff h).mpr
      ⟨generatedFeasibleEighthExplicitIncoming_orbit,
        generatedFeasibleEighthExplicitIncoming_mate_zero⟩, ?_⟩
    exact generatedFeasibleEighthExplicitDestination_first_coordinate
  obtain ⟨m, hm⟩ := generatedFeasibleContaining_eighth_input_incoming_orbit h hc
  obtain ⟨n, hn⟩ := generatedFeasibleContaining_N_triality_word m
  refine ⟨n, ?_⟩
  change rhoLocal n.val (sExtra generatedFeasibleContainingNewIncoming) =
      sExtra generatedFeasibleEighthExplicitIncoming
  change rhoLocal m.val generatedFeasibleContainingNewIncoming =
    generatedFeasibleEighthExplicitIncoming at hm
  rw [hn, hm]

/-- Every actual whole explicit destination fixer preserving the first axis fixes Omega.
The original matrix recognizes the mate line, and its nonzero coefficient fixes the mate phase. -/
theorem generatedFeasibleEighthExplicitDestination_fixer_Omega (h : H)
    (hfirst : h ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hfix : rhoLocal h generatedFeasibleEighthExplicitDestination =
      generatedFeasibleEighthExplicitDestination) : h ∈ localOmegaStabilizer := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hmatrix := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hfix
  rw [← hf] at hmatrix
  change (griessConwayEncode (localGriessRepresentation f
    generatedFeasibleEighthExplicitDestination)).1 = _ at hmatrix
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply,
    generatedFeasibleEighthExplicitDestination_matrix_flag] at hmatrix
  have hflag := (generatedAxisE8ShortFlagMatrix_stabilizer_iff
    generatedFeasibleEighthFlagOctad generatedFeasibleMateLabel
    generatedFeasibleEighthFlagOctad_mate_incident f.val.2).mp hmatrix
  have hp := ((generatedAxisE8ShortFlagStabilizer_mem _ _ _).mp hflag).2
  have hcoordinate := congrArg (fun x : GriessSpace =>
    (griessConwayEncode x).2.1 generatedFeasibleMateLabel) hfix
  rw [← hf] at hcoordinate
  change (griessConwayEncode (localGriessRepresentation f
    generatedFeasibleEighthExplicitDestination)).2.1 _ = _ at hcoordinate
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at hcoordinate
  have hi := localShortOperator_image f
    (griessConwayEncode generatedFeasibleEighthExplicitDestination).2.1
      generatedFeasibleMateLabel
  rw [hp] at hi
  change localShortOperator f
    (griessConwayEncode generatedFeasibleEighthExplicitDestination).2.1
      generatedFeasibleMateLabel =
        (griessConwayEncode generatedFeasibleEighthExplicitDestination).2.1
          generatedFeasibleMateLabel at hcoordinate
  rw [hi, generatedFeasibleEighthExplicitDestination_mate_coordinate] at hcoordinate
  have hphase : localShortPhase f generatedFeasibleMateLabel = 0 := by
    apply (qSign_eq_one_iff _).mp
    linarith
  have hsecondary : rhoLocal h (generatedFeasibleSecondaryAxis
      generatedFeasiblePhysicalRootPair) = generatedFeasibleSecondaryAxis
        generatedFeasiblePhysicalRootPair := by
    rw [← hf, generatedFeasibleSecondaryAxis_eq_short]
    change localGriessRepresentation f _ = _
    rw [generatedAxis_localFiber_image]
    change conwayShortAxis (griessShortPermutation f.val.2 generatedFeasibleMateLabel)
      (localShortPhase f generatedFeasibleMateLabel + 1) =
        conwayShortAxis generatedFeasibleMateLabel 1
    rw [hp, hphase, zero_add]
  have hn : (⟨h, hfirst⟩ : localAxisStabilizer generatedFeasiblePhysicalRootPair) ∈
      localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair := by
    rw [← generatedFeasibleSecondaryAxis_stabilizer]
    exact hsecondary
  exact hn

/-- Every actual whole fixer of the original independently defined sixth destination is
simultaneous: this is transferred by a certified whole N transport, not assumed. -/
theorem generatedFeasibleContainingEighthAStabilizer_fixes_Omega
    (g : generatedFeasibleContainingEighthAStabilizer) : g.val.val ∈ localOmegaStabilizer := by
  obtain ⟨n, hn⟩ := generatedFeasibleEighthExplicitDestination_actual_N_transport
  let k := n.val * g.val.val * n.val⁻¹
  have hkfirst : k ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    (localAxisStabilizer _).mul_mem
      ((localAxisStabilizer _).mul_mem n.property.1 g.val.property)
      ((localAxisStabilizer _).inv_mem n.property.1)
  have hkfix : rhoLocal k generatedFeasibleEighthExplicitDestination =
      generatedFeasibleEighthExplicitDestination :=
    generatedFeasibleContaining_conjugate_fixes n.val g.val.val _ _ hn g.property
  have hk := generatedFeasibleEighthExplicitDestination_fixer_Omega k hkfirst hkfix
  have he : g.val.val = n.val⁻¹ * k * n.val := by dsimp only [k]; group
  rw [he]
  exact localOmegaStabilizer.mul_mem
    (localOmegaStabilizer.mul_mem (localOmegaStabilizer.inv_mem n.property.2) hk) n.property.2

/-- Exactly 470,060,236,800 original vectors form the genuine sixth feasible A orbit. -/
theorem generatedFeasibleContainingEighth_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingNewDestination) = 470060236800 :=
  generatedFeasibleContainingEighth_actual_A_orbit_card_iff.mpr
    generatedFeasibleContainingEighthAStabilizer_fixes_Omega

/-- The entire actual sixth feasible A stabilizer has exactly 1,509,949,440 elements. -/
theorem generatedFeasibleContainingEighthAStabilizer_card :
    Nat.card generatedFeasibleContainingEighthAStabilizer = 1509949440 := by
  have h := generatedFeasibleContainingEighthAStabilizer.card_mul_index
  rw [generatedFeasibleContainingEighthAStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq, generatedFeasibleContainingEighth_actual_A_orbit_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 470060236800)
  exact h.trans (by decide)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
