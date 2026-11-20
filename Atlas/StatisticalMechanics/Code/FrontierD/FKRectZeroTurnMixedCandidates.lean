/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectMedialDualShift
import Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge











open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



noncomputable def fkRectZeroTurnRemainderDualBoundaryCycleWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk
      (fkRectMedialDartPrimalLabel R
        (fkRectMedialDualShiftDart R
          (fkRectZeroTurnRemainderBlackDart R omega C).1))
      (fkRectMedialDartPrimalLabel R
        (fkRectMedialDualShiftDart R
          (fkRectZeroTurnRemainderBlackDart R omega C).1)) := by
  let d := fkRectZeroTurnRemainderBlackDart R omega C
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dualPairing := fkRectConfigurationToMedialPairing R
    (fkRectDualConfigurationEquiv R omega)
  let n := (fkRectBlackOrbitList pairing d).length
  let p := fkRectMedialBoundaryPrimalTrace R
    (fkRectDualConfigurationEquiv R omega)
    (fkRectMedialDualShiftDart R d.1) n
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have horig : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  have hreturn : (fkMedialBoundaryStep dualPairing)^[n]
      (fkRectMedialDualShiftDart R d.1) =
        fkRectMedialDualShiftDart R d.1 := by
    rw [← fkRectMedialDualShiftDart_boundaryStep_iterate R omega d.1 n,
      horig]
  exact p.copy rfl (congrArg (fkRectMedialDartPrimalLabel R) hreturn)


def FKRectWalkAvoidsRowSeam
    (R : FKRectTorus) {eta : R.Configuration} {x : R.Vertex}
    (p : (fkRectOpenGraph R eta).Walk x x) : Prop :=
  ∀ e ∈ p.edges, ¬ fkRectCrossesVerticalSeam R e



theorem fkRectRefinedBoundaryCenterAfter_dualShift
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) (n : Nat) :
    fkRectRefinedBoundaryCenterAfter
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega))
        (fkRectMedialDualShiftDart R d) c n =
      fkRectRefinedBoundaryCenterAfter
        (fkRectConfigurationToMedialPairing R omega) d c n := by
  induction n generalizing d c with
  | zero => rfl
  | succ n ih =>
      simp only [fkRectRefinedBoundaryCenterAfter]
      rw [← fkRectMedialDualShiftDart_boundaryStep]
      have hlocal := fkRectMedialDualShiftDart_localMate R omega d
      have hside := congrArg
        (fun e : FKMedialDart R.medialTorus => e.2) hlocal
      change (fkMedialLocalMate
          (fkRectConfigurationToMedialPairing R omega) d).2 =
        (fkMedialLocalMate
          (fkRectConfigurationToMedialPairing R
            (fkRectDualConfigurationEquiv R omega))
          (fkRectMedialDualShiftDart R d)).2 at hside
      rw [hside]
      exact ih _ _



theorem fkRectMedialBoundaryPrimalSeamTrace_dualShift
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (n : Nat)
    (hclosed : (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega))^[n] d = d) :
    fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega))
        (fkRectMedialDualShiftDart R d) n =
      fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d n := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dualPairing := fkRectConfigurationToMedialPairing R
    (fkRectDualConfigurationEquiv R omega)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let z := fkRectRefinedBoundaryCanonicalCenter R
    (fkRectMedialDualShiftDart R d)
  let u := fkRectMedialBoundaryPrimalSeamTrace R pairing d n
  let v := fkRectMedialBoundaryPrimalSeamTrace R dualPairing
    (fkRectMedialDualShiftDart R d) n
  have hdualClosed : (fkMedialBoundaryStep dualPairing)^[n]
      (fkRectMedialDualShiftDart R d) =
        fkRectMedialDualShiftDart R d := by
    rw [← fkRectMedialDualShiftDart_boundaryStep_iterate R omega d n,
      hclosed]
  have ho := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d (0, 0) n
  have hd := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R dualPairing (fkRectMedialDualShiftDart R d)
      (c.1 - z.1, c.2 - z.2) n
  simp only [Prod.fst, Prod.snd, add_zero] at ho
  change fkRectRefinedBoundaryCenterAfter pairing d c n = _ at ho
  change fkRectRefinedBoundaryCenterAfter dualPairing
      (fkRectMedialDualShiftDart R d)
      (z.1 + (c.1 - z.1), z.2 + (c.2 - z.2)) n = _ at hd
  rw [hclosed] at ho
  rw [hdualClosed] at hd
  have hs := fkRectRefinedBoundaryCenterAfter_dualShift
    R omega d c n
  change fkRectRefinedBoundaryCenterAfter dualPairing
      (fkRectMedialDualShiftDart R d) c n =
    fkRectRefinedBoundaryCenterAfter pairing d c n at hs
  have hc1 : z.1 + (c.1 - z.1) = c.1 := by ring
  have hc2 : z.2 + (c.2 - z.2) = c.2 := by ring
  rw [hc1, hc2] at hd
  have hdeck : fkRectSquareDeckTranslation R v =
      fkRectSquareDeckTranslation R u := by
    apply Prod.ext
    · have ho1 := congrArg Prod.fst ho
      have hd1 := congrArg Prod.fst hd
      have hs1 := congrArg Prod.fst hs
      simp only [Prod.fst, Prod.snd, add_zero, sub_self] at ho1 hd1 hs1
      dsimp [c, z, u, v] at ho1 hd1 hs1 ⊢
      linarith
    · have ho2 := congrArg Prod.snd ho
      have hd2 := congrArg Prod.snd hd
      have hs2 := congrArg Prod.snd hs
      simp only [Prod.fst, Prod.snd, add_zero, sub_self] at ho2 hd2 hs2
      dsimp [c, z, u, v] at ho2 hd2 hs2 ⊢
      linarith
  exact fkRectSquareDeckHom_injective R hdeck



theorem fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectWalkWinding R
        (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C) =
      fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega
          (fkRectZeroTurnRemainderBlackDart R omega C)) := by
  let d := fkRectZeroTurnRemainderBlackDart R omega C
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hclosed : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  unfold fkRectZeroTurnRemainderDualBoundaryCycleWalk
  rw [fkRectWalkWinding_copy,
    fkRectMedialBoundaryPrimalTrace_winding]
  change fkRectMedialBoundaryPrimalSeamTrace R
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega))
      (fkRectMedialDualShiftDart R d.1) n = _
  rw [fkRectMedialBoundaryPrimalSeamTrace_dualShift
    R omega d.1 n hclosed]
  exact (fkRectBlackBoundaryPrimalCycleWalk_winding R omega d).symm


noncomputable def fkRectZeroTurnPrimalTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawPrimalHorizontalCrossingComponent R omega) := by
  classical
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  exact Finset.univ.filter fun X =>
    ∃ x ∈ p.support,
      (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).connectedComponentMk x = X.1

theorem mem_fkRectZeroTurnPrimalTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C ↔
      ∃ x ∈ (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega C)).support,
        (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk x = X.1 := by
  classical
  simp [fkRectZeroTurnPrimalTouchedCrossings]



theorem fkRectZeroTurnPrimalTouchedCrossing_matches
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C) :
    FKRectZeroTurnCrossingMatches R omega C X := by
  obtain ⟨x, hx, hcomponent⟩ :=
    (mem_fkRectZeroTurnPrimalTouchedCrossings R omega C X).1 hX
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  have htorusX : fkRectRawPrimalCrossingTorusComponent R omega X =
      (fkRectOpenGraph R omega).connectedComponentMk x := by
    unfold fkRectRawPrimalCrossingTorusComponent
    rw [← hcomponent]
    exact fkRectRawPrimalCrossingTorusComponent_mk R omega x
  unfold FKRectZeroTurnCrossingMatches
  rw [htorusX,
    fkRectZeroTurnRemainderPrimalComponent_eq_label R omega C]
  apply SimpleGraph.ConnectedComponent.sound
  exact ⟨(p.takeUntil x hx).reverse⟩

theorem fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hXC : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
    (hXD : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega D) :
    fkRectZeroTurnRemainderPrimalComponent R omega C =
      fkRectZeroTurnRemainderPrimalComponent R omega D := by
  have hC := fkRectZeroTurnPrimalTouchedCrossing_matches R omega C X hXC
  have hD := fkRectZeroTurnPrimalTouchedCrossing_matches R omega D X hXD
  exact hC.symm.trans hD


theorem fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (havoid : FKRectWalkAvoidsRowSeam R
      (fkRectBlackBoundaryPrimalCycleWalk R omega
        (fkRectZeroTurnRemainderBlackDart R omega C))) :
    (fkRectZeroTurnPrimalTouchedCrossings R omega C).Nonempty := by
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  obtain ⟨X, hcross, z, hz, hcomponent⟩ :=
    exists_fkRectRawHorizontalCrossingComponent_touched_by_closedWalk
      R omega p havoid
        (fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C)
  refine ⟨⟨X, hcross⟩,
    (mem_fkRectZeroTurnPrimalTouchedCrossings R omega C _).2 ?_⟩
  exact ⟨z, hz, hcomponent⟩


noncomputable def fkRectZeroTurnDualTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawWiredDualHorizontalCrossingComponent R omega) := by
  classical
  let p := fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C
  exact Finset.univ.filter fun X =>
    ∃ x ∈ p.support,
      (fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R omega))).connectedComponentMk x = X.1

theorem mem_fkRectZeroTurnDualTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawWiredDualHorizontalCrossingComponent R omega) :
    X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ↔
      ∃ x ∈ (fkRectZeroTurnRemainderDualBoundaryCycleWalk
        R omega C).support,
        (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R omega))).connectedComponentMk x = X.1 := by
  classical
  simp [fkRectZeroTurnDualTouchedCrossings]



theorem fkRectOpenGraph_dual_le_dual_forceCutClosed
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega) ≤
      fkRectOpenGraph R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R omega)) := by
  apply fkRectOpenGraph_mono R
  intro e he
  rw [fkRectDualConfigurationEquiv_apply] at he ⊢
  by_cases hcut : fkRectDualEdgeToEdge R e ∈ fkRectTorusCutEdges R
  · rw [fkRectForceCutClosed_of_mem R omega _ hcut]
    rfl
  · rwa [fkRectForceCutClosed_of_not_mem R omega _ hcut]


theorem fkRectZeroTurnDualTouchedCrossings_nonempty_of_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hwind : (fkRectWalkWinding R
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C)).1 ≠ 0) :
    (fkRectZeroTurnDualTouchedCrossings R omega C).Nonempty := by
  let p := fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C
  let hle := fkRectOpenGraph_dual_le_dual_forceCutClosed R omega
  let q := p.mapLe hle
  have hqwind : (fkRectWalkWinding R q).1 ≠ 0 := by
    simpa only [q, fkRectWalkWinding_mapLe] using hwind
  obtain ⟨X, hcross, z, hz, hcomponent⟩ :=
    exists_fkRectRawHorizontalCrossingComponent_touched_of_winding
      R _ q hqwind
  refine ⟨⟨X, hcross⟩,
    (mem_fkRectZeroTurnDualTouchedCrossings R omega C _).2 ?_⟩
  refine ⟨z, ?_, hcomponent⟩
  simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using hz



theorem fkRectZeroTurnDualTouchedCrossings_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectZeroTurnDualTouchedCrossings R omega C).Nonempty := by
  apply fkRectZeroTurnDualTouchedCrossings_nonempty_of_winding R omega C
  rw [fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding]
  exact fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C


noncomputable def fkRectZeroTurnPrimalTouchedCrossingsInMixed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega) := by
  classical
  exact (fkRectZeroTurnPrimalTouchedCrossings R omega C).image Sum.inl


noncomputable def fkRectZeroTurnDualTouchedCrossingsInMixed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega) := by
  classical
  exact (fkRectZeroTurnDualTouchedCrossings R omega C).image Sum.inr



noncomputable def fkRectZeroTurnMixedTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega) := by
  classical
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  if FKRectWalkAvoidsRowSeam R p then
    exact fkRectZeroTurnPrimalTouchedCrossingsInMixed R omega C
  else
    exact fkRectZeroTurnDualTouchedCrossingsInMixed R omega C


def FKRectZeroTurnUsesPrimalTouchedCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) : Prop :=
  FKRectWalkAvoidsRowSeam R
    (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C))

theorem fkRectZeroTurnMixedTouchedCrossings_eq_primal
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    fkRectZeroTurnMixedTouchedCrossings R omega C =
      fkRectZeroTurnPrimalTouchedCrossingsInMixed R omega C := by
  classical
  unfold FKRectZeroTurnUsesPrimalTouchedCrossings at hC
  unfold fkRectZeroTurnMixedTouchedCrossings
  dsimp only
  rw [dif_pos hC]

theorem fkRectZeroTurnMixedTouchedCrossings_eq_dual
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    fkRectZeroTurnMixedTouchedCrossings R omega C =
      fkRectZeroTurnDualTouchedCrossingsInMixed R omega C := by
  classical
  unfold FKRectZeroTurnUsesPrimalTouchedCrossings at hC
  unfold fkRectZeroTurnMixedTouchedCrossings
  dsimp only
  rw [dif_neg hC]

theorem mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Sum.inl X ∈ fkRectZeroTurnMixedTouchedCrossings R omega C ↔
      FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ∧
        X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C := by
  classical
  by_cases hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C
  · rw [fkRectZeroTurnMixedTouchedCrossings_eq_primal R omega C hC]
    simp [fkRectZeroTurnPrimalTouchedCrossingsInMixed, hC]
  · rw [fkRectZeroTurnMixedTouchedCrossings_eq_dual R omega C hC]
    simp [fkRectZeroTurnDualTouchedCrossingsInMixed, hC]

theorem mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawWiredDualHorizontalCrossingComponent R omega) :
    Sum.inr X ∈ fkRectZeroTurnMixedTouchedCrossings R omega C ↔
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ∧
        X ∈ fkRectZeroTurnDualTouchedCrossings R omega C := by
  classical
  by_cases hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C
  · rw [fkRectZeroTurnMixedTouchedCrossings_eq_primal R omega C hC]
    simp [fkRectZeroTurnPrimalTouchedCrossingsInMixed, hC]
  · rw [fkRectZeroTurnMixedTouchedCrossings_eq_dual R omega C hC]
    simp [fkRectZeroTurnDualTouchedCrossingsInMixed, hC]


theorem fkRectZeroTurnMixedTouchedCrossings_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectZeroTurnMixedTouchedCrossings R omega C).Nonempty := by
  classical
  let p := fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)
  change (if h : FKRectWalkAvoidsRowSeam R p then
      fkRectZeroTurnPrimalTouchedCrossingsInMixed R omega C
    else
      fkRectZeroTurnDualTouchedCrossingsInMixed R omega C).Nonempty
  split
  · obtain ⟨X, hX⟩ :=
      fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam
        R omega C (by assumption)
    exact ⟨Sum.inl X, by
      simp [fkRectZeroTurnPrimalTouchedCrossingsInMixed, hX]⟩
  · obtain ⟨X, hX⟩ :=
      fkRectZeroTurnDualTouchedCrossings_nonempty R omega C
    exact ⟨Sum.inr X, by
      simp [fkRectZeroTurnDualTouchedCrossingsInMixed, hX]⟩




structure FKRectZeroTurnMixedTouchedCertificate
    (R : FKRectTorus) (omega : R.Configuration) where
  nonempty : ∀ C, (fkRectZeroTurnMixedTouchedCrossings R omega C).Nonempty
  sameSide_unique : ∀ C D X,
    X ∈ fkRectZeroTurnMixedTouchedCrossings R omega C →
    X ∈ fkRectZeroTurnMixedTouchedCrossings R omega D →
    fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D → C = D



noncomputable def FKRectZeroTurnMixedTouchedCertificate.ofBranchUniqueness
    (R : FKRectTorus) (omega : R.Configuration)
    (hprimal : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      fkRectZeroTurnRemainderPrimalComponent R omega C =
          fkRectZeroTurnRemainderPrimalComponent R omega D →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D)
    (hdual : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      ∀ X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
        X ∈ fkRectZeroTurnDualTouchedCrossings R omega C →
        X ∈ fkRectZeroTurnDualTouchedCrossings R omega D →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnMixedTouchedCertificate R omega where
  nonempty := fkRectZeroTurnMixedTouchedCrossings_nonempty R omega
  sameSide_unique := by
    intro C D X hXC hXD hside
    cases X with
    | inl X =>
        have hC :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff R omega C X).1 hXC
        have hD :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff R omega D X).1 hXD
        exact hprimal C D
          (fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing
            R omega C D X hC.2 hD.2) hside
    | inr X =>
        have hC :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff R omega C X).1 hXC
        have hD :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff R omega D X).1 hXD
        exact hdual C D X hC.2 hD.2 hside


noncomputable def fkRectZeroTurnSelectedMixedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (certificate : FKRectZeroTurnMixedTouchedCertificate R omega)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega :=
  (certificate.nonempty C).choose

theorem fkRectZeroTurnSelectedMixedCrossing_mem
    (R : FKRectTorus) (omega : R.Configuration)
    (certificate : FKRectZeroTurnMixedTouchedCertificate R omega)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnSelectedMixedCrossing R omega certificate C ∈
      fkRectZeroTurnMixedTouchedCrossings R omega C :=
  (certificate.nonempty C).choose_spec

set_option maxHeartbeats 800000 in


noncomputable def FKRectZeroTurnMixedTouchedCertificate.toCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (certificate : FKRectZeroTurnMixedTouchedCertificate R omega) :
    FKRectZeroTurnMixedAnnulusCharge R omega :=
  FKRectZeroTurnMixedAnnulusCharge.ofCrossing R omega
    (fkRectZeroTurnSelectedMixedCrossing R omega certificate) (by
      intro C D hcross hside
      exact certificate.sameSide_unique C D
        (fkRectZeroTurnSelectedMixedCrossing R omega certificate C)
        (fkRectZeroTurnSelectedMixedCrossing_mem R omega certificate C)
        (hcross ▸
          fkRectZeroTurnSelectedMixedCrossing_mem R omega certificate D)
        hside)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_touched
    (R : FKRectTorus) (omega : R.Configuration)
    (certificate : FKRectZeroTurnMixedTouchedCertificate R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
    R omega (certificate.toCharge R omega)

end

end StatMech.FrontierD
