/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnCutInjection











namespace StatMech.FrontierD

noncomputable section



abbrev FKRectZeroTurnCutRemainderComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  {C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega) //
    C ∈ fkRectZeroTurnCutRemainderComponents R omega}


abbrev FKRectRawPrimalHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  {C : (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).ConnectedComponent //
    FKRectRawHorizontalCrossingComponent R
      (fkRectForceCutClosed R omega) C}

noncomputable instance instDecidablePredFKRectRawPrimalHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    DecidablePred (FKRectRawHorizontalCrossingComponent R
      (fkRectForceCutClosed R omega)) :=
  Classical.decPred _



noncomputable def fkRectRawPrimalCrossingLeftRows
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Finset (Fin R.height) := by
  classical
  exact Finset.univ.filter fun y =>
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectLeftColumn R, y) = C.1

theorem mem_fkRectRawPrimalCrossingLeftRows
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (y : Fin R.height) :
    y ∈ fkRectRawPrimalCrossingLeftRows R omega C ↔
      (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).connectedComponentMk
          (fkRectLeftColumn R, y) = C.1 := by
  classical
  simp [fkRectRawPrimalCrossingLeftRows]

theorem fkRectRawPrimalCrossingLeftRows_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectRawPrimalCrossingLeftRows R omega C).Nonempty := by
  obtain ⟨y, hy⟩ := C.2.1
  exact ⟨y, (mem_fkRectRawPrimalCrossingLeftRows R omega C y).2 hy⟩


noncomputable def fkRectRawPrimalCrossingFirstRow
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Fin R.height :=
  (fkRectRawPrimalCrossingLeftRows R omega C).min'
    (fkRectRawPrimalCrossingLeftRows_nonempty R omega C)


noncomputable def fkRectRawPrimalCrossingLastRow
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Fin R.height :=
  (fkRectRawPrimalCrossingLeftRows R omega C).max'
    (fkRectRawPrimalCrossingLeftRows_nonempty R omega C)

theorem fkRectRawPrimalCrossingFirstRow_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectLeftColumn R,
          fkRectRawPrimalCrossingFirstRow R omega C) = C.1 := by
  apply (mem_fkRectRawPrimalCrossingLeftRows R omega C _).1
  exact Finset.min'_mem _ _

theorem fkRectRawPrimalCrossingLastRow_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectLeftColumn R,
          fkRectRawPrimalCrossingLastRow R omega C) = C.1 := by
  apply (mem_fkRectRawPrimalCrossingLeftRows R omega C _).1
  exact Finset.max'_mem _ _

theorem fkRectRawPrimalCrossingFirstRow_injective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Injective
      (fkRectRawPrimalCrossingFirstRow R omega) := by
  intro C D hrow
  apply Subtype.ext
  calc
    C.1 = (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk
            (fkRectLeftColumn R,
              fkRectRawPrimalCrossingFirstRow R omega C) :=
      (fkRectRawPrimalCrossingFirstRow_component R omega C).symm
    _ = (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk
            (fkRectLeftColumn R,
              fkRectRawPrimalCrossingFirstRow R omega D) := by rw [hrow]
    _ = D.1 := fkRectRawPrimalCrossingFirstRow_component R omega D

theorem fkRectRawPrimalCrossingLastRow_injective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Injective
      (fkRectRawPrimalCrossingLastRow R omega) := by
  intro C D hrow
  apply Subtype.ext
  calc
    C.1 = (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk
            (fkRectLeftColumn R,
              fkRectRawPrimalCrossingLastRow R omega C) :=
      (fkRectRawPrimalCrossingLastRow_component R omega C).symm
    _ = (fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk
            (fkRectLeftColumn R,
              fkRectRawPrimalCrossingLastRow R omega D) := by rw [hrow]
    _ = D.1 := fkRectRawPrimalCrossingLastRow_component R omega D



noncomputable def fkRectRawPrimalCrossingExtremeRow
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) : Fin R.height :=
  if side then fkRectRawPrimalCrossingFirstRow R omega C
  else fkRectRawPrimalCrossingLastRow R omega C

theorem fkRectRawPrimalCrossingExtremeRow_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectLeftColumn R,
          fkRectRawPrimalCrossingExtremeRow R omega C side) = C.1 := by
  cases side <;> simp [fkRectRawPrimalCrossingExtremeRow,
    fkRectRawPrimalCrossingFirstRow_component,
    fkRectRawPrimalCrossingLastRow_component]



theorem fkRectRawPrimalCrossing_eq_of_extremeRow_eq
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hrow : fkRectRawPrimalCrossingExtremeRow R omega C side =
      fkRectRawPrimalCrossingExtremeRow R omega D side) :
    C = D := by
  cases side
  · exact fkRectRawPrimalCrossingLastRow_injective R omega
      (by simpa [fkRectRawPrimalCrossingExtremeRow] using hrow)
  · exact fkRectRawPrimalCrossingFirstRow_injective R omega
      (by simpa [fkRectRawPrimalCrossingExtremeRow] using hrow)


theorem fkRectOpenGraph_forceCutClosed_le
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R (fkRectForceCutClosed R omega) ≤
      fkRectOpenGraph R omega := by
  apply fkRectOpenGraph_mono R
  intro e he
  by_cases hcut : e ∈ fkRectTorusCutEdges R
  · rw [fkRectForceCutClosed_of_mem R omega e hcut] at he
    contradiction
  · rwa [fkRectForceCutClosed_of_not_mem R omega e hcut] at he


noncomputable def fkRectRawPrimalCrossingTorusComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R omega).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map
    (SimpleGraph.Hom.ofLE (fkRectOpenGraph_forceCutClosed_le R omega)) C.1

@[simp] theorem fkRectRawPrimalCrossingTorusComponent_mk
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    SimpleGraph.ConnectedComponent.map
        (SimpleGraph.Hom.ofLE (fkRectOpenGraph_forceCutClosed_le R omega))
        ((fkRectOpenGraph R
          (fkRectForceCutClosed R omega)).connectedComponentMk x) =
      (fkRectOpenGraph R omega).connectedComponentMk x := by
  exact SimpleGraph.ConnectedComponent.map_mk _ _




noncomputable def fkRectRawPrimalCrossingExtremeDart
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) : FKMedialDart R.medialTorus :=
  fkRectMedialDartAtPrimalVertex R
    (fkRectLeftColumn R,
      fkRectRawPrimalCrossingExtremeRow R omega C side)

@[simp] theorem fkRectRawPrimalCrossingExtremeDart_label
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    fkRectMedialDartPrimalLabel R
        (fkRectRawPrimalCrossingExtremeDart R omega C side) =
      (fkRectLeftColumn R,
        fkRectRawPrimalCrossingExtremeRow R omega C side) := by
  exact fkRectMedialDartPrimalLabel_dartAtPrimalVertex R _



theorem fkRectRawPrimalCrossing_eq_of_extremeDart_eq
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hdart : fkRectRawPrimalCrossingExtremeDart R omega C side =
      fkRectRawPrimalCrossingExtremeDart R omega D side) :
    C = D := by
  apply fkRectRawPrimalCrossing_eq_of_extremeRow_eq R omega C D side
  have hlabel := congrArg (fkRectMedialDartPrimalLabel R) hdart
  simpa only [fkRectRawPrimalCrossingExtremeDart_label, Prod.mk.injEq,
    true_and] using hlabel



structure FKRectZeroTurnAnnulusCharge
    (R : FKRectTorus) (omega : R.Configuration) where
  crossing : FKRectZeroTurnCutRemainderComponent R omega →
    FKRectRawPrimalHorizontalCrossingComponent R omega
  side : FKRectZeroTurnCutRemainderComponent R omega → Bool
  injective_pair : Function.Injective fun C => (crossing C, side C)


noncomputable def fkRectZeroTurnRemainderBlackDart
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKMedialBlackDart R.medialTorus := by
  have hC := (mem_fkRectZeroTurnCutRemainderComponents R omega C.1).1 C.2
  exact Classical.choose
    (exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
      R omega C.1 hC.1 hC.2)

theorem fkRectZeroTurnRemainderBlackDart_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkRectZeroTurnRemainderBlackDart R omega C).1 = C.1 := by
  have hC := (mem_fkRectZeroTurnCutRemainderComponents R omega C.1).1 C.2
  exact (Classical.choose_spec
    (exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
      R omega C.1 hC.1 hC.2)).1

theorem fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C))).1 ≠ 0 := by
  have hC := (mem_fkRectZeroTurnCutRemainderComponents R omega C.1).1 C.2
  exact (Classical.choose_spec
    (exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
      R omega C.1 hC.1 hC.2)).2.1

theorem fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C))).2 = 0 := by
  have hC := (mem_fkRectZeroTurnCutRemainderComponents R omega C.1).1 C.2
  exact (Classical.choose_spec
    (exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
      R omega C.1 hC.1 hC.2)).2.2



noncomputable def fkRectZeroTurnRemainderSide
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) : Bool :=
  decide (0 < (fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C))).1)

theorem fkRectZeroTurnRemainderSide_eq_true_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnRemainderSide R omega C = true ↔
      0 < (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega
          (fkRectZeroTurnRemainderBlackDart R omega C))).1 := by
  simp [fkRectZeroTurnRemainderSide]

theorem fkRectZeroTurnRemainderSide_eq_false_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnRemainderSide R omega C = false ↔
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega
          (fkRectZeroTurnRemainderBlackDart R omega C))).1 < 0 := by
  rw [fkRectZeroTurnRemainderSide, decide_eq_false_iff_not]
  have hne := fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero
    R omega C
  omega


noncomputable def fkRectZeroTurnRemainderPrimalComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectOpenGraph R omega).ConnectedComponent :=
  fkRectMedialComponentToPrimalComponent R omega C.1

theorem fkRectZeroTurnRemainderPrimalComponent_eq_label
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnRemainderPrimalComponent R omega C =
      (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectMedialDartPrimalLabel R
          (fkRectZeroTurnRemainderBlackDart R omega C).1) := by
  unfold fkRectZeroTurnRemainderPrimalComponent
  rw [← fkRectZeroTurnRemainderBlackDart_component R omega C]
  exact fkRectMedialComponentToPrimalComponent_mk R omega _



def FKRectZeroTurnCrossingMatches
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Prop :=
  fkRectRawPrimalCrossingTorusComponent R omega X =
    fkRectZeroTurnRemainderPrimalComponent R omega C




theorem FKRectZeroTurnCrossingMatches.of_extremeDart_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hcomponent :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingExtremeDart R omega X side) = C.1) :
    FKRectZeroTurnCrossingMatches R omega C X := by
  unfold FKRectZeroTurnCrossingMatches
    fkRectZeroTurnRemainderPrimalComponent
  rw [← hcomponent]
  rw [fkRectMedialComponentToPrimalComponent_mk]
  rw [fkRectRawPrimalCrossingExtremeDart_label]
  unfold fkRectRawPrimalCrossingTorusComponent
  rw [← fkRectRawPrimalCrossingExtremeRow_component R omega X side]
  exact fkRectRawPrimalCrossingTorusComponent_mk R omega _



noncomputable def FKRectZeroTurnAnnulusCharge.ofCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hunique : ∀ C D,
      crossing C = crossing D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnAnnulusCharge R omega where
  crossing := crossing
  side := fkRectZeroTurnRemainderSide R omega
  injective_pair := by
    intro C D h
    injection h with hcross hside
    exact hunique C D hcross hside




noncomputable def FKRectZeroTurnAnnulusCharge.ofClusterMatching
    (R : FKRectTorus) (omega : R.Configuration)
    (hexists : ∀ C : FKRectZeroTurnCutRemainderComponent R omega,
      ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
        FKRectZeroTurnCrossingMatches R omega C X)
    (hunique : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      fkRectZeroTurnRemainderPrimalComponent R omega C =
          fkRectZeroTurnRemainderPrimalComponent R omega D →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnAnnulusCharge R omega := by
  let crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega := fun C =>
    Classical.choose (hexists C)
  apply FKRectZeroTurnAnnulusCharge.ofCrossing R omega crossing
  intro C D hcross hside
  apply hunique C D
  · have hC := Classical.choose_spec (hexists C)
    have hD := Classical.choose_spec (hexists D)
    exact hC.symm.trans ((congrArg
      (fkRectRawPrimalCrossingTorusComponent R omega) hcross).trans hD)
  · exact hside





noncomputable def FKRectZeroTurnAnnulusCharge.ofAnchor
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (anchor : FKRectRawPrimalHorizontalCrossingComponent R omega →
      Bool → FKMedialDart R.medialTorus)
    (hanchor : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (anchor (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    FKRectZeroTurnAnnulusCharge R omega :=
  FKRectZeroTurnAnnulusCharge.ofCrossing R omega crossing (by
    intro C D hcross hside
    apply Subtype.ext
    rw [← hanchor C, ← hanchor D, hcross, hside])




noncomputable def FKRectZeroTurnAnnulusCharge.ofExtremeDart
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hextreme : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingExtremeDart R omega (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    FKRectZeroTurnAnnulusCharge R omega :=
  FKRectZeroTurnAnnulusCharge.ofAnchor R omega crossing
    (fkRectRawPrimalCrossingExtremeDart R omega) hextreme

private theorem card_fkRectZeroTurnCutRemainderComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectZeroTurnCutRemainderComponent R omega) =
      fkRectZeroTurnCutRemainderCount R omega := by
  classical
  unfold FKRectZeroTurnCutRemainderComponent
    fkRectZeroTurnCutRemainderCount
  exact Fintype.card_ofFinset
    (fkRectZeroTurnCutRemainderComponents R omega) (by simp)

private theorem card_fkRectRawPrimalHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectRawPrimalHorizontalCrossingComponent R omega) =
      fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  unfold fkRectRawHorizontalCrossingClusterCount
  exact Fintype.card_congr (Equiv.refl _)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (charge : FKRectZeroTurnAnnulusCharge R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  let encode : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega × Bool :=
    fun C => (charge.crossing C, charge.side C)
  have hcard := Fintype.card_le_of_injective encode charge.injective_pair
  rw [card_fkRectZeroTurnCutRemainderComponent] at hcard
  rw [Fintype.card_prod, Fintype.card_bool,
    card_fkRectRawPrimalHorizontalCrossingComponent] at hcard
  omega




theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_crossing
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hunique : ∀ C D,
      crossing C = crossing D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    R omega (FKRectZeroTurnAnnulusCharge.ofCrossing R omega crossing hunique)




theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_clusterMatching
    (R : FKRectTorus) (omega : R.Configuration)
    (hexists : ∀ C : FKRectZeroTurnCutRemainderComponent R omega,
      ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
        FKRectZeroTurnCrossingMatches R omega C X)
    (hunique : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      fkRectZeroTurnRemainderPrimalComponent R omega C =
          fkRectZeroTurnRemainderPrimalComponent R omega D →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    R omega (FKRectZeroTurnAnnulusCharge.ofClusterMatching
      R omega hexists hunique)



theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_anchor
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (anchor : FKRectRawPrimalHorizontalCrossingComponent R omega →
      Bool → FKMedialDart R.medialTorus)
    (hanchor : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (anchor (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    R omega (FKRectZeroTurnAnnulusCharge.ofAnchor
      R omega crossing anchor hanchor)


theorem fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_extremeDart
    (R : FKRectTorus) (omega : R.Configuration)
    (crossing : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hextreme : ∀ C,
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingExtremeDart R omega (crossing C)
            (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_of_annulusCharge
    R omega (FKRectZeroTurnAnnulusCharge.ofExtremeDart
      R omega crossing hextreme)

end

end StatMech.FrontierD
