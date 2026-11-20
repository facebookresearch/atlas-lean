/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryCycleDuality
import Code.FrontierD.FKRectPrimalDualClusterLoopCount
import Code.FrontierD.FiniteBipartiteFlowSparse



open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 600000 in


theorem fkMedialBlackDart_pair_eq_dart01_of_base_eq
    {T : EvenTorus} (v : T.Vertex) (d e : FKMedialBlackDart T)
    (hd : d.1.1 = v) (he : e.1.1 = v) (hne : d ≠ e) :
    s(d, e) = s(fkMedialBlackDart0 v, fkMedialBlackDart1 v) := by
  let E := fkMedialBlackDartEquivVertexBool T
  let bd := (E d).2
  let be := (E e).2
  have hd' : d = if bd then fkMedialBlackDart1 v
      else fkMedialBlackDart0 v := by
    calc
      d = E.symm (E d) := (E.symm_apply_apply d).symm
      _ = _ := by simp [E, bd, fkMedialBlackDartEquivVertexBool, hd]
  have he' : e = if be then fkMedialBlackDart1 v
      else fkMedialBlackDart0 v := by
    calc
      e = E.symm (E e) := (E.symm_apply_apply e).symm
      _ = _ := by simp [E, be, fkMedialBlackDartEquivVertexBool, he]
  cases hbd : bd <;> cases hbe : be <;>
    simp [hbd, hbe] at hd' he'
  all_goals subst d; subst e
  all_goals simp [Sym2.eq_iff] at hne ⊢


@[simp] theorem fkMedialLocalMate_fst
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
  (d : FKMedialDart T) :
    (fkMedialLocalMate pairing d).1 = d.1 := by
  rcases d with ⟨v, side⟩
  cases hpair : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, hpair]



theorem fkRectDualBlackDartEquiv_localPair
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex) :
    s(fkRectDualBlackDartEquiv R omega (fkMedialBlackDart0 v),
        fkRectDualBlackDartEquiv R omega (fkMedialBlackDart1 v)) =
      s(fkMedialBlackDart0 (fkRectMedialDualShiftVertex R v),
        fkMedialBlackDart1 (fkRectMedialDualShiftVertex R v)) := by
  apply fkMedialBlackDart_pair_eq_dart01_of_base_eq
  · simp [fkRectDualBlackDartEquiv, fkRectMedialDualShiftDart,
      fkMedialBlackDart0]
  · simp [fkRectDualBlackDartEquiv, fkRectMedialDualShiftDart,
      fkMedialBlackDart1]
  · intro h
    exact fkMedialBlackDart0_ne_dart1 v
      ((fkRectDualBlackDartEquiv R omega).injective h)



theorem fkRectBoundaryLocalPair_left_eq_of_open
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex)
    (hopen : omega e = true) :
    fkRectBlackBoundaryCyclePrimalComponent R omega
        (Quot.mk _ (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))) =
      fkRectBlackBoundaryCyclePrimalComponent R omega
        (Quot.mk _ (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))) := by
  rw [fkRectBlackBoundaryCyclePrimalComponent_mk,
    fkRectBlackBoundaryCyclePrimalComponent_mk]
  apply ConnectedComponent.sound
  apply fkRectBlackDart01_primalLabels_reachable_of_open
  rw [fkRectTorusMedialEdgeEquiv_vertexOfEdge]
  exact hopen



theorem fkRectBoundaryLocalPair_right_eq_of_closed
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex)
    (hclosed : omega e = false) :
    fkRectBlackBoundaryCycleDualComponent R omega
        (Quot.mk _ (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))) =
      fkRectBlackBoundaryCycleDualComponent R omega
        (Quot.mk _ (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))) := by
  let dual := fkRectDualConfigurationEquiv R omega
  let v := fkRectMedialVertexOfEdge R e
  let sv := fkRectMedialDualShiftVertex R v
  let a := fkRectDualBlackDartEquiv R omega (fkMedialBlackDart0 v)
  let b := fkRectDualBlackDartEquiv R omega (fkMedialBlackDart1 v)
  have hopen : dual (fkRectTorusMedialEdgeEquiv R sv) = true := by
    rw [fkRectTorusMedialEdgeEquiv_dualShiftVertex]
    have hve : fkRectTorusMedialEdgeEquiv R v = e := by
      simp [v]
    rw [hve]
    unfold dual
    rw [fkRectDualConfigurationEquiv_apply_edgeToDualEdge, hclosed]
    rfl
  have h01 := fkRectBlackDart01_primalLabels_reachable_of_open
    R dual sv hopen
  have hab : s(a, b) =
      s(fkMedialBlackDart0 sv, fkMedialBlackDart1 sv) := by
    exact fkRectDualBlackDartEquiv_localPair R omega v
  change (fkRectOpenGraph R dual).connectedComponentMk
      (fkRectMedialDartPrimalLabel R a.1) =
    (fkRectOpenGraph R dual).connectedComponentMk
      (fkRectMedialDartPrimalLabel R b.1)
  rcases Sym2.eq_iff.mp hab with hsame | hswap
  · apply ConnectedComponent.sound
    rw [hsame.1, hsame.2]
    exact h01
  · apply ConnectedComponent.sound
    rw [hswap.1, hswap.2]
    exact h01.symm



theorem fkRectBoundaryLocalPair_incidence_reachable
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    let left := fkRectBlackBoundaryCyclePrimalComponent R omega
    let right := fkRectBlackBoundaryCycleDualComponent R omega
    (bipartiteEdgeIncidenceGraph left right).Reachable
      (Quot.mk _ (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)))
      (Quot.mk _ (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))) := by
  dsimp only
  let A : FKRectConfigurationBlackBoundaryCycle R omega :=
    Quot.mk _ (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))
  let B : FKRectConfigurationBlackBoundaryCycle R omega :=
    Quot.mk _ (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))
  by_cases hAB : A = B
  · change (bipartiteEdgeIncidenceGraph
      (fkRectBlackBoundaryCyclePrimalComponent R omega)
      (fkRectBlackBoundaryCycleDualComponent R omega)).Reachable A B
    rw [hAB]
  · apply SimpleGraph.Adj.reachable
    change A ≠ B ∧ (_ ∨ _)
    refine ⟨hAB, ?_⟩
    cases hstate : omega e
    · exact Or.inr (fkRectBoundaryLocalPair_right_eq_of_closed
        R omega e hstate)
    · exact Or.inl (fkRectBoundaryLocalPair_left_eq_of_open
        R omega e hstate)


theorem fkRectBlackBoundaryCyclePrimalComponent_surjective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Surjective
      (fkRectBlackBoundaryCyclePrimalComponent R omega) := by
  intro K
  induction K using ConnectedComponent.ind with
  | _ x =>
      let pairing := fkRectConfigurationToMedialPairing R omega
      let M := (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
        (fkRectMedialDartAtPrimalVertex R x)
      obtain ⟨C, hC⟩ :=
        (fkMedialBlackBoundaryCycleToLoop_bijective pairing).2 M
      refine ⟨C, ?_⟩
      induction C using Quot.ind with
      | _ d =>
          change (fkRectOpenGraph R omega).connectedComponentMk
              (fkRectMedialDartPrimalLabel R d.1) =
            (fkRectOpenGraph R omega).connectedComponentMk x
          have hloop : (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
              d.1 = M := hC
          have hmapped := congrArg
            (fkRectMedialComponentToPrimalComponent R omega) hloop
          simpa [M, pairing] using hmapped



theorem bipartiteEdgeIncidenceGraph_reachable_of_label_eq
    {E P D : Type*} (left : E → P) (right : E → D)
    {C D' : E} (h : left C = left D' ∨ right C = right D') :
    (bipartiteEdgeIncidenceGraph left right).Reachable C D' := by
  by_cases hCD : C = D'
  · subst D'
    exact .refl C
  · exact (show (bipartiteEdgeIncidenceGraph left right).Adj C D' from
      ⟨hCD, h⟩).reachable



theorem fkRectBoundaryIncidence_reachable_of_torus_adj
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex} (hxy : (fkRectTorusGraph R).Adj x y)
    (C D : FKRectConfigurationBlackBoundaryCycle R omega)
    (hC : fkRectBlackBoundaryCyclePrimalComponent R omega C =
      (fkRectOpenGraph R omega).connectedComponentMk x)
    (hD : fkRectBlackBoundaryCyclePrimalComponent R omega D =
      (fkRectOpenGraph R omega).connectedComponentMk y) :
    let left := fkRectBlackBoundaryCyclePrimalComponent R omega
    let right := fkRectBlackBoundaryCycleDualComponent R omega
    (bipartiteEdgeIncidenceGraph left right).Reachable C D := by
  dsimp only
  obtain ⟨e, he⟩ := hxy
  let A : FKRectConfigurationBlackBoundaryCycle R omega :=
    Quot.mk _ (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))
  let B : FKRectConfigurationBlackBoundaryCycle R omega :=
    Quot.mk _ (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))
  have hlabels :
      s(fkRectMedialDartPrimalLabel R
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1,
        fkRectMedialDartPrimalLabel R
          (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)).1) =
        s(x, y) := by
    rw [fkRectBlackDart01_primalLabels,
      fkRectTorusMedialEdgeEquiv_vertexOfEdge, he]
  have hAB := fkRectBoundaryLocalPair_incidence_reachable R omega e
  have connectLeft {U V : FKRectConfigurationBlackBoundaryCycle R omega}
      (hUV : fkRectBlackBoundaryCyclePrimalComponent R omega U =
        fkRectBlackBoundaryCyclePrimalComponent R omega V) :
      (bipartiteEdgeIncidenceGraph
        (fkRectBlackBoundaryCyclePrimalComponent R omega)
        (fkRectBlackBoundaryCycleDualComponent R omega)).Reachable U V :=
    bipartiteEdgeIncidenceGraph_reachable_of_label_eq _ _ (Or.inl hUV)
  rcases Sym2.eq_iff.mp hlabels with hsame | hswap
  · have hCA : (bipartiteEdgeIncidenceGraph
        (fkRectBlackBoundaryCyclePrimalComponent R omega)
        (fkRectBlackBoundaryCycleDualComponent R omega)).Reachable C A := by
      apply connectLeft
      rw [hC, fkRectBlackBoundaryCyclePrimalComponent_mk, hsame.1]
    have hBD : (bipartiteEdgeIncidenceGraph
        (fkRectBlackBoundaryCyclePrimalComponent R omega)
        (fkRectBlackBoundaryCycleDualComponent R omega)).Reachable B D := by
      apply connectLeft
      rw [hD, fkRectBlackBoundaryCyclePrimalComponent_mk, hsame.2]
    exact hCA.trans (hAB.trans hBD)
  · have hCB : (bipartiteEdgeIncidenceGraph
        (fkRectBlackBoundaryCyclePrimalComponent R omega)
        (fkRectBlackBoundaryCycleDualComponent R omega)).Reachable C B := by
      apply connectLeft
      rw [hC, fkRectBlackBoundaryCyclePrimalComponent_mk, hswap.2]
    have hAD : (bipartiteEdgeIncidenceGraph
        (fkRectBlackBoundaryCyclePrimalComponent R omega)
        (fkRectBlackBoundaryCycleDualComponent R omega)).Reachable A D := by
      apply connectLeft
      rw [hD, fkRectBlackBoundaryCyclePrimalComponent_mk, hswap.1]
    exact hCB.trans (hAB.symm.trans hAD)



theorem fkRectBoundaryIncidence_reachable_of_torus_walk
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex} (p : (fkRectTorusGraph R).Walk x y)
    (C D : FKRectConfigurationBlackBoundaryCycle R omega)
    (hC : fkRectBlackBoundaryCyclePrimalComponent R omega C =
      (fkRectOpenGraph R omega).connectedComponentMk x)
    (hD : fkRectBlackBoundaryCyclePrimalComponent R omega D =
      (fkRectOpenGraph R omega).connectedComponentMk y) :
    let left := fkRectBlackBoundaryCyclePrimalComponent R omega
    let right := fkRectBlackBoundaryCycleDualComponent R omega
    (bipartiteEdgeIncidenceGraph left right).Reachable C D := by
  dsimp only
  induction p generalizing C with
  | nil =>
      apply bipartiteEdgeIncidenceGraph_reachable_of_label_eq _ _
      exact Or.inl (hC.trans hD.symm)
  | @cons u v w huv p ih =>
      obtain ⟨M, hM⟩ :=
        fkRectBlackBoundaryCyclePrimalComponent_surjective R omega
          ((fkRectOpenGraph R omega).connectedComponentMk v)
      have hfirst := fkRectBoundaryIncidence_reachable_of_torus_adj
        R omega huv C M hC hM
      exact hfirst.trans (ih M hM hD)



theorem fkRectBoundaryCycleIncidence_connected
    (R : FKRectTorus) (omega : R.Configuration) :
    (bipartiteEdgeIncidenceGraph
      (fkRectBlackBoundaryCyclePrimalComponent R omega)
      (fkRectBlackBoundaryCycleDualComponent R omega)).Connected := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let d0 := fkMedialBlackDart0
    (fkRectMedialVertexOfEdge R (true,
      (⟨0, R.width_pos⟩, ⟨0, R.height_pos⟩)))
  let _ : Nonempty (FKRectConfigurationBlackBoundaryCycle R omega) :=
    ⟨Quot.mk _ d0⟩
  refine ⟨?_⟩
  intro C D
  let KC := fkRectBlackBoundaryCyclePrimalComponent R omega C
  let KD := fkRectBlackBoundaryCyclePrimalComponent R omega D
  let x := KC.out
  let y := KD.out
  obtain ⟨p⟩ := (fkRectTorusGraph_connected R).preconnected x y
  apply fkRectBoundaryIncidence_reachable_of_torus_walk R omega p C D
  · exact KC.out_eq.symm
  · exact KD.out_eq.symm



theorem fkRectBlackBoundaryCycleDualComponent_surjective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Surjective
      (fkRectBlackBoundaryCycleDualComponent R omega) := by
  intro L
  obtain ⟨D, hD⟩ := fkRectBlackBoundaryCyclePrimalComponent_surjective
    R (fkRectDualConfigurationEquiv R omega) L
  let C := (fkRectBlackBoundaryCycleDualEquiv R omega).symm D
  refine ⟨C, ?_⟩
  unfold fkRectBlackBoundaryCycleDualComponent
  rw [(fkRectBlackBoundaryCycleDualEquiv R omega).apply_symm_apply]
  exact hD


theorem card_fkRectConfigurationBlackBoundaryCycle
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card (FKRectConfigurationBlackBoundaryCycle R omega) =
      fkRectMedialLoopCount R omega := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let e : FKRectConfigurationBlackBoundaryCycle R omega ≃
      FKMedialLoop R.medialTorus pairing :=
    Equiv.ofBijective (fkMedialBlackBoundaryCycleToLoop pairing)
      (fkMedialBlackBoundaryCycleToLoop_bijective pairing)
  rw [Fintype.card_congr e]
  simp [fkRectMedialLoopCount, fkMedialLoopCount, pairing,
    Nat.card_eq_fintype_card]



theorem card_boundaryCycles_le_incidentComponents
    (R : FKRectTorus) (omega : R.Configuration)
    [DecidableEq (fkRectOpenGraph R omega).ConnectedComponent]
    [DecidableEq (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent] :
    Fintype.card (FKRectConfigurationBlackBoundaryCycle R omega) ≤
      ((Finset.univ : Finset
        (FKRectConfigurationBlackBoundaryCycle R omega)).image
          (fkRectBlackBoundaryCyclePrimalComponent R omega)).card +
      ((Finset.univ : Finset
        (FKRectConfigurationBlackBoundaryCycle R omega)).image
          (fkRectBlackBoundaryCycleDualComponent R omega)).card := by
  classical
  rw [Finset.image_univ_of_surjective
      (fkRectBlackBoundaryCyclePrimalComponent_surjective R omega),
    Finset.image_univ_of_surjective
      (fkRectBlackBoundaryCycleDualComponent_surjective R omega),
    Finset.card_univ, Finset.card_univ,
    card_fkRectConfigurationBlackBoundaryCycle]
  have h := fkRectMedialLoopCount_add_netIndicators_eq_clusterCounts R omega
  unfold fkRectNumClusters at h
  omega


theorem card_boundaryCycles_le_incidentComponents_of_not_hasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (_hnoNet : ¬ FKRectHasNet R omega)
    [DecidableEq (fkRectOpenGraph R omega).ConnectedComponent]
    [DecidableEq (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent] :
    Fintype.card (FKRectConfigurationBlackBoundaryCycle R omega) ≤
      ((Finset.univ : Finset
        (FKRectConfigurationBlackBoundaryCycle R omega)).image
          (fkRectBlackBoundaryCyclePrimalComponent R omega)).card +
      ((Finset.univ : Finset
        (FKRectConfigurationBlackBoundaryCycle R omega)).image
          (fkRectBlackBoundaryCycleDualComponent R omega)).card :=
  card_boundaryCycles_le_incidentComponents R omega



theorem fkRectPrimalBoundarySupportedFiberSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    [DecidableEq (fkRectOpenGraph R omega).ConnectedComponent] :
    (∑ C ∈ ((Finset.univ : Finset
        (FKRectConfigurationBlackBoundaryCycle R omega)).filter fun C ↦
          fkRectBlackBoundaryCycleWinding R omega C ≠ 0).filter
        (fun C ↦ fkRectBlackBoundaryCyclePrimalComponent R omega C = K),
      fkRectBlackBoundaryCycleWinding R omega C) = 0 := by
  classical
  have hzero := fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero
    R omega K.out
  unfold fkRectPrimalClusterBoundaryCycleWindingSum at hzero
  have hcomponent (C : FKRectConfigurationBlackBoundaryCycle R omega) :
      fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C ↔
        fkRectBlackBoundaryCyclePrimalComponent R omega C = K := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent,
      show (fkRectOpenGraph R omega).connectedComponentMk K.out = K from
        K.out_eq]
  simp_rw [hcomponent] at hzero
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if fkRectBlackBoundaryCycleWinding R omega C ≠ 0 then
          if fkRectBlackBoundaryCyclePrimalComponent R omega C = K then
            fkRectBlackBoundaryCycleWinding R omega C else 0 else 0) =
      ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if fkRectBlackBoundaryCyclePrimalComponent R omega C = K then
          fkRectBlackBoundaryCycleWinding R omega C else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      by_cases hw : fkRectBlackBoundaryCycleWinding R omega C = 0 <;>
        by_cases hK : fkRectBlackBoundaryCyclePrimalComponent R omega C = K <;>
        simp [hw, hK]
    _ = 0 := hzero


noncomputable def fkRectDualBoundarySupportedFiberSum
    (R : FKRectTorus) (omega : R.Configuration)
    (L : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent) : Int × Int := by
  classical
  exact ∑ C ∈ ((Finset.univ : Finset
        (FKRectConfigurationBlackBoundaryCycle R omega)).filter fun C ↦
          fkRectBlackBoundaryCycleWinding R omega C ≠ 0).filter
        (fun C ↦ fkRectBlackBoundaryCycleDualComponent R omega C = L),
      fkRectBlackBoundaryCycleWinding R omega C

set_option maxHeartbeats 600000 in


theorem fkRectDualBoundarySupportedFiberSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (L : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent) :
    fkRectDualBoundarySupportedFiberSum R omega L = 0 := by
  classical
  let w := fkRectBlackBoundaryCycleWinding R omega
  let right := fkRectBlackBoundaryCycleDualComponent R omega
  unfold fkRectDualBoundarySupportedFiberSum
  change (∑ C ∈ ((Finset.univ : Finset
      (FKRectConfigurationBlackBoundaryCycle R omega)).filter fun C ↦
        w C ≠ 0).filter (fun C ↦ right C = L), w C) = 0
  have hzero := fkRectDualClusterBoundaryCycleWindingSum_eq_zero R omega L
  change (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
      if right C = L then w C else 0) = 0 at hzero
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if w C ≠ 0 then
          if right C = L then w C else 0 else 0) =
      ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if right C = L then w C else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      by_cases hw : w C = 0 <;>
        by_cases hL : right C = L <;>
        simp [hw, hL]
    _ = 0 := hzero

set_option maxHeartbeats 800000 in



theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 := by
  classical
  have hcard := connectedBipartiteFlow_leftFiber_card_le_two
    (fkRectBlackBoundaryCyclePrimalComponent R omega)
    (fkRectBlackBoundaryCycleDualComponent R omega)
    (fkRectBlackBoundaryCycleWinding R omega)
    (fkRectBoundaryCycleIncidence_connected R omega)
    (card_boundaryCycles_le_incidentComponents R omega)
    (fun p => fkRectPrimalBoundarySupportedFiberSum_eq_zero R omega p)
    (fun d => by
      have h := fkRectDualBoundarySupportedFiberSum_eq_zero R omega d
      unfold fkRectDualBoundarySupportedFiberSum at h
      exact h) K
  have hcomponent (C : FKRectConfigurationBlackBoundaryCycle R omega) :
      fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C ↔
        fkRectBlackBoundaryCyclePrimalComponent R omega C = K := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent,
      show (fkRectOpenGraph R omega).connectedComponentMk K.out = K from
        K.out_eq]
  simpa only [fkRectPrimalClusterNonzeroBoundaryCycles,
    Finset.mem_filter, Finset.mem_univ, true_and, hcomponent] using hcard

set_option maxHeartbeats 800000 in


theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2 := by
  let K := (fkRectOpenGraph R omega).connectedComponentMk x
  have h := card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two R omega K
  have hcomponent (C : FKRectConfigurationBlackBoundaryCycle R omega) :
      fkRectBlackBoundaryCycleInPrimalCluster R omega x C ↔
        fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent,
      fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent,
      show (fkRectOpenGraph R omega).connectedComponentMk x = K from rfl,
      show (fkRectOpenGraph R omega).connectedComponentMk K.out = K from
        K.out_eq]
  have hset : fkRectPrimalClusterNonzeroBoundaryCycles R omega x =
      fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out := by
    ext C
    simp only [fkRectPrimalClusterNonzeroBoundaryCycles,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr (hcomponent C) Iff.rfl
  rw [hset]
  exact h


theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_not_hasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (_hnoNet : ¬ FKRectHasNet R omega)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 :=
  card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two R omega K

end

end StatMech.FrontierD
