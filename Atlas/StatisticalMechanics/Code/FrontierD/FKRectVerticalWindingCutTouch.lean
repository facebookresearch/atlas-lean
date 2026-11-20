/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingCutFiberBalance
import Code.FrontierD.FKRectTorusWindingEvent









open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

private theorem fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut_touch
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectHorizontalCutEdges R) :
    fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val = 0 at ha
  have hlast : R.height - 1 + 1 = R.height := by omega
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk]
    all_goals rw [fkRectCyclicPred_val]
    all_goals simp only [ha, if_true]
    all_goals exact Or.inl ⟨True.intro, hlast⟩
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk]
    rw [fkRectCyclicPred_val]
    simp only [ha, if_true]
    exact Or.inl ⟨True.intro, hlast⟩



theorem fkRectForceHorizontalCutClosed_adj_of_not_crossesVerticalSeam
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Adj x y)
    (hnot : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
    (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).Adj x y := by
  rcases hxy with ⟨a, hopen, hedge⟩
  refine ⟨a, ?_, hedge⟩
  have hcut : a ∉ fkRectHorizontalCutEdges R := by
    intro ha
    apply hnot
    rw [← hedge]
    exact fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut_touch
      R a ha
  simpa [fkRectForceHorizontalCutClosed, fkRectForceEdgesClosed, hcut]
    using hopen



noncomputable def fkRectTopComponentPotential
    (R : FKRectTorus) (eta : R.Configuration) (x : R.Vertex) : Int := by
  classical
  exact if ∃ z : Fin R.width,
    (fkRectOpenGraph R eta).connectedComponentMk x =
      (fkRectOpenGraph R eta).connectedComponentMk
        (z, fkRectTopRow R) then 1 else 0

@[simp] theorem fkRectTopComponentPotential_top
    (R : FKRectTorus) (eta : R.Configuration) (z : Fin R.width) :
    fkRectTopComponentPotential R eta (z, fkRectTopRow R) = 1 := by
  classical
  unfold fkRectTopComponentPotential
  rw [if_pos ⟨z, rfl⟩]

private theorem fkRectTopComponentPotential_bottom_eq_zero_of_noCrossing
    (R : FKRectTorus) (eta : R.Configuration) (z : Fin R.width)
    (hno : ¬ FKRectHorizontalCutPrimalCrossingComponent R eta
      ((fkRectOpenGraph R eta).connectedComponentMk
        (z, fkRectBottomRow R))) :
    fkRectTopComponentPotential R eta (z, fkRectBottomRow R) = 0 := by
  unfold fkRectTopComponentPotential
  split
  · rename_i htop
    obtain ⟨w, hw⟩ := htop
    exfalso
    apply hno
    exact ⟨⟨z, rfl⟩, ⟨w, hw.symm⟩⟩
  · rfl

private theorem fkRectVerticalIncrement_eq_topPotential_sub
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex} (hxy : (fkRectOpenGraph R omega).Adj x y)
    (hnox : ¬ FKRectHorizontalCutPrimalCrossingComponent R
      (fkRectForceHorizontalCutClosed R omega)
      ((fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x))
    (hnoy : ¬ FKRectHorizontalCutPrimalCrossingComponent R
      (fkRectForceHorizontalCutClosed R omega)
      ((fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk y)) :
    fkRectVerticalSeamIncrement R x y =
      fkRectTopComponentPotential R
          (fkRectForceHorizontalCutClosed R omega) x -
        fkRectTopComponentPotential R
          (fkRectForceHorizontalCutClosed R omega) y := by
  by_cases hcross : fkRectCrossesVerticalSeam R s(x, y)
  · rw [fkRectCrossesVerticalSeam_mk] at hcross
    rcases hcross with ⟨hx0, hytop⟩ | ⟨hy0, hxtop⟩
    · have hxbot : x.2 = fkRectBottomRow R := by
        apply Fin.ext
        simpa [fkRectBottomRow] using hx0
      have hyt : y.2 = fkRectTopRow R := by
        apply Fin.ext
        dsimp [fkRectTopRow]
        omega
      have hxEq : x = (x.1, fkRectBottomRow R) := Prod.ext rfl hxbot
      have hyEq : y = (y.1, fkRectTopRow R) := Prod.ext rfl hyt
      rw [hxEq] at hnox
      rw [hxEq, hyEq,
        fkRectTopComponentPotential_bottom_eq_zero_of_noCrossing
          R _ x.1 hnox,
        fkRectTopComponentPotential_top]
      unfold fkRectVerticalSeamIncrement
      have hheight := R.height_gt_two
      simp [fkRectBottomRow, fkRectTopRow]
      omega
    · have hybot : y.2 = fkRectBottomRow R := by
        apply Fin.ext
        simpa [fkRectBottomRow] using hy0
      have hxt : x.2 = fkRectTopRow R := by
        apply Fin.ext
        dsimp [fkRectTopRow]
        omega
      have hxEq : x = (x.1, fkRectTopRow R) := Prod.ext rfl hxt
      have hyEq : y = (y.1, fkRectBottomRow R) := Prod.ext rfl hybot
      rw [hyEq] at hnoy
      rw [hxEq, hyEq,
        fkRectTopComponentPotential_top,
        fkRectTopComponentPotential_bottom_eq_zero_of_noCrossing
          R _ y.1 hnoy]
      unfold fkRectVerticalSeamIncrement
      have hheight := R.height_gt_two
      simp [fkRectBottomRow, fkRectTopRow]
      omega
  · have hcutAdj :=
      fkRectForceHorizontalCutClosed_adj_of_not_crossesVerticalSeam
        R omega hxy hcross
    have hcomponent :
        (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x =
          (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk y :=
      ConnectedComponent.sound hcutAdj.reachable
    rw [fkRectVerticalSeamIncrement_eq_zero_of_not_crosses
      R x y hcross]
    unfold fkRectTopComponentPotential
    rw [hcomponent]
    ring

private theorem fkRectWalkWinding_snd_eq_topPotential_sub_of_supportNoCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex} (p : (fkRectOpenGraph R omega).Walk x y)
    (hno : ∀ z ∈ p.support,
      ¬ FKRectHorizontalCutPrimalCrossingComponent R
        (fkRectForceHorizontalCutClosed R omega)
        ((fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk z)) :
    (fkRectWalkWinding R p).2 =
      fkRectTopComponentPotential R
          (fkRectForceHorizontalCutClosed R omega) x -
        fkRectTopComponentPotential R
          (fkRectForceHorizontalCutClosed R omega) y := by
  induction p with
  | nil => simp [fkRectWalkWinding]
  | @cons x z y hxz p ih =>
      have hnox := hno x (by simp [Walk.support_cons])
      have hnoTail : ∀ w ∈ p.support,
          ¬ FKRectHorizontalCutPrimalCrossingComponent R
            (fkRectForceHorizontalCutClosed R omega)
            ((fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk w) := by
        intro w hw
        exact hno w (by simp [Walk.support_cons, hw])
      have hnoz := hnoTail z p.start_mem_support
      simp only [fkRectWalkWinding, Prod.snd]
      rw [fkRectVerticalIncrement_eq_topPotential_sub
        R omega hxz hnox hnoz, ih hnoTail]
      ring



theorem exists_fkRectHorizontalCutPrimalCrossingComponent_touched_by_closedWalk
    (R : FKRectTorus) (omega : R.Configuration) {x : R.Vertex}
    (p : (fkRectOpenGraph R omega).Walk x x)
    (hwind : (fkRectWalkWinding R p).2 ≠ 0) :
    ∃ C : (fkRectOpenGraph R
        (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent,
      FKRectHorizontalCutPrimalCrossingComponent R
          (fkRectForceHorizontalCutClosed R omega) C ∧
        ∃ z ∈ p.support,
          (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk z = C := by
  by_contra hnone
  push Not at hnone
  have hno : ∀ z ∈ p.support,
      ¬ FKRectHorizontalCutPrimalCrossingComponent R
        (fkRectForceHorizontalCutClosed R omega)
        ((fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk z) := by
    intro z hz hcross
    exact hnone _ hcross z hz rfl
  have hzero :=
    fkRectWalkWinding_snd_eq_topPotential_sub_of_supportNoCrossing
      R omega p hno
  simp only [sub_self] at hzero
  exact hwind hzero



theorem exists_horizontalCutCrossing_in_fiber_of_blackBoundaryWinding_snd_ne_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectConfigurationBlackBoundaryCycle R omega)
    (hwind : (fkRectBlackBoundaryCycleWinding R omega C).2 ≠ 0) :
    ∃ X : (fkRectOpenGraph R
        (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent,
      FKRectHorizontalCutPrimalCrossingComponent R
          (fkRectForceHorizontalCutClosed R omega) X ∧
        fkRectHorizontalCutComponentTorusComponent R omega X =
          fkRectBlackBoundaryCyclePrimalComponent R omega C := by
  induction C using Quot.ind with
  | _ d =>
      rw [fkRectBlackBoundaryCycleWinding_mk,
        ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
        at hwind
      let p := fkRectBlackBoundaryPrimalCycleWalk R omega d
      obtain ⟨X, hcross, z, hz, hzX⟩ :=
        exists_fkRectHorizontalCutPrimalCrossingComponent_touched_by_closedWalk
          R omega p hwind
      refine ⟨X, hcross, ?_⟩
      have hzstart :
          (fkRectOpenGraph R omega).connectedComponentMk z =
            (fkRectOpenGraph R omega).connectedComponentMk
              (fkRectMedialDartPrimalLabel R d.1) := by
        exact ConnectedComponent.sound (p.takeUntil z hz).reachable.symm
      rw [← hzX, fkRectHorizontalCutComponentTorusComponent_mk,
        hzstart, fkRectBlackBoundaryCyclePrimalComponent_mk]



theorem fkRectPrimalComponentHorizontalCutCrossingCount_pos_of_positiveBoundaryMass
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hmass : 0 <
      fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K) :
    0 < fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
  classical
  unfold fkRectPrimalComponentPositiveBoundaryVerticalMass at hmass
  rw [Finset.sum_pos_iff] at hmass
  obtain ⟨C, _, hC⟩ := hmass
  have hCK : fkRectBlackBoundaryCyclePrimalComponent R omega C = K := by
    by_contra hne
    simp [hne] at hC
  rw [if_pos hCK] at hC
  have hwind : (fkRectBlackBoundaryCycleWinding R omega C).2 ≠ 0 := by
    omega
  obtain ⟨X, hcross, hXK⟩ :=
    exists_horizontalCutCrossing_in_fiber_of_blackBoundaryWinding_snd_ne_zero
      R omega C hwind
  unfold fkRectPrimalComponentHorizontalCutCrossingCount
  apply Finset.card_pos.mpr
  refine ⟨⟨X, hcross⟩, ?_⟩
  simp [hXK, hCK]



theorem fkRectPositiveBoundaryVerticalMass_le_crossingCount_of_le_one
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hle : fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤ 1) :
    fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤
      fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
  by_cases hzero :
      fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K = 0
  · simp [hzero]
  · have hmass :
        fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K = 1 := by
      omega
    rw [hmass]
    exact fkRectPrimalComponentHorizontalCutCrossingCount_pos_of_positiveBoundaryMass
      R omega K (by omega)

end

end StatMech.FrontierD
