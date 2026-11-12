/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnMixedCandidates
import Code.FrontierD.FKRectBoundaryToggleWinding
import Code.FrontierD.FKRectRefinedOpenBoundaryDependence

open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

private theorem seamTrace_eq_sum_range
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d n =
      ∑ i ∈ Finset.range n,
        fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[i] d) := by
  induction n generalizing d with
  | zero => simp [fkRectMedialBoundaryPrimalSeamTrace]
  | succ n ih =>
      rw [fkRectMedialBoundaryPrimalSeamTrace, ih,
        Finset.sum_range_succ']
      have htail :
          (∑ i ∈ Finset.range n,
            fkRectMedialBoundaryPrimalSeamIncrement R pairing
              ((fkMedialBoundaryStep pairing)^[i]
                (fkMedialBoundaryStep pairing d))) =
          ∑ i ∈ Finset.range n,
            fkRectMedialBoundaryPrimalSeamIncrement R pairing
              ((fkMedialBoundaryStep pairing)^[i + 1] d) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.iterate_succ_apply]
      rw [htail]
      simp only [Function.iterate_zero_apply]
      exact add_comm _ _



theorem fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) =
      fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R omega) d := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let sigma := fkMedialBlackBoundaryPerm pairing
  let l := fkRectBlackOrbitList pairing d
  let f : FKMedialBlackDart R.medialTorus → Int × Int :=
    fkRectBlackBoundaryWeight R pairing
  have hdSupport : d ∈ sigma.support := by
    rw [Equiv.Perm.mem_support]
    exact fkMedialBlackBoundaryPerm_apply_ne pairing d
  rw [fkRectBlackBoundaryPrimalCycleWalk_winding]
  change fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 l.length = _
  rw [seamTrace_eq_sum_range]
  have hsum :
      (∑ i ∈ Finset.range l.length,
        fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[i] d.1)) =
        ∑ i ∈ Finset.range l.length, f ((sigma^[i]) d) := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold f fkRectBlackBoundaryWeight
    rw [fkMedialBlackBoundaryPerm_iterate_val]
  rw [hsum]
  change (∑ i ∈ Finset.range l.length, f ((sigma^[i]) d)) = _
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin l.length, f ((sigma^[i.val]) d)) =
        (l.map f).sum := by
          rw [← List.sum_ofFn]
          have hlist :
              List.ofFn (fun i : Fin l.length ↦ f ((sigma^[i.val]) d)) =
                l.map f := by
            rw [← List.ofFn_getElem_eq_map l f]
            congr 1
            funext i
            apply congrArg f
            simpa [l, sigma, List.get_eq_getElem] using
              (fkRectBlackOrbitList_get pairing d i).symm
          rw [hlist]
    _ = ∑ x ∈ l.toFinset, f x := by
      exact (List.sum_toFinset f (by
        simpa [l, sigma] using Equiv.Perm.nodup_toList sigma d)).symm
    _ = fkRectBlackBoundaryCycleClassWinding R pairing d := by
      unfold fkRectBlackBoundaryCycleClassWinding
        permCycleClassWeightSum
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change x ∈ sigma.toList d ↔ sigma.SameCycle d x
      rw [Equiv.Perm.mem_toList_iff]
      simp [hdSupport]



theorem fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d.1) =
      permOrbitVisitCount
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega)) d.1 d.1 •
        fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d) := by
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul,
    fkRectBoundaryCycleClassWinding_eq_black,
    fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]




theorem
    fkRectMedialBoundaryPrimalOrbitWalk_winding_ne_zero_of_componentTurn_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    (hturn : FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega)
      ((fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d) =
        0) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d) ≠ (0, 0) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  have blackCase (b : FKMedialBlackDart R.medialTorus)
      (hbturn : FKMedialTurningFiber.canonicalComponentTurn pairing
        ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk b.1) =
          0) :
      fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1) ≠ (0, 0) := by
    have hdisp := fkRectBlackOrbitDisplacement_ne_zero_of_turn_eq_zero
      R pairing
      ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk b.1)
      b rfl hbturn
    have hprimitive :=
      fkRectBlackBoundaryPrimalCycleWalk_winding_ne_zero_of_displacement
        R omega b hdisp
    rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle]
    let m := permOrbitVisitCount (fkMedialBoundaryStep pairing) b.1 b.1
    have hm : 0 < m := permOrbitVisitCount_self_pos _ _
    intro hzero
    apply hprimitive
    have hfirst := congrArg Prod.fst hzero
    have hsecond := congrArg Prod.snd hzero
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul,
      Prod.fst_zero, Prod.snd_zero] at hfirst hsecond
    have hm0 : (m : Int) ≠ 0 := by exact_mod_cast hm.ne'
    apply Prod.ext
    · exact (mul_eq_zero.mp hfirst).resolve_left hm0
    · exact (mul_eq_zero.mp hsecond).resolve_left hm0
  by_cases hd : fkMedialCheckerColor d = false
  · let b : FKMedialBlackDart R.medialTorus := ⟨d, hd⟩
    exact blackCase b (by simpa [pairing, b] using hturn)
  · have hdtrue : fkMedialCheckerColor d = true :=
      Bool.eq_true_of_not_eq_false hd
    let e := fkMedialLocalMate pairing d
    have heblack : fkMedialCheckerColor e = false := by
      rw [show e = fkMedialLocalMate pairing d from rfl,
        fkMedialCheckerColor_localMate_eq_not, hdtrue]
      rfl
    let b : FKMedialBlackDart R.medialTorus := ⟨e, heblack⟩
    have heComponent : (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
        e = (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_reachable_localMate pairing d).symm
    have hbturn : FKMedialTurningFiber.canonicalComponentTurn pairing
        ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk b.1) =
          0 := by
      change FKMedialTurningFiber.canonicalComponentTurn pairing
          ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e) = 0
      rw [heComponent]
      exact hturn
    have hb := blackCase b hbturn
    intro hzero
    apply hb
    change fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega e) = (0, 0)
    rw [show e = fkMedialLocalMate pairing d from rfl,
      fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate, hzero]
    simp


theorem fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
    (R : FKRectTorus) (omega : R.Configuration) {x : R.Vertex}
    (w : (fkRectOpenGraph R omega).Walk x x)
    (d : FKMedialDart R.medialTorus) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R w) := by
  generalize hF : fkRectOpenEdges R omega = F
  have hconfig : fkRectConfigurationOfEdges R F = omega := by
    rw [← hF]
    exact fkRectConfigurationOfEdges_openEdges R omega
  clear hF
  cases hconfig
  exact fkRect_boundaryOrbit_winding_dependent_of_openWalk R F w d



theorem fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    {x : R.Vertex} (w : (fkRectOpenGraph R omega).Walk x x) :
    (fkRectWalkWinding R w).2 = 0 := by
  let d := fkRectZeroTurnRemainderBlackDart R omega C
  let m := permOrbitVisitCount
    (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega)) d.1 d.1
  have hm : 0 < m := permOrbitVisitCount_self_pos _ _
  have hd1 := fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C
  have hd2 := fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero R omega C
  have hdep :=
    fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
      R omega w d.1
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
    R omega d] at hdep
  unfold FKRectWindingIndependent at hdep
  push Not at hdep
  simp only [Prod.smul_fst, Prod.smul_snd] at hdep
  simp only [nsmul_eq_mul] at hdep
  change (fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0 at hd1
  change (fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 at hd2
  have hm0 : (m : Int) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hd2] at hdep
  simp only [mul_zero, zero_mul, sub_zero] at hdep
  rcases mul_eq_zero.mp hdep with hma | hw
  · exact ((mul_ne_zero hm0 hd1) hma).elim
  · exact hw



theorem not_fkRectHasNet_of_zeroTurnRemainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    ¬ FKRectHasNet R omega := by
  rintro ⟨x, p, q, hpq⟩
  have hp := fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder
    R omega C p
  have hq := fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder
    R omega C q
  apply hpq
  rw [hp, hq]
  ring



theorem fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (d : FKMedialDart R.medialTorus) :
    (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 = 0 := by
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  let w := fkRectBlackBoundaryPrimalCycleWalk R omega b
  have hb1 :=
    fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C
  have hb2 :=
    fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero R omega C
  have hdep :=
    fkRect_boundaryOrbit_winding_dependent_of_openWalk_configuration
      R omega w d
  unfold FKRectWindingIndependent at hdep
  push Not at hdep
  change (fkRectWalkWinding R w).1 ≠ 0 at hb1
  change (fkRectWalkWinding R w).2 = 0 at hb2
  rw [hb2] at hdep
  simp only [mul_zero, zero_sub] at hdep
  have hmul :
      (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 *
        (fkRectWalkWinding R w).1 = 0 := by
    linarith
  exact (mul_eq_zero.mp hmul).resolve_right hb1



theorem fkRectBlackBoundaryPrimalCycleWalk_verticalWinding_eq_zero_of_remainder
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (d : FKMedialBlackDart R.medialTorus) :
    (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
  have horbit :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C d.1
  rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle]
    at horbit
  let m := permOrbitVisitCount
    (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega)) d.1 d.1
  have hmul : (m : Int) *
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
    simpa only [m, Prod.smul_snd, nsmul_eq_mul] using horbit
  have hm0 : (m : Int) ≠ 0 := by
    have hpos := permOrbitVisitCount_self_pos
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega)) d.1
    exact_mod_cast hpos.ne'
  exact (mul_eq_zero.mp hmul).resolve_left hm0




noncomputable def fkRectZeroTurnRemainderOrientedDart
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) : FKMedialDart R.medialTorus :=
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := (fkRectZeroTurnRemainderBlackDart R omega C).1
  if color then fkMedialLocalMate pairing b else b

@[simp] theorem fkRectZeroTurnRemainderOrientedDart_checkerColor
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) :
    fkMedialCheckerColor
        (fkRectZeroTurnRemainderOrientedDart R omega C color) = color := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  cases color
  · exact b.2
  · change fkMedialCheckerColor (fkMedialLocalMate pairing b.1) = true
    rw [fkMedialCheckerColor_localMate_eq_not, b.2]
    rfl



theorem fkRectZeroTurnRemainderOrientedDart_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) :
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkRectZeroTurnRemainderOrientedDart R omega C color) = C.1 := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  cases color
  · exact fkRectZeroTurnRemainderBlackDart_component R omega C
  · calc
      (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
          (fkMedialLocalMate pairing b.1) =
          (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
            b.1 := by
        apply SimpleGraph.ConnectedComponent.sound
        exact (fkMedial_reachable_localMate pairing b.1).symm
      _ = C.1 := fkRectZeroTurnRemainderBlackDart_component R omega C



theorem fkRectZeroTurnRemainderOrientedDart_winding_fst_pos_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) :
    0 < (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega
        (fkRectZeroTurnRemainderOrientedDart R omega C color))).1 ↔
      fkRectZeroTurnRemainderSide R omega C = !color := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  let m := permOrbitVisitCount (fkMedialBoundaryStep pairing) b.1 b.1
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega b)
  have hmNat : 0 < m := permOrbitVisitCount_self_pos _ _
  have hm : (0 : Int) < m := by exact_mod_cast hmNat
  have horbit : fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1) = m • w := by
    exact fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
      R omega b
  cases color
  · change 0 < (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1)).1 ↔
        fkRectZeroTurnRemainderSide R omega C = true
    rw [horbit]
    simp only [nsmul_eq_mul]
    rw [fkRectZeroTurnRemainderSide_eq_true_iff]
    change 0 < (m : Int) * w.1 ↔ 0 < w.1
    constructor <;> intro h <;> nlinarith
  · change 0 < (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega
          (fkMedialLocalMate pairing b.1))).1 ↔
        fkRectZeroTurnRemainderSide R omega C = false
    rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate, horbit]
    simp only [Prod.fst_neg, nsmul_eq_mul]
    rw [fkRectZeroTurnRemainderSide_eq_false_iff]
    change 0 < -((m : Int) * w.1) ↔ w.1 < 0
    constructor <;> intro h <;> nlinarith



theorem fkRectZeroTurnRemainderOrientedDart_winding_fst_neg_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) :
    (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega
        (fkRectZeroTurnRemainderOrientedDart R omega C color))).1 < 0 ↔
      fkRectZeroTurnRemainderSide R omega C = color := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  let m := permOrbitVisitCount (fkMedialBoundaryStep pairing) b.1 b.1
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega b)
  have hmNat : 0 < m := permOrbitVisitCount_self_pos _ _
  have hm : (0 : Int) < m := by exact_mod_cast hmNat
  have horbit : fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1) = m • w := by
    exact fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
      R omega b
  cases color
  · change (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1)).1 < 0 ↔
        fkRectZeroTurnRemainderSide R omega C = false
    rw [horbit]
    simp only [nsmul_eq_mul]
    rw [fkRectZeroTurnRemainderSide_eq_false_iff]
    change (m : Int) * w.1 < 0 ↔ w.1 < 0
    constructor <;> intro h <;> nlinarith
  · change (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega
          (fkMedialLocalMate pairing b.1))).1 < 0 ↔
        fkRectZeroTurnRemainderSide R omega C = true
    rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate, horbit]
    simp only [Prod.fst_neg, nsmul_eq_mul]
    rw [fkRectZeroTurnRemainderSide_eq_true_iff]
    change -((m : Int) * w.1) < 0 ↔ 0 < w.1
    constructor <;> intro h <;> nlinarith


noncomputable def fkRectRawPrimalCrossingBase
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : R.Vertex :=
  (fkRectLeftColumn R, fkRectRawPrimalCrossingFirstRow R omega X)

theorem fkRectRawPrimalCrossingBase_component
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectRawPrimalCrossingBase R omega X) = X.1 := by
  exact fkRectRawPrimalCrossingFirstRow_component R omega X

theorem fkRectRawPrimalCrossingBase_torusComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectRawPrimalCrossingBase R omega X) =
      fkRectRawPrimalCrossingTorusComponent R omega X := by
  unfold fkRectRawPrimalCrossingTorusComponent
  rw [← fkRectRawPrimalCrossingTorusComponent_mk R omega
    (fkRectRawPrimalCrossingBase R omega X),
    fkRectRawPrimalCrossingBase_component]



noncomputable def fkRectRawPrimalCrossingVerticalPotential
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (y : R.Vertex) : Int := by
  classical
  exact if h : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) y then
    (fkRectWalkWinding R (Classical.choice h)).2
  else 0



theorem fkRectRawPrimalCrossingVerticalPotential_eq_walk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    {y : R.Vertex}
    (p : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingBase R omega X) y) :
    fkRectRawPrimalCrossingVerticalPotential R omega X y =
      (fkRectWalkWinding R p).2 := by
  classical
  unfold fkRectRawPrimalCrossingVerticalPotential
  rw [dif_pos ⟨p⟩]
  let q : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingBase R omega X) y :=
    Classical.choice ⟨p⟩
  have hclosed := fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder
    R omega C (p.append q.reverse)
  rw [fkRectWalkWinding_append, fkRectWalkWinding_reverse] at hclosed
  change (fkRectWalkWinding R p).2 - (fkRectWalkWinding R q).2 = 0 at hclosed
  change (fkRectWalkWinding R q).2 = (fkRectWalkWinding R p).2
  linarith



theorem fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    {x y : R.Vertex}
    (hx : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x)
    (p : (fkRectOpenGraph R omega).Walk x y) :
    fkRectRawPrimalCrossingVerticalPotential R omega X y -
        fkRectRawPrimalCrossingVerticalPotential R omega X x =
      (fkRectWalkWinding R p).2 := by
  let q : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingBase R omega X) x := Classical.choice hx
  have hy : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) y := ⟨q.append p⟩
  rw [fkRectRawPrimalCrossingVerticalPotential_eq_walk R omega C X q,
    fkRectRawPrimalCrossingVerticalPotential_eq_walk R omega C X
      (q.append p),
    fkRectWalkWinding_append]
  ring


noncomputable def fkRectRawPrimalCrossingDevelopedHeight
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (y : R.Vertex) : Int :=
  (y.2.val : Int) + (R.height : Int) *
    fkRectRawPrimalCrossingVerticalPotential R omega X y


noncomputable def fkRectRawPrimalCrossingTorusVertices
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    Finset R.Vertex := by
  classical
  exact Finset.univ.filter fun y =>
    (fkRectOpenGraph R omega).connectedComponentMk y =
      fkRectRawPrimalCrossingTorusComponent R omega X

theorem mem_fkRectRawPrimalCrossingTorusVertices
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (y : R.Vertex) :
    y ∈ fkRectRawPrimalCrossingTorusVertices R omega X ↔
      (fkRectOpenGraph R omega).connectedComponentMk y =
        fkRectRawPrimalCrossingTorusComponent R omega X := by
  classical
  simp [fkRectRawPrimalCrossingTorusVertices]

theorem fkRectRawPrimalCrossingBase_mem_torusVertices
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    fkRectRawPrimalCrossingBase R omega X ∈
      fkRectRawPrimalCrossingTorusVertices R omega X := by
  rw [mem_fkRectRawPrimalCrossingTorusVertices,
    fkRectRawPrimalCrossingBase_torusComponent]

theorem fkRectRawPrimalCrossingTorusVertices_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectRawPrimalCrossingTorusVertices R omega X).Nonempty :=
  ⟨fkRectRawPrimalCrossingBase R omega X,
    fkRectRawPrimalCrossingBase_mem_torusVertices R omega X⟩

theorem fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    {y : R.Vertex}
    (hy : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) y := by
  apply SimpleGraph.ConnectedComponent.exact
  rw [fkRectRawPrimalCrossingBase_torusComponent]
  exact (mem_fkRectRawPrimalCrossingTorusVertices R omega X y).1 hy |>.symm



noncomputable def fkRectRawPrimalCrossingDevelopedHeights
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Finset Int := by
  classical
  exact (fkRectRawPrimalCrossingTorusVertices R omega X).image
    (fkRectRawPrimalCrossingDevelopedHeight R omega X)

theorem fkRectRawPrimalCrossingDevelopedHeights_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectRawPrimalCrossingDevelopedHeights R omega X).Nonempty := by
  obtain ⟨y, hy⟩ := fkRectRawPrimalCrossingTorusVertices_nonempty R omega X
  exact ⟨fkRectRawPrimalCrossingDevelopedHeight R omega X y,
    Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩

noncomputable def fkRectRawPrimalCrossingMinDevelopedHeight
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Int :=
  (fkRectRawPrimalCrossingDevelopedHeights R omega X).min'
    (fkRectRawPrimalCrossingDevelopedHeights_nonempty R omega X)

noncomputable def fkRectRawPrimalCrossingMaxDevelopedHeight
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Int :=
  (fkRectRawPrimalCrossingDevelopedHeights R omega X).max'
    (fkRectRawPrimalCrossingDevelopedHeights_nonempty R omega X)


noncomputable def fkRectRawPrimalCrossingBottomVertexWithSpec
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    {y : R.Vertex //
      y ∈ fkRectRawPrimalCrossingTorusVertices R omega X ∧
      fkRectRawPrimalCrossingDevelopedHeight R omega X y =
        fkRectRawPrimalCrossingMinDevelopedHeight R omega X} := by
  have hmem : fkRectRawPrimalCrossingMinDevelopedHeight R omega X ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.min'_mem _ _
  let hex := Finset.mem_image.mp hmem
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩


noncomputable def fkRectRawPrimalCrossingBottomVertex
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : R.Vertex :=
  fkRectRawPrimalCrossingBottomVertexWithSpec R omega X

theorem fkRectRawPrimalCrossingBottomVertex_spec
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    fkRectRawPrimalCrossingBottomVertex R omega X ∈
        fkRectRawPrimalCrossingTorusVertices R omega X ∧
      fkRectRawPrimalCrossingDevelopedHeight R omega X
          (fkRectRawPrimalCrossingBottomVertex R omega X) =
        fkRectRawPrimalCrossingMinDevelopedHeight R omega X := by
  exact (fkRectRawPrimalCrossingBottomVertexWithSpec R omega X).2


noncomputable def fkRectRawPrimalCrossingTopVertexWithSpec
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    {y : R.Vertex //
      y ∈ fkRectRawPrimalCrossingTorusVertices R omega X ∧
      fkRectRawPrimalCrossingDevelopedHeight R omega X y =
        fkRectRawPrimalCrossingMaxDevelopedHeight R omega X} := by
  have hmem : fkRectRawPrimalCrossingMaxDevelopedHeight R omega X ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.max'_mem _ _
  let hex := Finset.mem_image.mp hmem
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩


noncomputable def fkRectRawPrimalCrossingTopVertex
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : R.Vertex :=
  fkRectRawPrimalCrossingTopVertexWithSpec R omega X

theorem fkRectRawPrimalCrossingTopVertex_spec
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    fkRectRawPrimalCrossingTopVertex R omega X ∈
        fkRectRawPrimalCrossingTorusVertices R omega X ∧
      fkRectRawPrimalCrossingDevelopedHeight R omega X
          (fkRectRawPrimalCrossingTopVertex R omega X) =
        fkRectRawPrimalCrossingMaxDevelopedHeight R omega X := by
  exact (fkRectRawPrimalCrossingTopVertexWithSpec R omega X).2


theorem fkRectRawPrimalCrossingDevelopedHeight_sub_eq_walk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    {x y : R.Vertex}
    (hx : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x)
    (p : (fkRectOpenGraph R omega).Walk x y) :
    fkRectRawPrimalCrossingDevelopedHeight R omega X y -
        fkRectRawPrimalCrossingDevelopedHeight R omega X x =
      (y.2.val : Int) - x.2.val + (R.height : Int) *
        (fkRectWalkWinding R p).2 := by
  unfold fkRectRawPrimalCrossingDevelopedHeight
  have hpot := fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk
    R omega C X hx p
  calc
    (y.2.val : Int) + (R.height : Int) *
          fkRectRawPrimalCrossingVerticalPotential R omega X y -
        ((x.2.val : Int) + (R.height : Int) *
          fkRectRawPrimalCrossingVerticalPotential R omega X x) =
      (y.2.val : Int) - x.2.val + (R.height : Int) *
        (fkRectRawPrimalCrossingVerticalPotential R omega X y -
          fkRectRawPrimalCrossingVerticalPotential R omega X x) := by ring
    _ = _ := by rw [hpot]



theorem fkRectRawPrimalCrossingDevelopedHeight_verticalPred
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (x : R.Vertex)
    (hx : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x)
    (hpred : (fkRectOpenGraph R omega).Adj x
      (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)) :
    fkRectRawPrimalCrossingDevelopedHeight R omega X
        (x.1, SixVertexArrows.cyclicPred R.height_pos x.2) =
      fkRectRawPrimalCrossingDevelopedHeight R omega X x - 1 := by
  let y : R.Vertex :=
    (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
  let p : (fkRectOpenGraph R omega).Walk x y := .cons hpred .nil
  have h := fkRectRawPrimalCrossingDevelopedHeight_sub_eq_walk
    R omega C X hx p
  have hwind : (fkRectWalkWinding R p).2 =
      fkRectVerticalSeamIncrement R x y := by
    simp [p, y, fkRectWalkWinding]
  rw [hwind] at h
  have hinc := fkRectVerticalSeamIncrement_pred R x.1 x.1 x.2
  change fkRectVerticalSeamIncrement R x y =
      (if x.2.val = 0 then -1 else 0) at hinc
  rw [hinc] at h
  have hpredVal := fkRectCyclicPred_val R.height_pos x.2
  change y.2.val =
      (if x.2.val = 0 then R.height - 1 else x.2.val - 1) at hpredVal
  rw [hpredVal] at h
  dsimp only [y] at h ⊢
  split at h <;> omega



theorem fkRectRawPrimalCrossingBottomEdge_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    omega (true, fkRectRawPrimalCrossingBottomVertex R omega X) = false := by
  let x := fkRectRawPrimalCrossingBottomVertex R omega X
  let y : R.Vertex :=
    (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
  let e : R.EdgeIndex := (true, x)
  by_contra hopen
  have hopen' : omega e = true := Bool.eq_true_of_not_eq_false hopen
  have hxy : (fkRectOpenGraph R omega).Adj x y := by
    refine ⟨e, hopen', ?_⟩
    simp [e, x, y, fkRectTorusIndexedEdge]
  have hxmem : x ∈ fkRectRawPrimalCrossingTorusVertices R omega X :=
    (fkRectRawPrimalCrossingBottomVertex_spec R omega X).1
  have hxreach : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x :=
    fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
      R omega X hxmem
  have hymem : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
    rw [mem_fkRectRawPrimalCrossingTorusVertices]
    calc
      (fkRectOpenGraph R omega).connectedComponentMk y =
          (fkRectOpenGraph R omega).connectedComponentMk x :=
        SimpleGraph.ConnectedComponent.sound hxy.symm.reachable
      _ = fkRectRawPrimalCrossingTorusComponent R omega X :=
        (mem_fkRectRawPrimalCrossingTorusVertices R omega X x).1 hxmem
  have hyHeightMem : fkRectRawPrimalCrossingDevelopedHeight R omega X y ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hmin : fkRectRawPrimalCrossingMinDevelopedHeight R omega X ≤
      fkRectRawPrimalCrossingDevelopedHeight R omega X y :=
    Finset.min'_le _ _ hyHeightMem
  have hxheight := (fkRectRawPrimalCrossingBottomVertex_spec R omega X).2
  have hpred := fkRectRawPrimalCrossingDevelopedHeight_verticalPred
    R omega C X x hxreach hxy
  dsimp only [x, y] at hmin hpred
  rw [← hxheight] at hmin
  omega



theorem fkRectRawPrimalCrossingDevelopedHeight_verticalSucc
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (x : R.Vertex)
    (hx : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x)
    (hsucc : (fkRectOpenGraph R omega).Adj x
      (x.1, finitePeriodicSucc R.height_pos x.2)) :
    fkRectRawPrimalCrossingDevelopedHeight R omega X
        (x.1, finitePeriodicSucc R.height_pos x.2) =
      fkRectRawPrimalCrossingDevelopedHeight R omega X x + 1 := by
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  have hy : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) y :=
    hx.trans hsucc.reachable
  have hpred : (fkRectOpenGraph R omega).Adj y
      (y.1, SixVertexArrows.cyclicPred R.height_pos y.2) := by
    simpa [y, svCyclicPred_finitePeriodicSucc] using hsucc.symm
  have h := fkRectRawPrimalCrossingDevelopedHeight_verticalPred
    R omega C X y hy hpred
  simp only [y, svCyclicPred_finitePeriodicSucc] at h
  calc
    fkRectRawPrimalCrossingDevelopedHeight R omega X
          (x.1, finitePeriodicSucc R.height_pos x.2) =
        (fkRectRawPrimalCrossingDevelopedHeight R omega X
          (x.1, finitePeriodicSucc R.height_pos x.2) - 1) + 1 := by ring
    _ = fkRectRawPrimalCrossingDevelopedHeight R omega X x + 1 := by
      rw [← h]

private theorem fkRectVerticalSeamIncrement_succ_back
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectVerticalSeamIncrement R
        ((x.1, finitePeriodicSucc R.height_pos x.2)) x =
      if x.2.val + 1 = R.height then -1 else 0 := by
  unfold fkRectVerticalSeamIncrement
  rw [finitePeriodicSucc_val]
  have hgt := R.height_gt_two
  have hlt := x.2.isLt
  by_cases hwrap : x.2.val + 1 = R.height
  · simp [hwrap]
    omega
  · simp [hwrap]
    omega

private theorem fkRectVerticalSeamIncrement_pred_forward
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectVerticalSeamIncrement R
        ((x.1, SixVertexArrows.cyclicPred R.height_pos x.2)) x =
      if x.2.val = 0 then 1 else 0 := by
  unfold fkRectVerticalSeamIncrement
  rw [fkRectCyclicPred_val]
  have hgt := R.height_gt_two
  have hlt := x.2.isLt
  by_cases hzero : x.2.val = 0
  · simp [hzero]
    omega
  · simp [hzero]
    omega




theorem fkRectRawPrimalCrossingTopClosing_verticalWinding_neg
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (p : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingTopVertex R omega X)
      ((fkRectRawPrimalCrossingTopVertex R omega X).1,
        finitePeriodicSucc R.height_pos
          (fkRectRawPrimalCrossingTopVertex R omega X).2)) :
    (fkRectWalkWinding R p).2 +
        fkRectVerticalSeamIncrement R
          ((fkRectRawPrimalCrossingTopVertex R omega X).1,
            finitePeriodicSucc R.height_pos
              (fkRectRawPrimalCrossingTopVertex R omega X).2)
          (fkRectRawPrimalCrossingTopVertex R omega X) < 0 := by
  let x := fkRectRawPrimalCrossingTopVertex R omega X
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  have hxmem : x ∈ fkRectRawPrimalCrossingTorusVertices R omega X :=
    (fkRectRawPrimalCrossingTopVertex_spec R omega X).1
  have hxreach : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x :=
    fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
      R omega X hxmem
  have hymem : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
    rw [mem_fkRectRawPrimalCrossingTorusVertices]
    calc
      (fkRectOpenGraph R omega).connectedComponentMk y =
          (fkRectOpenGraph R omega).connectedComponentMk x :=
        SimpleGraph.ConnectedComponent.sound ⟨p.reverse⟩
      _ = fkRectRawPrimalCrossingTorusComponent R omega X :=
        (mem_fkRectRawPrimalCrossingTorusVertices R omega X x).1 hxmem
  have hyHeightMem : fkRectRawPrimalCrossingDevelopedHeight R omega X y ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hmax : fkRectRawPrimalCrossingDevelopedHeight R omega X y ≤
      fkRectRawPrimalCrossingMaxDevelopedHeight R omega X :=
    Finset.le_max' _ _ hyHeightMem
  have hxheight := (fkRectRawPrimalCrossingTopVertex_spec R omega X).2
  have hpot := fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk
    R omega C X hxreach p
  dsimp only [x, y] at hmax hpot ⊢
  rw [← hxheight] at hmax
  unfold fkRectRawPrimalCrossingDevelopedHeight at hmax
  have hpot' :
      fkRectRawPrimalCrossingVerticalPotential R omega X
          ((fkRectRawPrimalCrossingTopVertex R omega X).1,
            finitePeriodicSucc R.height_pos
              (fkRectRawPrimalCrossingTopVertex R omega X).2) =
        (fkRectWalkWinding R p).2 +
          fkRectRawPrimalCrossingVerticalPotential R omega X
            (fkRectRawPrimalCrossingTopVertex R omega X) := by
    linarith
  rw [hpot'] at hmax
  have hheight : (0 : Int) < R.height := by exact_mod_cast R.height_pos
  by_cases hwrap :
    (fkRectRawPrimalCrossingTopVertex R omega X).2.val + 1 = R.height
  · have hinc := fkRectVerticalSeamIncrement_succ_back R
      (fkRectRawPrimalCrossingTopVertex R omega X)
    rw [if_pos hwrap] at hinc
    simp [finitePeriodicSucc_val, hwrap] at hmax
    rw [hinc]
    ring_nf at hmax
    nlinarith
  · have hinc := fkRectVerticalSeamIncrement_succ_back R
      (fkRectRawPrimalCrossingTopVertex R omega X)
    rw [if_neg hwrap] at hinc
    simp [finitePeriodicSucc_val, hwrap] at hmax
    rw [hinc]
    ring_nf at hmax
    nlinarith




theorem fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (p : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingBottomVertex R omega X)
      ((fkRectRawPrimalCrossingBottomVertex R omega X).1,
        SixVertexArrows.cyclicPred R.height_pos
          (fkRectRawPrimalCrossingBottomVertex R omega X).2)) :
    0 < (fkRectWalkWinding R p).2 +
        fkRectVerticalSeamIncrement R
          ((fkRectRawPrimalCrossingBottomVertex R omega X).1,
            SixVertexArrows.cyclicPred R.height_pos
              (fkRectRawPrimalCrossingBottomVertex R omega X).2)
          (fkRectRawPrimalCrossingBottomVertex R omega X) := by
  let x := fkRectRawPrimalCrossingBottomVertex R omega X
  let y : R.Vertex :=
    (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
  have hxmem : x ∈ fkRectRawPrimalCrossingTorusVertices R omega X :=
    (fkRectRawPrimalCrossingBottomVertex_spec R omega X).1
  have hxreach : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x :=
    fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
      R omega X hxmem
  have hymem : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
    rw [mem_fkRectRawPrimalCrossingTorusVertices]
    calc
      (fkRectOpenGraph R omega).connectedComponentMk y =
          (fkRectOpenGraph R omega).connectedComponentMk x :=
        SimpleGraph.ConnectedComponent.sound ⟨p.reverse⟩
      _ = fkRectRawPrimalCrossingTorusComponent R omega X :=
        (mem_fkRectRawPrimalCrossingTorusVertices R omega X x).1 hxmem
  have hyHeightMem : fkRectRawPrimalCrossingDevelopedHeight R omega X y ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hmin : fkRectRawPrimalCrossingMinDevelopedHeight R omega X ≤
      fkRectRawPrimalCrossingDevelopedHeight R omega X y :=
    Finset.min'_le _ _ hyHeightMem
  have hxheight := (fkRectRawPrimalCrossingBottomVertex_spec R omega X).2
  have hpot := fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk
    R omega C X hxreach p
  dsimp only [x, y] at hmin hpot ⊢
  rw [← hxheight] at hmin
  unfold fkRectRawPrimalCrossingDevelopedHeight at hmin
  have hpot' :
      fkRectRawPrimalCrossingVerticalPotential R omega X
          ((fkRectRawPrimalCrossingBottomVertex R omega X).1,
            SixVertexArrows.cyclicPred R.height_pos
              (fkRectRawPrimalCrossingBottomVertex R omega X).2) =
        (fkRectWalkWinding R p).2 +
          fkRectRawPrimalCrossingVerticalPotential R omega X
            (fkRectRawPrimalCrossingBottomVertex R omega X) := by
    linarith
  rw [hpot'] at hmin
  have hheight : (0 : Int) < R.height := by exact_mod_cast R.height_pos
  by_cases hzero :
    (fkRectRawPrimalCrossingBottomVertex R omega X).2.val = 0
  · have hinc := fkRectVerticalSeamIncrement_pred_forward R
      (fkRectRawPrimalCrossingBottomVertex R omega X)
    rw [if_pos hzero] at hinc
    simp [fkRectCyclicPred_val, hzero] at hmin
    rw [Nat.cast_sub (by omega : 1 ≤ R.height)] at hmin
    norm_num at hmin
    rw [hinc]
    ring_nf at hmin
    nlinarith
  · have hinc := fkRectVerticalSeamIncrement_pred_forward R
      (fkRectRawPrimalCrossingBottomVertex R omega X)
    rw [if_neg hzero] at hinc
    simp [fkRectCyclicPred_val, hzero] at hmin
    have hpos : 1 ≤
        (fkRectRawPrimalCrossingBottomVertex R omega X).2.val := by omega
    rw [Nat.cast_sub hpos] at hmin
    norm_num at hmin
    rw [hinc]
    ring_nf at hmin
    nlinarith



theorem fkRectRawPrimalCrossingTopEdge_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    omega (true,
      ((fkRectRawPrimalCrossingTopVertex R omega X).1,
        finitePeriodicSucc R.height_pos
          (fkRectRawPrimalCrossingTopVertex R omega X).2)) = false := by
  let x := fkRectRawPrimalCrossingTopVertex R omega X
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  let e : R.EdgeIndex := (true, y)
  by_contra hopen
  have hopen' : omega e = true := Bool.eq_true_of_not_eq_false hopen
  have hxy : (fkRectOpenGraph R omega).Adj x y := by
    refine ⟨e, hopen', ?_⟩
    simp [e, x, y, fkRectTorusIndexedEdge,
      svCyclicPred_finitePeriodicSucc]
  have hxmem : x ∈ fkRectRawPrimalCrossingTorusVertices R omega X :=
    (fkRectRawPrimalCrossingTopVertex_spec R omega X).1
  have hxreach : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x :=
    fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
      R omega X hxmem
  have hymem : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
    rw [mem_fkRectRawPrimalCrossingTorusVertices]
    calc
      (fkRectOpenGraph R omega).connectedComponentMk y =
          (fkRectOpenGraph R omega).connectedComponentMk x :=
        SimpleGraph.ConnectedComponent.sound hxy.symm.reachable
      _ = fkRectRawPrimalCrossingTorusComponent R omega X :=
        (mem_fkRectRawPrimalCrossingTorusVertices R omega X x).1 hxmem
  have hyHeightMem : fkRectRawPrimalCrossingDevelopedHeight R omega X y ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hmax : fkRectRawPrimalCrossingDevelopedHeight R omega X y ≤
      fkRectRawPrimalCrossingMaxDevelopedHeight R omega X :=
    Finset.le_max' _ _ hyHeightMem
  have hxheight := (fkRectRawPrimalCrossingTopVertex_spec R omega X).2
  have hsucc := fkRectRawPrimalCrossingDevelopedHeight_verticalSucc
    R omega C X x hxreach hxy
  dsimp only [x, y] at hmax hsucc
  rw [← hxheight] at hmax
  omega



def fkRectMedialDartAbovePrimalVertex
    (R : FKRectTorus) (x : R.Vertex) : FKMedialDart R.medialTorus :=
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  let e : R.EdgeIndex := (true, y)
  if Even y.2.val then
    fkMedialEastDart (fkRectMedialVertexOfEdge R e)
  else
    fkMedialWestDart (fkRectMedialVertexOfEdge R e)

@[simp] theorem fkRectMedialDartAbovePrimalVertex_label
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectMedialDartPrimalLabel R
      (fkRectMedialDartAbovePrimalVertex R x) = x := by
  unfold fkRectMedialDartAbovePrimalVertex
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  by_cases hy : Even y.2.val
  · simp [fkRectMedialEastPrimal, y, hy,
      svCyclicPred_finitePeriodicSucc]
  · simp [fkRectMedialWestPrimal, y, hy,
      svCyclicPred_finitePeriodicSucc]



noncomputable def fkRectRawPrimalCrossingDevelopedExtremeDart
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) : FKMedialDart R.medialTorus :=
  if side then
    fkRectMedialDartAbovePrimalVertex R
      (fkRectRawPrimalCrossingTopVertex R omega X)
  else
    fkRectMedialDartAtPrimalVertex R
      (fkRectRawPrimalCrossingBottomVertex R omega X)

@[simp] theorem fkRectRawPrimalCrossingDevelopedExtremeDart_label
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    fkRectMedialDartPrimalLabel R
        (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) =
      if side then fkRectRawPrimalCrossingTopVertex R omega X
      else fkRectRawPrimalCrossingBottomVertex R omega X := by
  cases side <;> simp [fkRectRawPrimalCrossingDevelopedExtremeDart]



theorem fkRectRawPrimalCrossingDevelopedExtremeDart_primalComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    fkRectMedialComponentToPrimalComponent R omega
        ((fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
            (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side)) =
      fkRectRawPrimalCrossingTorusComponent R omega X := by
  rw [fkRectMedialComponentToPrimalComponent_mk,
    fkRectRawPrimalCrossingDevelopedExtremeDart_label]
  cases side
  · exact (mem_fkRectRawPrimalCrossingTorusVertices R omega X _).1
      (fkRectRawPrimalCrossingBottomVertex_spec R omega X).1
  · exact (mem_fkRectRawPrimalCrossingTorusVertices R omega X _).1
      (fkRectRawPrimalCrossingTopVertex_spec R omega X).1



theorem fkRectRawPrimalCrossingDevelopedExtremeDart_matches_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C) :
    fkRectMedialComponentToPrimalComponent R omega
        ((fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
            (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
              (fkRectZeroTurnRemainderSide R omega C))) =
      fkRectZeroTurnRemainderPrimalComponent R omega C := by
  rw [fkRectRawPrimalCrossingDevelopedExtremeDart_primalComponent]
  exact fkRectZeroTurnPrimalTouchedCrossing_matches R omega C X hX




def FKRectZeroTurnPrimalDevelopedExtremeIncidence
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega),
    X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C →
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
            (fkRectZeroTurnRemainderSide R omega C)) = C.1



theorem fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (hincidence : FKRectZeroTurnPrimalDevelopedExtremeIncidence R omega)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hXC : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C)
    (hXD : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega D)
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) : C = D := by
  apply Subtype.ext
  rw [← hincidence C X hXC, ← hincidence D X hXD, hside]

end

end StatMech.FrontierD
