/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.KacWardFormalMultiaffine

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Onsager



theorem kwSpinorGraphLoopWeight_loopRev
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (hphase : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        phase next.symm dart.symm = (phase dart next)⁻¹)
    (hloopSq : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart),
      (∀ k : Fin n, G.DartAdj (loop k) (loop (k + 1)) ∧
        (loop k).edge ≠ (loop (k + 1)).edge) →
      (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1)
    {n : Nat} [NeZero n] (weight : Sym2 V → Complex)
    (loop : Fin n → G.Dart) :
    ons_loopWeight (kwGraphTransition G weight phase)
        (ons_involutiveLoopRev SimpleGraph.Dart.symm loop) =
      ons_loopWeight (kwGraphTransition G weight phase) loop := by
  let reversed := ons_involutiveLoopRev SimpleGraph.Dart.symm loop
  let adjacencyProduct : (Fin n → G.Dart) → Complex := fun path ↦
    ∏ k, kwGraphNonbacktrackingFactor G (path k) (path (k + 1))
  let reflected : Equiv.Perm (Fin n) :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  have hadjacency : adjacencyProduct reversed = adjacencyProduct loop := by
    change (∏ k, kwGraphNonbacktrackingFactor G
      (loop (-k)).symm (loop (-(k + 1))).symm) = _
    calc
      (∏ k, kwGraphNonbacktrackingFactor G
          (loop (-k)).symm (loop (-(k + 1))).symm) =
          ∏ k, kwGraphNonbacktrackingFactor G
            (loop (-(k + 1))) (loop (-k)) := by
        apply Finset.prod_congr rfl
        intro k _
        exact kwGraphNonbacktrackingFactor_reverse G _ _
      _ = ∏ k, kwGraphNonbacktrackingFactor G
          (loop (reflected k)) (loop (reflected k + 1)) := by
        apply Finset.prod_congr rfl
        intro k _
        congr 2
        change -k = -(k + 1) + 1
        abel
      _ = adjacencyProduct loop := Equiv.prod_comp reflected
        (fun k ↦ kwGraphNonbacktrackingFactor G
          (loop k) (loop (k + 1)))
  have hexponent : kwGraphLoopExponent G reversed =
      kwGraphLoopExponent G loop := by
    unfold kwGraphLoopExponent reversed
    simp only [ons_involutiveLoopRev, SimpleGraph.Dart.edge_symm]
    exact Equiv.sum_comp (Equiv.neg (Fin n))
      (fun k ↦ Finsupp.single (loop k).edge 1)
  have hscalar : kwGraphLoopScalar G phase reversed =
      kwGraphLoopScalar G phase loop := by
    by_cases hzero : adjacencyProduct loop = 0
    · rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
        kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
      change adjacencyProduct reversed * _ = adjacencyProduct loop * _
      rw [hadjacency, hzero]
      ring
    · have hvalid : ∀ k : Fin n,
          G.DartAdj (loop k) (loop (k + 1)) ∧
            (loop k).edge ≠ (loop (k + 1)).edge := by
        intro k
        have hfactor : kwGraphNonbacktrackingFactor G
            (loop k) (loop (k + 1)) ≠ 0 := by
          intro hk
          apply hzero
          apply Finset.prod_eq_zero (Finset.mem_univ k)
          exact hk
        by_contra hstep
        simp [kwGraphNonbacktrackingFactor, hstep] at hfactor
      have hphaseProduct := kwLoopPhaseProduct_involutiveLoopRev
        SimpleGraph.Dart.symm phase loop
        (fun k ↦ hphase _ _ (hvalid k).1 (hvalid k).2)
        (hloopSq loop hvalid)
      rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
        kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
      change adjacencyProduct reversed * _ = adjacencyProduct loop * _
      have hp : (∏ k, phase (reversed k) (reversed (k + 1))) =
          ∏ k, phase (loop k) (loop (k + 1)) := by
        simpa only [kwLoopPhaseProduct, reversed] using hphaseProduct
      rw [hadjacency, hp]
  rw [kwGraphLoopWeight_factor, kwGraphLoopWeight_factor,
    hexponent, hscalar]



theorem kwSpinorGraph_bothOrientation_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (hpathSq : ∀ {N : Nat} (path : Fin (N + 1) → G.Dart),
      path (Fin.last N) = (path 0).symm →
        (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧
          (path j.castSucc).edge ≠ (path j.succ).edge) →
        (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
    (hphase : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        phase next.symm dart.symm = (phase dart next)⁻¹)
    {n : Nat} [NeZero n] (weight : Sym2 V → Complex)
    (selected : G.Dart) :
    (∑ loop ∈ ons_loopSetBoth (n := n) selected selected.symm,
      ons_loopWeight (kwGraphTransition G weight phase) loop) = 0 := by
  apply ons_sum_zero_of_sign_involution'
    (kwGraphTransition G weight phase)
    (ons_loopSetBoth (n := n) selected selected.symm)
    (ons_surgery selected SimpleGraph.Dart.symm)
  · intro loop hloop
    apply (ons_mem_loopSetBoth selected selected.symm _).mpr
    exact ons_surgery_visitsBoth SimpleGraph.Dart.symm_involutive
      (SimpleGraph.Dart.symm_ne selected)
      ((ons_mem_loopSetBoth selected selected.symm loop).mp hloop)
  · intro loop hloop
    exact kwGraphLoopWeight_surgery_sign G weight phase hpathSq hphase
      selected loop ((ons_mem_loopSetBoth selected selected.symm loop).mp hloop)
  · intro loop hloop
    exact ons_surgery_involutive SimpleGraph.Dart.symm_involutive
      (SimpleGraph.Dart.symm_ne selected)
      ((ons_mem_loopSetBoth selected selected.symm loop).mp hloop)


theorem kwSpinorGraph_oneOrientation_sum_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (hphase : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        phase next.symm dart.symm = (phase dart next)⁻¹)
    (hloopSq : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart),
      (∀ k : Fin n, G.DartAdj (loop k) (loop (k + 1)) ∧
        (loop k).edge ≠ (loop (k + 1)).edge) →
      (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1)
    {n : Nat} [NeZero n] (weight : Sym2 V → Complex)
    (selected : G.Dart) :
    (∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → G.Dart ↦
          (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm),
      ons_loopWeight (kwGraphTransition G weight phase) loop) =
      ∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → G.Dart ↦
          (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected),
        ons_loopWeight (kwGraphTransition G weight phase) loop := by
  apply ons_matrixLoopSum_orientation_symm_of_loopRev
    SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive _ _ selected
  intro loop
  exact kwSpinorGraphLoopWeight_loopRev G phase hphase hloopSq weight loop



theorem kwPrincipalAngleGraphLoopWeight_loopRev
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : G.Dart → Real.Angle)
    (hangle : ∀ dart,
      angle dart.symm = angle dart + (Real.pi : Real.Angle))
    (hnonantipodal : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        angle next - angle dart ≠ (Real.pi : Real.Angle))
    {n : Nat} [NeZero n] (weight : Sym2 V → Complex)
    (loop : Fin n → G.Dart) :
    ons_loopWeight
        (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle))
        (ons_involutiveLoopRev SimpleGraph.Dart.symm loop) =
      ons_loopWeight
        (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop := by
  let reversed := ons_involutiveLoopRev SimpleGraph.Dart.symm loop
  let adjacencyProduct : (Fin n → G.Dart) → Complex := fun path ↦
    ∏ k, kwGraphNonbacktrackingFactor G (path k) (path (k + 1))
  let reflected : Equiv.Perm (Fin n) :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  have hadjacency : adjacencyProduct reversed = adjacencyProduct loop := by
    change (∏ k, kwGraphNonbacktrackingFactor G
      (loop (-k)).symm (loop (-(k + 1))).symm) = _
    calc
      (∏ k, kwGraphNonbacktrackingFactor G
          (loop (-k)).symm (loop (-(k + 1))).symm) =
          ∏ k, kwGraphNonbacktrackingFactor G
            (loop (-(k + 1))) (loop (-k)) := by
        apply Finset.prod_congr rfl
        intro k _
        exact kwGraphNonbacktrackingFactor_reverse G _ _
      _ = ∏ k, kwGraphNonbacktrackingFactor G
          (loop (reflected k)) (loop (reflected k + 1)) := by
        apply Finset.prod_congr rfl
        intro k _
        congr 2
        change -k = -(k + 1) + 1
        abel
      _ = adjacencyProduct loop := Equiv.prod_comp reflected
        (fun k ↦ kwGraphNonbacktrackingFactor G
          (loop k) (loop (k + 1)))
  have hexponent : kwGraphLoopExponent G reversed =
      kwGraphLoopExponent G loop := by
    unfold kwGraphLoopExponent reversed
    simp only [ons_involutiveLoopRev, SimpleGraph.Dart.edge_symm]
    exact Equiv.sum_comp (Equiv.neg (Fin n))
      (fun k ↦ Finsupp.single (loop k).edge 1)
  have hscalar :
      kwGraphLoopScalar G (kwPrincipalHalfAnglePhase angle) reversed =
        kwGraphLoopScalar G (kwPrincipalHalfAnglePhase angle) loop := by
    by_cases hzero : adjacencyProduct loop = 0
    · rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
        kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
      change adjacencyProduct reversed * _ = adjacencyProduct loop * _
      rw [hadjacency, hzero]
      ring
    · have hvalid : ∀ k : Fin n,
          G.DartAdj (loop k) (loop (k + 1)) ∧
            (loop k).edge ≠ (loop (k + 1)).edge := by
        intro k
        have hfactor : kwGraphNonbacktrackingFactor G
            (loop k) (loop (k + 1)) ≠ 0 := by
          intro hk
          apply hzero
          apply Finset.prod_eq_zero (Finset.mem_univ k)
          exact hk
        by_contra hstep
        simp [kwGraphNonbacktrackingFactor, hstep] at hfactor
      have hphaseProduct :=
        kwLoopPhaseProduct_principal_involutiveLoopRev
          SimpleGraph.Dart.symm angle hangle loop
          (fun k ↦ hnonantipodal _ _ (hvalid k).1 (hvalid k).2)
      rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
        kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
      change adjacencyProduct reversed * _ = adjacencyProduct loop * _
      have hp :
          (∏ k, kwPrincipalHalfAnglePhase angle
            (reversed k) (reversed (k + 1))) =
          ∏ k, kwPrincipalHalfAnglePhase angle
            (loop k) (loop (k + 1)) := by
        simpa only [kwLoopPhaseProduct, reversed] using hphaseProduct
      rw [hadjacency, hp]
  rw [kwGraphLoopWeight_factor, kwGraphLoopWeight_factor,
    hexponent, hscalar]

theorem kwPrincipalAngleGraph_bothOrientation_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : G.Dart → Real.Angle)
    (hangle : ∀ dart,
      angle dart.symm = angle dart + (Real.pi : Real.Angle))
    (hnonantipodal : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        angle next - angle dart ≠ (Real.pi : Real.Angle))
    {n : Nat} [NeZero n] (weight : Sym2 V → Complex)
    (selected : G.Dart) :
    (∑ loop ∈ ons_loopSetBoth (n := n) selected selected.symm,
      ons_loopWeight
        (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop) = 0 := by
  apply ons_sum_zero_of_sign_involution'
    (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle))
    (ons_loopSetBoth (n := n) selected selected.symm)
    (ons_surgery selected SimpleGraph.Dart.symm)
  · intro loop hloop
    apply (ons_mem_loopSetBoth selected selected.symm _).mpr
    exact ons_surgery_visitsBoth SimpleGraph.Dart.symm_involutive
      (SimpleGraph.Dart.symm_ne selected)
      ((ons_mem_loopSetBoth selected selected.symm loop).mp hloop)
  · intro loop hloop
    exact kwGraphLoopWeight_principal_surgery_sign
      G weight angle hangle hnonantipodal selected loop
        ((ons_mem_loopSetBoth selected selected.symm loop).mp hloop)
  · intro loop hloop
    exact ons_surgery_involutive SimpleGraph.Dart.symm_involutive
      (SimpleGraph.Dart.symm_ne selected)
      ((ons_mem_loopSetBoth selected selected.symm loop).mp hloop)

theorem kwPrincipalAngleGraph_oneOrientation_sum_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : G.Dart → Real.Angle)
    (hangle : ∀ dart,
      angle dart.symm = angle dart + (Real.pi : Real.Angle))
    (hnonantipodal : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        angle next - angle dart ≠ (Real.pi : Real.Angle))
    {n : Nat} [NeZero n] (weight : Sym2 V → Complex)
    (selected : G.Dart) :
    (∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → G.Dart ↦
          (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm),
      ons_loopWeight
        (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop) =
      ∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → G.Dart ↦
          (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected),
        ons_loopWeight
          (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop := by
  apply ons_matrixLoopSum_orientation_symm_of_loopRev
    SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive _ _ selected
  intro loop
  exact kwPrincipalAngleGraphLoopWeight_loopRev
    G angle hangle hnonantipodal weight loop



theorem kwSpinorGraph_detWalkRoot_scaleEdge_affine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (hpathSq : ∀ {N : Nat} (path : Fin (N + 1) → G.Dart),
      path (Fin.last N) = (path 0).symm →
        (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧
          (path j.castSucc).edge ≠ (path j.succ).edge) →
        (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
    (hphase : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        phase next.symm dart.symm = (phase dart next)⁻¹)
    (hloopSq : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart),
      (∀ k : Fin n, G.DartAdj (loop k) (loop (k + 1)) ∧
        (loop k).edge ≠ (loop (k + 1)).edge) →
      (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1)
    (weight : Sym2 V → Complex) (selected : G.Dart) (t : Complex)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t
        (kwGraphTransition G weight phase) dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : Real) * q < 1) :
    ons_detWalkRoot
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t) phase) =
      ons_detWalkRoot
          (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight phase)) *
        (1 - t * ∑' path, ons_firstReturnWeight
          (kwGraphTransition G weight phase) selected selected.symm path) := by
  let M := kwGraphTransition G weight phase
  let scaledWeight := kwScaleGraphEdgeWeight weight selected.edge t
  let Ms := kwGraphTransition G scaledWeight phase
  let Mt := ons_scaleColumns
    ({selected, selected.symm} : Finset G.Dart) t M
  have hboth : ∀ n : Nat,
      (∑ loop ∈ ons_loopSetBoth (n := n + 1) selected selected.symm,
        ons_loopWeight Mt loop) = 0 := by
    intro n
    calc
      (∑ loop ∈ ons_loopSetBoth (n := n + 1) selected selected.symm,
          ons_loopWeight Mt loop) =
          ∑ loop ∈ ons_loopSetBoth (n := n + 1) selected selected.symm,
            ons_loopWeight Ms loop := by
        apply Finset.sum_congr rfl
        intro loop _
        exact (kw_loopWeight_scaleGraphEdge_eq_scaleColumns
          G weight phase selected t loop).symm
      _ = 0 := kwSpinorGraph_bothOrientation_sum_zero
        G phase hpathSq hphase scaledWeight selected
  have hloopRev : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart),
      ons_loopWeight Mt
          (ons_involutiveLoopRev SimpleGraph.Dart.symm loop) =
        ons_loopWeight Mt loop := by
    intro n hn loop
    rw [← kw_loopWeight_scaleGraphEdge_eq_scaleColumns
        G weight phase selected t,
      ← kw_loopWeight_scaleGraphEdge_eq_scaleColumns
        G weight phase selected t]
    exact kwSpinorGraphLoopWeight_loopRev
      G phase hphase hloopSq scaledWeight loop
  have hsymm : ∀ n : Nat,
      (∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → G.Dart ↦
            (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm),
        ons_loopWeight Mt loop) =
        ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → G.Dart ↦
            (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected),
          ons_loopWeight Mt loop := by
    intro n
    apply ons_matrixLoopSum_orientation_symm_of_loopRev
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive Mt
        (fun loop ↦ hloopRev loop) selected
  have hdelete := ons_detWalkRoot_matrix_delete_pair
    Mt selected selected.symm (SimpleGraph.Dart.symm_ne selected).symm
      q hq hentry hsmall hcard hboth hsymm
  have hmask :
      ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) Mt =
        ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) M := by
    ext dart next
    simp only [Mt, ons_maskMatrix, ons_scaleColumns,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hforbidden :
        (dart = selected ∨ dart = selected.symm) ∨
          next = selected ∨ next = selected.symm
    · simp [hforbidden]
    · have hnext : ¬(next = selected ∨ next = selected.symm) := by tauto
      simp [hnext]
  have hfirst :
      (∑' path, ons_firstReturnWeight Mt selected selected.symm path) =
        t * ∑' path, ons_firstReturnWeight M selected selected.symm path := by
    exact ons_tsum_firstReturnWeight_scale M selected selected.symm t
  rw [kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns]
  change ons_detWalkRoot Mt = _
  rw [hdelete, hmask, hfirst]



theorem kw_spinorGraph_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → Complex)
    (hpathSq : ∀ {N : Nat} (path : Fin (N + 1) → G.Dart),
      path (Fin.last N) = (path 0).symm →
        (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧
          (path j.castSucc).edge ≠ (path j.succ).edge) →
        (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
    (hphase : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        phase next.symm dart.symm = (phase dart next)⁻¹)
    (hloopSq : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart),
      (∀ k : Fin n, G.DartAdj (loop k) (loop (k + 1)) ∧
        (loop k).edge ≠ (loop (k + 1)).edge) →
      (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1)
    (selected : G.Dart) (m : Sym2 V →₀ Nat)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0 := by
  apply kwGraph_formalRoot_coeff_eq_zero_of_repeated_of_scaleEdge_affine
    G phase selected m hrepeated
  intro weight t q hq hentry hsmall hcard
  exact kwSpinorGraph_detWalkRoot_scaleEdge_affine
    G phase hpathSq hphase hloopSq weight selected t q
      hq hentry hsmall hcard



theorem kwPrincipalAngleGraph_detWalkRoot_scaleEdge_affine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : G.Dart → Real.Angle)
    (hangle : ∀ dart,
      angle dart.symm = angle dart + (Real.pi : Real.Angle))
    (hnonantipodal : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        angle next - angle dart ≠ (Real.pi : Real.Angle))
    (weight : Sym2 V → Complex) (selected : G.Dart) (t : Complex)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t
        (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle))
          dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : Real) * q < 1) :
    ons_detWalkRoot
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t)
          (kwPrincipalHalfAnglePhase angle)) =
      ons_detWalkRoot
          (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight
              (kwPrincipalHalfAnglePhase angle))) *
        (1 - t * ∑' path, ons_firstReturnWeight
          (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle))
          selected selected.symm path) := by
  let phase := kwPrincipalHalfAnglePhase angle
  let M := kwGraphTransition G weight phase
  let scaledWeight := kwScaleGraphEdgeWeight weight selected.edge t
  let Ms := kwGraphTransition G scaledWeight phase
  let Mt := ons_scaleColumns
    ({selected, selected.symm} : Finset G.Dart) t M
  have hboth : ∀ n : Nat,
      (∑ loop ∈ ons_loopSetBoth (n := n + 1) selected selected.symm,
        ons_loopWeight Mt loop) = 0 := by
    intro n
    calc
      (∑ loop ∈ ons_loopSetBoth (n := n + 1) selected selected.symm,
          ons_loopWeight Mt loop) =
          ∑ loop ∈ ons_loopSetBoth (n := n + 1) selected selected.symm,
            ons_loopWeight Ms loop := by
        apply Finset.sum_congr rfl
        intro loop _
        exact (kw_loopWeight_scaleGraphEdge_eq_scaleColumns
          G weight phase selected t loop).symm
      _ = 0 := kwPrincipalAngleGraph_bothOrientation_sum_zero
        G angle hangle hnonantipodal scaledWeight selected
  have hloopRev : ∀ {n : Nat} [NeZero n] (loop : Fin n → G.Dart),
      ons_loopWeight Mt
          (ons_involutiveLoopRev SimpleGraph.Dart.symm loop) =
        ons_loopWeight Mt loop := by
    intro n hn loop
    rw [← kw_loopWeight_scaleGraphEdge_eq_scaleColumns
        G weight phase selected t,
      ← kw_loopWeight_scaleGraphEdge_eq_scaleColumns
        G weight phase selected t]
    exact kwPrincipalAngleGraphLoopWeight_loopRev
      G angle hangle hnonantipodal scaledWeight loop
  have hsymm : ∀ n : Nat,
      (∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → G.Dart ↦
            (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm),
        ons_loopWeight Mt loop) =
        ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → G.Dart ↦
            (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected),
          ons_loopWeight Mt loop := by
    intro n
    apply ons_matrixLoopSum_orientation_symm_of_loopRev
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive Mt
        (fun loop ↦ hloopRev loop) selected
  have hdelete := ons_detWalkRoot_matrix_delete_pair
    Mt selected selected.symm (SimpleGraph.Dart.symm_ne selected).symm
      q hq hentry hsmall hcard hboth hsymm
  have hmask :
      ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) Mt =
        ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) M := by
    ext dart next
    simp only [Mt, ons_maskMatrix, ons_scaleColumns,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hforbidden :
        (dart = selected ∨ dart = selected.symm) ∨
          next = selected ∨ next = selected.symm
    · simp [hforbidden]
    · have hnext : ¬(next = selected ∨ next = selected.symm) := by tauto
      simp [hnext]
  have hfirst :
      (∑' path, ons_firstReturnWeight Mt selected selected.symm path) =
        t * ∑' path, ons_firstReturnWeight M
          selected selected.symm path := by
    exact ons_tsum_firstReturnWeight_scale M selected selected.symm t
  rw [kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns]
  change ons_detWalkRoot Mt = _
  rw [hdelete, hmask, hfirst]


theorem kw_principalAngleGraph_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : G.Dart → Real.Angle)
    (hangle : ∀ dart,
      angle dart.symm = angle dart + (Real.pi : Real.Angle))
    (hnonantipodal : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        angle next - angle dart ≠ (Real.pi : Real.Angle))
    (selected : G.Dart) (m : Sym2 V →₀ Nat)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (kwPrincipalHalfAnglePhase angle)) = 0 := by
  apply kwGraph_formalRoot_coeff_eq_zero_of_repeated_of_scaleEdge_affine
    G (kwPrincipalHalfAnglePhase angle) selected m hrepeated
  intro weight t q hq hentry hsmall hcard
  exact kwPrincipalAngleGraph_detWalkRoot_scaleEdge_affine
    G angle hangle hnonantipodal weight selected t q
      hq hentry hsmall hcard

end StatMech.FrontierA
