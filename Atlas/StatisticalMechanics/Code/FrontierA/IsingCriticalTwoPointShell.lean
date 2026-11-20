/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingCriticalSimonMass
import Code.FrontierA.IsingCriticalTwoPointReduction
import Code.FrontierB.CurrentContinuityFreeLeftContinuous
import Code.FrontierB.CurrentContinuityMagnetizationFK

open Finset MeasureTheory Set

namespace StatMech.FrontierA

open Ising Lattice Percolation Sharpness
open StatMech.FrontierB



theorem isingExpectation_instance_irrel
    {V : Type*} (i j : Fintype V) (deqI deqJ : DecidableEq V)
    (G : SimpleGraph V) (adjI adjJ : DecidableRel G.Adj)
    (beta h : Real) (f : ConfigSpace V → Real) :
    @isingExpectation V i deqI G adjI beta h f =
      @isingExpectation V j deqJ G adjJ beta h f := by
  have hi : i = j := Subsingleton.elim _ _
  subst j
  have hdeq : deqI = deqJ := Subsingleton.elim _ _
  subst deqJ
  have hadj : adjI = adjJ := Subsingleton.elim _ _
  subst adjJ
  rfl



theorem corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint
    (d n : Nat) (beta : Real) (x : Site d)
    (hx : x ∈ box d n) (hxo : x ≠ Percolation.origin d) :
    corrOriginInner d beta (boxSV_boxF d n) x =
      currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) x := by
  classical
  have h0 : Percolation.origin d ∈ boxSV_boxF d n := by
    change Percolation.origin d ∈ (boxSV_boxF d n : Set (Site d))
    rw [boxSV_coe_boxF]
    exact origin_mem_box' n
  have hxF : x ∈ boxSV_boxF d n := by
    change x ∈ (boxSV_boxF d n : Set (Site d))
    rw [boxSV_coe_boxF]
    exact hx
  let oF : {z : Site d // z ∈ boxSV_boxF d n} :=
    ⟨Percolation.origin d, h0⟩
  let xF : {z : Site d // z ∈ boxSV_boxF d n} := ⟨x, hxF⟩
  have hox : oF ≠ xF := by
    intro h
    apply hxo
    exact congrArg Subtype.val h |>.symm
  unfold corrOriginInner
  rw [dif_pos h0, dif_pos hxF]
  rw [freeCorr, if_neg hox]
  unfold currentContinuityFreeBoxTwoPoint
  rw [integral_freeMeasure_spinProd_eq_freeDomain d n beta
    ({Percolation.origin d, x} : Finset _)]
  · rw [show Ising.boxFinset d n = boxSV_boxF d n by
      rw [boxSV_boxF_eq_toFinset]
      rfl]
    have hsupp : ({oF, xF} : Finset _) =
        freeDomainSpinSupport (boxSV_boxF d n)
          {Percolation.origin d, x} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton,
        freeDomainSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (hz | hz)
        · left
          exact Subtype.ext hz
        · right
          exact Subtype.ext hz
    have hsupp' :
        ({⟨Percolation.origin d, h0⟩, ⟨x, hxF⟩} : Finset _) =
          freeDomainSpinSupport (boxSV_boxF d n)
            {Percolation.origin d, x} := by
      simpa [oF, xF] using hsupp
    rw [hsupp']
    exact isingExpectation_instance_irrel
      (Finset.Subtype.fintype (boxSV_boxF d n))
      (freeDomainVerticesFintype (boxSV_boxF d n))
      (fun a b => a.instDecidableEq b) (fun a b => a.instDecidableEq b)
      (graphS d (boxSV_boxF d n))
      (instDecidableAdjGraphS d (boxSV_boxF d n))
      (freeDomainGraphDecidableAdj (boxSV_boxF d n)) beta 0 _
  · intro z hz
    rw [show Ising.boxFinset d n = boxSV_boxF d n by
      rw [boxSV_boxF_eq_toFinset]
      rfl]
    have hz' : z = Percolation.origin d ∨ z = x := by simpa using hz
    exact hz'.elim (fun h => h ▸ h0) (fun h => h ▸ hxF)



theorem corrOriginInner_box_le_currentContinuityFreeTwoPoint
    (d n : Nat) (beta : Real) (hbeta : 0 ≤ beta) (x : Site d)
    (hx : x ∈ box d n) (hxo : x ≠ Percolation.origin d) :
    corrOriginInner d beta (boxSV_boxF d n) x ≤
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  rw [corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint
    d n beta x hx hxo]
  apply currentContinuityFreeBoxTwoPoint_le_freeTwoPoint beta hbeta
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rw [show Ising.boxFinset d n = boxSV_boxF d n by
    rw [boxSV_boxF_eq_toFinset]
    rfl]
  change z ∈ (boxSV_boxF d n : Set (Site d))
  rw [boxSV_coe_boxF]
  exact hz.elim (fun h => h ▸ origin_mem_box' n) (fun h => h ▸ hx)


def criticalAxisSite {d : Nat} (hd : 1 ≤ d) (n : Nat) : Site d :=
  fun i => if i = (⟨0, hd⟩ : Fin d) then (n : Int) else 0

theorem criticalAxisSite_mem_box {d n : Nat} (hd : 1 ≤ d) :
    criticalAxisSite hd n ∈ box d n := by
  intro i
  by_cases hi : i = (⟨0, hd⟩ : Fin d)
  · simp [criticalAxisSite, hi]
  · simp [criticalAxisSite, hi]

theorem criticalAxisSite_ne_origin {d n : Nat} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    criticalAxisSite hd n ≠ Percolation.origin d := by
  intro h
  have hcoord := congrFun h ⟨0, hd⟩
  simp [criticalAxisSite, Percolation.origin] at hcoord
  omega




theorem criticalAxisTwoPoint_powerLower_of_shellComparison
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hshell : ∀ e ∈ boundaryEdges d (boxSV_boxF d n),
      currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d) e.1 ≤
        currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d)
          (criticalAxisSite (by omega) n)) :
    1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) *
      (2 * (n : Real) + 1) ^ (d - 1)) ≤
      currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d)
        (criticalAxisSite (by omega) n) := by
  let beta := IsingFK.betaC (magnetization d)
  let x := criticalAxisSite (d := d) (by omega : 1 ≤ d) n
  have hbeta : 0 < beta := by
    dsimp [beta]
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact tildeBetaCIsing_pos hd
  have hxo : x ≠ Percolation.origin d :=
    criticalAxisSite_ne_origin (by omega) hn
  have htarget : 0 ≤ currentContinuityFreeTwoPoint d beta
      (Percolation.origin d) x := by
    rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
      beta hbeta (by omega) (Percolation.origin d) x hxo.symm]
    exact measureReal_nonneg
  have hlower := isingBoxSimonMass_forces_pointwise_powerLower
    d n beta (currentContinuityFreeTwoPoint d beta (Percolation.origin d) x) 1
    (by omega) hn hbeta zero_lt_one htarget
    (phiIsing_ge_one_at_isingFK_betaC hd (boxSV_boxF d n) (by
      change Percolation.origin d ∈ (boxSV_boxF d n : Set (Site d))
      rw [boxSV_coe_boxF]
      exact origin_mem_box' n)) (by
        intro e he
        have heIn : e.1 ∈ box d n := by
          have heFin : e.1 ∈ (boxSV_boxF d n : Set (Site d)) :=
            boundaryEdges_fst_mem he
          rwa [boxSV_coe_boxF] at heFin
        have heNe : e.1 ≠ Percolation.origin d := by
          intro heq
          obtain ⟨_heIn, heOut, heAdj⟩ := shk_mem_boundaryEdges_iff.mp he
          rw [heq] at heAdj
          apply heOut
          change e.2 ∈ (boxSV_boxF d n : Set (Site d))
          rw [boxSV_coe_boxF]
          exact sct_adj_mem_box_of_mem_box_pred hn
            (origin_mem_box' (n - 1)) heAdj
        have hshell' : currentContinuityFreeTwoPoint d beta
            (Percolation.origin d) e.1 ≤
            1 * currentContinuityFreeTwoPoint d beta
              (Percolation.origin d) x := by
          simpa [beta, x] using hshell e he
        exact (corrOriginInner_box_le_currentContinuityFreeTwoPoint
          d n beta hbeta.le e.1 heIn heNe).trans hshell')
  simpa [beta, x] using hlower






def CriticalIsingMessagerMiracle (d : Nat) (hd : 1 ≤ d) : Prop :=
  ∀ n : Nat, 1 ≤ n →
    (∀ e ∈ boundaryEdges d (boxSV_boxF d n),
      currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d) e.1 ≤
        currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d)
          (criticalAxisSite hd n)) ∧
    ∀ x ∈ boxSV_vbF d n,
      currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d)
          (criticalAxisSite hd (d * n)) ≤
        currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d) x



theorem criticalBoundaryTwoPoint_powerLower_of_messagerMiracle
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hMM : CriticalIsingMessagerMiracle d (by omega))
    (x : Site d) (hx : x ∈ boxSV_vbF d n) :
    1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) *
      (2 * ((d * n : Nat) : Real) + 1) ^ (d - 1)) ≤
      currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d) x := by
  have hdn : 1 ≤ d * n := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hd)) (Nat.ne_of_gt hn))
  have haxis := criticalAxisTwoPoint_powerLower_of_shellComparison
    hd hdn (hMM (d * n) hdn).1
  exact haxis.trans ((hMM n hn).2 x hx)

end StatMech.FrontierA
