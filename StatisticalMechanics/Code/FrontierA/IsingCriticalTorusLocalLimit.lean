/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingTorusFreeBoundaryMonomialComparison
import Code.FrontierB.CurrentContinuityCriticalAxisClosure
import Code.FrontierB.FreeBoxEvenLimit
import Code.Ising.IsingPlusTIFromPlacement
import Code.Onsager.SignedLoopPhaseEndpoint









open Filter Finset MeasureTheory Set Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section


def boxFinsetSpinSupport (d n : Nat) (A : Finset (Site d)) :
    Finset {x : Site d // x ∈ boxFinset d n} :=
  Finset.univ.filter fun x ↦ x.1 ∈ A

theorem boxFinsetSpinSupport_map_subtype
    {d n : Nat} (A : Finset (Site d))
    (hA : (↑A : Set (Site d)) ⊆ box d n) :
    (boxFinsetSpinSupport d n A).map
        (Function.Embedding.subtype fun x ↦ x ∈ boxFinset d n) = A := by
  ext x
  simp only [Finset.mem_map, boxFinsetSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, mem_boxFinset.mpr (hA hx)⟩, hx, rfl⟩

theorem boxSpinSupport_map_iptp_boxEquiv
    {d n : Nat} (A : Finset (Site d)) :
    (boxSpinSupport d n A).map (iptp_boxEquiv d n).toEmbedding =
      boxFinsetSpinSupport d n A := by
  ext x
  simp [boxSpinSupport, boxFinsetSpinSupport, iptp_boxEquiv]
  change ((iptp_boxEquiv d n).symm x).1 ∈ A ↔ x.1 ∈ A
  rfl



theorem isingExpectation_boxFinsetSpinSupport_eq_freeMeasure
    {d n : Nat} (beta : Real) (A : Finset (Site d))
    (hA : (↑A : Set (Site d)) ⊆ box d n) :
    isingExpectation (graphS d (boxFinset d n)) beta 0
        (spinProd (boxFinsetSpinSupport d n A)) =
      ∫ omega, spinProd A omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  have hadj : ∀ x y : sctBox d n,
      (sctBoxGraph d n).Adj x y ↔
        (graphS d (boxFinset d n)).Adj
          (iptp_boxEquiv d n x) (iptp_boxEquiv d n y) := by
    intro x y
    rfl
  have hrel := isingExpectation_spinProd_relabel
    (sctBoxGraph d n) (graphS d (boxFinset d n))
    (iptp_boxEquiv d n) hadj beta 0 (boxSpinSupport d n A)
  rw [boxSpinSupport_map_iptp_boxEquiv] at hrel
  rw [integral_freeMeasure_spinProd d n beta 0 A hA]
  exact hrel.symm

theorem two_mul_succ_lt_isingDyadicSide (n : Nat) :
    2 * (n + 1) < isingDyadicSide n := by
  unfold isingDyadicSide
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
      have hp : 1 ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
      omega



theorem criticalFreeState_eq_plusState {d : Nat} (hd : 2 < d) :
    (freeState d (IsingFK.betaC (magnetization d)) 0 :
        Measure (ConfigSpace (Site d))) =
      (plusState d (IsingFK.betaC (magnetization d)) 0 :
        Measure (ConfigSpace (Site d))) := by
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 ≤ d)]
    exact (tildeBetaCIsing_pos (by omega : 2 ≤ d)).le
  exact StatMech.Onsager.freeState_eq_plusState_of_magnetization_eq_zero
    (IsingFK.betaC (magnetization d)) hbeta
    (isingCritical_magnetization_zero_and_gibbs_unique hd).1



def criticalTorusLocalSpinProd (d : Nat) (A : Finset (Site d))
    (n : Nat) : Real :=
  expJ (isingTorusGraph d n).edgeFinset
    (fun _ ↦ IsingFK.betaC (magnetization d)) (fun _ ↦ 0)
    (spinProd (A.image (isingSiteToDyadicTorus n)))

private theorem mapped_boxSupport_eq_torusImage
    {d n : Nat} (A : Finset (Site d))
    (hA : (↑A : Set (Site d)) ⊆ box d n)
    (hinj : Set.InjOn (isingSiteToDyadicTorus n)
      (↑(boxFinset d n) : Set (Site d))) :
    (((boxFinsetSpinSupport d n A).map
        (isingTorusImageEquiv (boxFinset d n) hinj).toEmbedding).map
      (Function.Embedding.subtype fun z ↦
        z ∈ isingTorusImageFinset n (boxFinset d n))) =
      A.image (isingSiteToDyadicTorus n) := by
  ext z
  simp only [Finset.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.1, by simpa [boxFinsetSpinSupport] using hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    let xBox : {x : Site d // x ∈ boxFinset d n} :=
      ⟨x, mem_boxFinset.mpr (hA hx)⟩
    let xT := isingTorusImageEquiv (boxFinset d n) hinj xBox
    refine ⟨xT, ?_, rfl⟩
    refine ⟨xBox, ?_, ?_⟩
    · simp [boxFinsetSpinSupport, xBox, hx]
    · apply Subtype.ext
      rfl

set_option maxHeartbeats 800000 in


theorem criticalTorusLocalSpinProd_tendsto
    {d : Nat} (hd : 2 < d) (A : Finset (Site d)) :
    Tendsto (criticalTorusLocalSpinProd d A) atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
          Measure (ConfigSpace (Site d))))) := by
  let betaC := IsingFK.betaC (magnetization d)
  have hbeta : 0 ≤ betaC := by
    dsimp [betaC]
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 ≤ d)]
    exact (tildeBetaCIsing_pos (by omega : 2 ≤ d)).le
  have hfree := integral_freeMeasure_spinProd_tendsto_freeState
    d betaC hbeta A
  have hplus := integral_plusMeasure_spinProd_full_tendsto
    d betaC hbeta A
  have hstates := criticalFreeState_eq_plusState hd
  have hplus' : Tendsto
      (fun n ↦ ∫ omega, spinProd A omega
        ∂(plusMeasure d n betaC 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d betaC 0 : Measure (ConfigSpace (Site d))))) := by
    rw [hstates]
    exact hplus
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  have hbounds : ∀ᶠ n in atTop,
      (∫ omega, spinProd A omega
          ∂(freeMeasure d n betaC 0 : Measure (ConfigSpace (Site d)))) ≤
        criticalTorusLocalSpinProd d A n ∧
      criticalTorusLocalSpinProd d A n ≤
        ∫ omega, spinProd A omega
          ∂(plusMeasure d n betaC 0 : Measure (ConfigSpace (Site d))) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hA : (↑A : Set (Site d)) ⊆ box d n :=
      hAN.trans (box_mono d hn)
    let S := boxFinset d n
    have hS : (↑S : Set (Site d)) ⊆ box d n := by
      intro x hx
      exact mem_boxFinset.mp hx
    let hinj : Set.InjOn (isingSiteToDyadicTorus n) (↑S : Set (Site d)) :=
      isingSiteToDyadicTorus_injectiveOn_finset S hS
        (by
          exact lt_of_lt_of_le (by omega : 2 * n < 2 * (n + 1))
            (two_mul_succ_lt_isingDyadicSide n).le)
    let B := boxFinsetSpinSupport d n A
    have hsandwich := freeSpinProd_le_isingTorusSpinProd_le_gvPlus
      S hS (two_mul_succ_lt_isingDyadicSide n) hinj betaC hbeta B
    have hfintype : (Finset.Subtype.fintype S) =
        (inferInstance : Fintype {x : Site d // x ∈ S}) :=
      Subsingleton.elim _ _
    rw [hfintype] at hsandwich
    have hmap := mapped_boxSupport_eq_torusImage A hA hinj
    have hBambient : B.map
        (Function.Embedding.subtype fun x ↦ x ∈ S) = A := by
      exact boxFinsetSpinSupport_map_subtype A hA
    constructor
    · rw [← isingExpectation_boxFinsetSpinSupport_eq_freeMeasure
        betaC A hA]
      change isingExpectation (graphS d S) betaC 0 (spinProd B) ≤ _
      rw [criticalTorusLocalSpinProd, ← hmap]
      exact hsandwich.1
    · rw [criticalTorusLocalSpinProd, ← hmap]
      calc
        _ ≤ ∫ omega, spinProd (B.map
              (Function.Embedding.subtype fun x ↦ x ∈ S)) omega
            ∂(gvPlusMeasure S betaC 0) := hsandwich.2
        _ = ∫ omega, spinProd A omega
            ∂(plusMeasure d n betaC 0 : Measure (ConfigSpace (Site d))) := by
          rw [hBambient, iptp_gvPlusMeasure_eq_plusMeasure]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hfree hplus' (hbounds.mono fun n hn ↦ hn.1)
      (hbounds.mono fun n hn ↦ hn.2)

end

end StatMech.FrontierA
