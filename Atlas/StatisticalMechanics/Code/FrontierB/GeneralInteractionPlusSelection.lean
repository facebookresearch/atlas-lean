/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.GeneralInteractionPlusParity









open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice



theorem generalPlusCurrentLimit_pattern_factor_nonDiagonal
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
    {nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (a : ↑S → Nat) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder S (currentLocalParity a)) *
        nonnegativeFiniteParityPMF S (fun e ↦ beta * J e)
          (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1))
          (currentLocalParity a) a := by
  apply hnu.pattern_factor_of_eventually S
    (fun odd ↦ nonnegativeFiniteParityPMF S (fun e ↦ beta * J e)
      (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1)) odd)
    (fun odd b ↦ PMF.apply_ne_top
      (nonnegativeFiniteParityPMF S (fun e ↦ beta * J e)
        (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1)) odd) b)
  obtain ⟨N, hSN⟩ := finiteInteractionEdges_subset_box S
  intro b
  filter_upwards [eventually_ge_atTop N] with k hk
  apply generalPlusBoxCurrentMeasure_pattern_factor_nonDiagonal
    J hJ beta hbeta S
  · intro e he x hx
    exact box_mono d (show N ≤ 2 * phi k + 1 by
      exact hk.trans (hphi.id_le k) |>.trans (by omega)) (hSN e he x hx)
  · exact hSdiag



def GeneralPlusParityAvoidanceConverges {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta) : Prop :=
  ∀ F : Finset (Sym2 (Site d)), ∃ L : ℝ≥0∞, Tendsto
    (fun n ↦ (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F)) atTop (nhds L)



theorem generalPlusCurrentLimit_parityMarginal_eq
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (havoid : GeneralPlusParityAvoidanceConverges J hJ beta hbeta)
    (S : Finset (Sym2 (Site d)))
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : Nat → Nat} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
    currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
  apply currentLimit_parityMarginal_eq_of_avoid_tendsto
    (fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le)
    havoid S hphi hpsi hnu hrho

theorem generalPlusCurrentLimit_nonDiagonalMarginal_eq
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (havoid : GeneralPlusParityAvoidanceConverges J hJ beta hbeta)
    (S : Finset (Sym2 (Site d))) (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : Nat → Nat} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor nu rho S
    (fun odd ↦ nonnegativeFiniteParityPMF S (fun e ↦ beta * J e)
      (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1)) odd)
  · exact generalPlusCurrentLimit_parityMarginal_eq
      J hJ beta hbeta havoid S hphi hpsi hnu hrho
  · intro a
    exact generalPlusCurrentLimit_pattern_factor_nonDiagonal
      J hJ beta hbeta S hSdiag hphi hnu a
  · intro a
    exact generalPlusCurrentLimit_pattern_factor_nonDiagonal
      J hJ beta hbeta S hSdiag hpsi hrho a

theorem generalPlusBoxCurrentMeasure_diag_zero {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (n : Nat) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e.IsDiag) :
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1 := by
  have hmeas : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} :=
    (measurable_pi_apply e) (MeasurableSet.singleton 0)
  change Measure.map (extendInteractionBoxCurrent d (2 * n + 1))
    (boundaryCurrentPMF (interactionBoxGraph d (2 * n + 1)) beta
      (interactionBoxCoupling J (2 * n + 1)) hbeta
      (fun f ↦ hJ (Sym2.map Subtype.val f))
      (interactionPlusInterior d n)).toMeasure
      {m | m e = 0} = 1
  rw [Measure.map_apply
    (measurable_extendInteractionBoxCurrent d (2 * n + 1)) hmeas]
  have hpre : extendInteractionBoxCurrent d (2 * n + 1) ⁻¹'
      {m | m e = 0} = Set.univ := by
    ext m
    simp [extendInteractionBoxCurrent_diag_zero d (2 * n + 1) m e he]
  rw [hpre, measure_univ]

theorem generalPlusCurrentLimit_diag_zero {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e.IsDiag)
    {nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : Nat → Nat}
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta) ∘ phi) nu) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  let S : Finset (Sym2 (Site d)) := {e}
  let A : Set (↑S → Nat) := {a | a ⟨e, by simp [S]⟩ = 0}
  have hset : currentCylinder S A = {m | m e = 0} := by
    ext m
    simp [currentCylinder, restrictCurrent, A, S]
  have hlim := hnu.cylinderENNReal S A
  rw [hset] at hlim
  have hone : Tendsto
      (fun k ↦ (generalPlusBoxCurrentMeasure J hJ (phi k) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0}) atTop (nhds 1) := by
    simpa only [generalPlusBoxCurrentMeasure_diag_zero J hJ _ beta hbeta e he]
      using (tendsto_const_nhds :
        Tendsto (fun _ : Nat ↦ (1 : ℝ≥0∞)) atTop (nhds 1))
  exact tendsto_nhds_unique hlim hone

theorem generalPlusCurrentLimit_marginal_eq
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (havoid : GeneralPlusParityAvoidanceConverges J hJ beta hbeta)
    (S : Finset (Sym2 (Site d)))
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : Nat → Nat} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply,
    currentCylinder_singleton_reduce_nonDiagonal nu S
      (fun e he ↦ generalPlusCurrentLimit_diag_zero
        J hJ beta hbeta.le e he hnu) a,
    currentCylinder_singleton_reduce_nonDiagonal rho S
      (fun e he ↦ generalPlusCurrentLimit_diag_zero
        J hJ beta hbeta.le e he hrho) a]
  split_ifs
  · have hD := generalPlusCurrentLimit_nonDiagonalMarginal_eq
      J hJ beta hbeta havoid (nonDiagonalEdgeFinset S)
      (nonDiagonalEdgeFinset_nonDiag S) hphi hpsi hnu hrho
    have happ := congrArg (fun p : ProbabilityMeasure
      (↑(nonDiagonalEdgeFinset S) → Nat) ↦
        (p : Measure (↑(nonDiagonalEdgeFinset S) → Nat))
          {Finset.restrict₂ (π := fun _ : Sym2 (Site d) ↦ Nat)
            (nonDiagonalEdgeFinset_subset S) a}) hD
    simpa only [currentMarginal_apply] using happ
  · rfl



theorem generalPlusCurrentLimit_eq
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (havoid : GeneralPlusParityAvoidanceConverges J hJ beta hbeta)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : Nat → Nat} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
    nu = rho := by
  apply ProbabilityMeasure.ext_of_currentMarginal_eq
  intro S
  exact generalPlusCurrentLimit_marginal_eq
    J hJ beta hbeta havoid S hphi hpsi hnu hrho

theorem generalPlusCurrentLimit_eq_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : ℝ) (hbeta : 0 < beta)
    (havoid : GeneralPlusParityAvoidanceConverges
      I.coupling I.nonneg beta hbeta)
    {nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalPlusBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta.le) ∘ phi) nu) :
    nu = generalInfinitePlusCurrentMeasure I beta hbeta.le := by
  exact generalPlusCurrentLimit_eq I.coupling I.nonneg beta hbeta havoid
    hphi (generalCurrentBoxSubsequence_strictMono I beta hbeta.le)
    hnu (generalPlusBoxCurrentMeasure_tendsto_infinite I beta hbeta.le)




theorem generalPlusBoxCurrentMeasure_tendsto_full
    {d : Nat} (I : SummableFerromagneticInteraction d)
    (beta : ℝ) (hbeta : 0 < beta)
    (havoid : GeneralPlusParityAvoidanceConverges
      I.coupling I.nonneg beta hbeta) :
    WeakCurrentConverges
      (fun n ↦ generalPlusBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta.le)
      (generalInfinitePlusCurrentMeasure I beta hbeta.le) := by
  let mu := fun n ↦ generalPlusBoxCurrentMeasure
    I.coupling I.nonneg n beta hbeta.le
  have hmem : generalInfinitePlusCurrentMeasure I beta hbeta.le ∈
      closure (Set.range mu) := by
    apply isClosed_closure.mem_of_tendsto
      (generalPlusBoxCurrentMeasure_tendsto_infinite I beta hbeta.le)
    filter_upwards with k
    exact subset_closure
      ⟨generalCurrentBoxSubsequence I beta hbeta.le k, rfl⟩
  exact weakCurrent_tendsto_of_tight_of_subseq_unique mu
    (generalInfinitePlusCurrentMeasure I beta hbeta.le)
    (generalPlusBoxCurrentMeasure_tight
      I.coupling I.nonneg beta hbeta.le) hmem
    (fun rho phi hphi hconv ↦
      generalPlusCurrentLimit_eq_infinite
        I beta hbeta havoid hphi hconv)

theorem generalPlusBoxCurrentMeasure_cylinder_tendsto_full
    {d : Nat} (I : SummableFerromagneticInteraction d)
    (beta : ℝ) (hbeta : 0 < beta)
    (havoid : GeneralPlusParityAvoidanceConverges
      I.coupling I.nonneg beta hbeta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → Nat)) :
    Tendsto
      (fun n ↦ (generalPlusBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta.le :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A)) atTop
      (nhds ((generalInfinitePlusCurrentMeasure I beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A))) :=
  (generalPlusBoxCurrentMeasure_tendsto_full
    I beta hbeta havoid).cylinderENNReal S A

end StatMech.FrontierB
