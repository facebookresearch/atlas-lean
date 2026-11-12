/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.GeneralInteractionFreeParityLimit
import Code.FrontierB.CurrentSelectionIndependence
import Code.FrontierB.NonnegativeCurrentFiniteMarginal





open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice

def interactionBoxLiftIndexEmbedding {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    ↑F ↪ (interactionBoxGraph d n).edgeFinset where
  toFun e := ⟨interactionBoxLiftEdge F hFbox e,
    interactionBoxLiftedEdges_subset_edgeFinset F hFbox hFdiag (by
      unfold interactionBoxLiftedEdges
      exact Finset.mem_map.mpr ⟨e, Finset.mem_univ e, rfl⟩)⟩
  inj' e f hef := by
    apply Subtype.ext
    exact congrArg Subtype.val
      ((interactionBoxLiftEdgeEmbedding F hFbox).injective
        (congrArg Subtype.val hef))

noncomputable def interactionBoxLiftedEdgeIndices {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    Finset (interactionBoxGraph d n).edgeFinset :=
  Finset.univ.map (interactionBoxLiftIndexEmbedding F hFbox hFdiag)

noncomputable def interactionBoxLiftIndexEquiv {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    ↑F ≃ ↑(interactionBoxLiftedEdgeIndices F hFbox hFdiag) :=
  Equiv.ofBijective
    (fun e => ⟨interactionBoxLiftIndexEmbedding F hFbox hFdiag e, by
      simp [interactionBoxLiftedEdgeIndices]⟩)
    ⟨fun _ _ h => (interactionBoxLiftIndexEmbedding F hFbox hFdiag).injective
        (congrArg Subtype.val h),
      fun i => by
        have hi := i.2
        change i.1 ∈ Finset.univ.map
          (interactionBoxLiftIndexEmbedding F hFbox hFdiag) at hi
        rw [Finset.mem_map] at hi
        obtain ⟨e, he, hei⟩ := hi
        refine ⟨e, ?_⟩
        apply Subtype.ext
        exact hei⟩

@[simp] theorem interactionBoxEdgeIncl_liftIndex {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) (e : ↑F) :
    interactionBoxEdgeIncl d n
        (interactionBoxLiftIndexEmbedding F hFbox hFdiag e) = e.1 := by
  exact interactionBoxLiftEdge_map_val F hFbox e

theorem restrictCurrent_extendInteractionBoxCurrent_lift {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag)
    (m : EdgeCurrent (interactionBoxGraph d n)) :
    restrictCurrent F (extendInteractionBoxCurrent d n m) =
      fun e => restrictCurrent
        (interactionBoxLiftedEdgeIndices F hFbox hFdiag) m
          (interactionBoxLiftIndexEquiv F hFbox hFdiag e) := by
  funext e
  change extendInteractionBoxCurrent d n m e.1 =
    m (interactionBoxLiftIndexEquiv F hFbox hFdiag e).1
  have heq : (interactionBoxLiftIndexEquiv F hFbox hFdiag e).1 =
      interactionBoxLiftIndexEmbedding F hFbox hFdiag e := rfl
  rw [heq, ← interactionBoxEdgeIncl_liftIndex F hFbox hFdiag e]
  exact extendInteractionBoxCurrent_included d n m
    (interactionBoxLiftIndexEmbedding F hFbox hFdiag e)

noncomputable def interactionBoxPullbackPattern {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) {A : Type*}
    (a : ↑F → A) :
    ↑(interactionBoxLiftedEdgeIndices F hFbox hFdiag) → A :=
  a ∘ (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm

theorem nonnegativeFiniteParityKernel_pullback {d n : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ)
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) (a : ↑F → Nat) :
    nonnegativeFiniteParityKernel
        (interactionBoxLiftedEdgeIndices F hFbox hFdiag)
        (fun e : (interactionBoxGraph d n).edgeFinset =>
          beta * interactionBoxCoupling J n e.1)
        (currentLocalParity
          (interactionBoxPullbackPattern F hFbox hFdiag a))
        (interactionBoxPullbackPattern F hFbox hFdiag a) =
      nonnegativeFiniteParityKernel F (fun e => beta * J e)
        (currentLocalParity a) a := by
  unfold nonnegativeFiniteParityKernel interactionBoxPullbackPattern
  symm
  apply Fintype.prod_equiv (interactionBoxLiftIndexEquiv F hFbox hFdiag)
  intro e
  have hincl := interactionBoxEdgeIncl_liftIndex F hFbox hFdiag e
  have hc : interactionBoxCoupling J n
      (interactionBoxLiftIndexEmbedding F hFbox hFdiag e).1 = J e.1 :=
    congrArg J hincl
  have heq :
      ((interactionBoxLiftIndexEquiv F hFbox hFdiag e).1 :
        (interactionBoxGraph d n).edgeFinset) =
        interactionBoxLiftIndexEmbedding F hFbox hFdiag e := rfl
  rw [heq]
  change nonnegativeParityEdgeKernel (beta * J e.1)
      (currentLocalParity a e) (a e) =
    nonnegativeParityEdgeKernel
      (beta * interactionBoxCoupling J n
        (interactionBoxLiftIndexEmbedding F hFbox hFdiag e).1)
      (currentLocalParity
        (a ∘ (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm)
        (interactionBoxLiftIndexEquiv F hFbox hFdiag e))
      ((a ∘ (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm)
        (interactionBoxLiftIndexEquiv F hFbox hFdiag e))
  rw [hc]
  simp [currentLocalParity, interactionBoxPullbackPattern]

theorem preimage_currentCylinder_singleton_extendInteractionBoxCurrent
    {d n : Nat} (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) (a : ↑F → Nat) :
    extendInteractionBoxCurrent d n ⁻¹' currentCylinder F {a} =
      {m | restrictCurrent (interactionBoxLiftedEdgeIndices F hFbox hFdiag) m =
        interactionBoxPullbackPattern F hFbox hFdiag a} := by
  ext m
  simp only [Set.mem_preimage, currentCylinder, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  rw [restrictCurrent_extendInteractionBoxCurrent_lift F hFbox hFdiag m]
  constructor
  · intro h
    funext i
    have hc := congrFun h ((interactionBoxLiftIndexEquiv F hFbox hFdiag).symm i)
    simpa [interactionBoxPullbackPattern] using hc
  · intro h
    funext e
    have hc := congrFun h (interactionBoxLiftIndexEquiv F hFbox hFdiag e)
    simpa [interactionBoxPullbackPattern] using hc

theorem preimage_currentParityPatternCylinder_extendInteractionBoxCurrent
    {d n : Nat} (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) (odd : ↑F → Bool) :
    extendInteractionBoxCurrent d n ⁻¹'
        currentParityPatternCylinder F odd =
      {m | currentLocalParity
        (restrictCurrent (interactionBoxLiftedEdgeIndices F hFbox hFdiag) m) =
          odd ∘ (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm} := by
  ext m
  change currentLocalParity
      (restrictCurrent F (extendInteractionBoxCurrent d n m)) = odd ↔ _
  rw [restrictCurrent_extendInteractionBoxCurrent_lift F hFbox hFdiag m]
  constructor
  · intro h
    funext i
    have hc := congrFun h ((interactionBoxLiftIndexEquiv F hFbox hFdiag).symm i)
    simpa [currentLocalParity] using hc
  · intro h
    funext e
    have hc := congrFun h (interactionBoxLiftIndexEquiv F hFbox hFdiag e)
    simpa [currentLocalParity] using hc

theorem sourcelessNonnegativeCurrentLocalParityPMF
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (S : Finset G.edgeFinset) :
    PMF.map currentLocalParity
        (PMF.map (restrictCurrent S)
          (sourcelessCurrentPMF G beta J hbeta.le hJ)) =
      PMF.map (restrictParity G S)
        (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ) := by
  rw [sourcelessNonnegativeParityPMF, PMF.map_comp, PMF.map_comp]
  congr 1
  funext m
  exact currentLocalParity_restrictCurrent_eq_restrictParity G S m



theorem generalFreeBoxCurrentMeasure_pattern_factor_nonDiagonal
    {d n : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) (a : ↑F → Nat) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder F {a}) =
      (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder F (currentLocalParity a)) *
        nonnegativeFiniteParityPMF F (fun e ↦ beta * J e)
          (fun e : ↑F ↦ mul_nonneg hbeta.le (hJ e.1))
          (currentLocalParity a) a := by
  let G := interactionBoxGraph d n
  let S := interactionBoxLiftedEdgeIndices F hFbox hFdiag
  let Jn := interactionBoxCoupling J n
  let p := sourcelessCurrentPMF G beta Jn hbeta.le
    (fun e ↦ hJ (Sym2.map Subtype.val e))
  let q := PMF.map (restrictParity G S)
    (sourcelessNonnegativeParityPMF G beta Jn hbeta.le
      (fun e ↦ hJ (Sym2.map Subtype.val e)))
  let a' := interactionBoxPullbackPattern F hFbox hFdiag a
  have hcurrent : PMF.map (restrictCurrent S) p =
      q.bind (nonnegativeFiniteParityPMF S
        (fun e : G.edgeFinset ↦ beta * Jn e.1)
        (fun e : ↑S ↦ mul_nonneg hbeta.le
          (hJ (Sym2.map Subtype.val e.1.1)))) := by
    exact sourcelessCurrentFiniteMarginal_eq_nonnegativeParity_bind
      G beta hbeta Jn (fun e ↦ hJ (Sym2.map Subtype.val e)) S
  have hpoint := congrArg (fun r : PMF (↑S → Nat) ↦ r a') hcurrent
  change (PMF.map (restrictCurrent S) p) a' =
    q.bind (nonnegativeFiniteParityPMF S
      (fun e : G.edgeFinset ↦ beta * Jn e.1)
      (fun e : ↑S ↦ mul_nonneg hbeta.le
        (hJ (Sym2.map Subtype.val e.1.1)))) a' at hpoint
  rw [bind_nonnegativeFiniteParityPMF_apply] at hpoint
  have hparity : currentLocalParity a' =
      currentLocalParity a ∘
        (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm := by
    funext i
    rfl
  have hkernel : nonnegativeFiniteParityPMF S
      (fun e : G.edgeFinset ↦ beta * Jn e.1)
      (fun e : ↑S ↦ mul_nonneg hbeta.le
        (hJ (Sym2.map Subtype.val e.1.1)))
      (currentLocalParity a') a' =
    nonnegativeFiniteParityPMF F (fun e ↦ beta * J e)
      (fun e : ↑F ↦ mul_nonneg hbeta.le (hJ e.1))
      (currentLocalParity a) a := by
    rw [nonnegativeFiniteParityPMF_apply,
      nonnegativeFiniteParityPMF_apply]
    exact congrArg ENNReal.ofReal
      (nonnegativeFiniteParityKernel_pullback J beta F hFbox hFdiag a)
  have hkernel' : nonnegativeFiniteParityPMF S
      (fun e : G.edgeFinset ↦ beta * Jn e.1)
      (fun e : ↑S ↦ mul_nonneg hbeta.le
        (hJ (Sym2.map Subtype.val e.1.1)))
      (currentLocalParity a ∘
        (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm) a' =
    nonnegativeFiniteParityPMF F (fun e ↦ beta * J e)
      (fun e : ↑F ↦ mul_nonneg hbeta.le (hJ e.1))
      (currentLocalParity a) a := by
    rw [← hparity]
    exact hkernel
  have hsingle : MeasurableSet (currentCylinder F {a}) :=
    measurableSet_currentCylinder F {a}
  have hparMeas : MeasurableSet
      (currentParityPatternCylinder F (currentLocalParity a)) :=
    measurableSet_currentCylinder F _
  change Measure.map (extendInteractionBoxCurrent d n) p.toMeasure
      (currentCylinder F {a}) =
    Measure.map (extendInteractionBoxCurrent d n) p.toMeasure
      (currentParityPatternCylinder F (currentLocalParity a)) * _
  rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hsingle,
    preimage_currentCylinder_singleton_extendInteractionBoxCurrent
      F hFbox hFdiag a,
    Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hparMeas,
    preimage_currentParityPatternCylinder_extendInteractionBoxCurrent
      F hFbox hFdiag]
  rw [show p.toMeasure {m | restrictCurrent S m = a'} =
      (PMF.map (restrictCurrent S) p) a' by
    rw [← PMF.toMeasure_apply_singleton _ a' (MeasurableSet.singleton a')]
    rw [PMF.toMeasure_map_apply]
    · rfl
    · exact Measurable.of_discrete
    · exact MeasurableSet.singleton a']
  rw [hpoint, hparity, hkernel']
  congr 1
  rw [show p.toMeasure {m | currentLocalParity (restrictCurrent S m) =
        currentLocalParity a ∘
          (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm} =
      (PMF.map currentLocalParity (PMF.map (restrictCurrent S) p))
        (currentLocalParity a ∘
          (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm) by
    let odd := currentLocalParity a ∘
      (interactionBoxLiftIndexEquiv F hFbox hFdiag).symm
    rw [← PMF.toMeasure_apply_singleton _ odd (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply currentLocalParity
      (PMF.map (restrictCurrent S) p) {odd}
      Measurable.of_discrete (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply (restrictCurrent S) p
      (currentLocalParity ⁻¹' {odd})
      Measurable.of_discrete MeasurableSet.of_discrete]
    rfl]
  rw [sourcelessNonnegativeCurrentLocalParityPMF G beta hbeta Jn
    (fun e ↦ hJ (Sym2.map Subtype.val e)) S]



theorem generalFreeCurrentLimit_pattern_factor_nonDiagonal
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
    {nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
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
  apply generalFreeBoxCurrentMeasure_pattern_factor_nonDiagonal
    J hJ beta hbeta S
  · intro e he x hx
    exact box_mono d (hk.trans (hphi.id_le k)) (hSN e he x hx)
  · exact hSdiag



theorem generalFreeCurrentLimit_parityMarginal_eq {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : Nat → Nat} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
    currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
  apply currentLimit_parityMarginal_eq_of_avoid_tendsto
    (fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta.le)
    (fun A => generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto_all
      J hJ beta hbeta A) S hphi hpsi hnu hrho

theorem generalFreeCurrentLimit_nonDiagonalMarginal_eq {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : Nat → Nat} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor nu rho S
    (fun odd ↦ nonnegativeFiniteParityPMF S (fun e ↦ beta * J e)
      (fun e : ↑S ↦ mul_nonneg hbeta.le (hJ e.1)) odd)
  · exact generalFreeCurrentLimit_parityMarginal_eq J hJ beta hbeta S
      hphi hpsi hnu hrho
  · intro a
    exact generalFreeCurrentLimit_pattern_factor_nonDiagonal
      J hJ beta hbeta S hSdiag hphi hnu a
  · intro a
    exact generalFreeCurrentLimit_pattern_factor_nonDiagonal
      J hJ beta hbeta S hSdiag hpsi hrho a

theorem generalFreeBoxCurrentMeasure_diag_zero {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (n : Nat) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e.IsDiag) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1 := by
  have hmeas : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} :=
    (measurable_pi_apply e) (MeasurableSet.singleton 0)
  change Measure.map (extendInteractionBoxCurrent d n)
    (sourcelessCurrentPMF (interactionBoxGraph d n) beta
      (interactionBoxCoupling J n) hbeta
      (fun f ↦ hJ (Sym2.map Subtype.val f))).toMeasure
      {m | m e = 0} = 1
  rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hmeas]
  have hpre : extendInteractionBoxCurrent d n ⁻¹' {m | m e = 0} = Set.univ := by
    ext m
    simp [extendInteractionBoxCurrent_diag_zero d n m e he]
  rw [hpre, measure_univ]

theorem generalFreeCurrentLimit_diag_zero {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e.IsDiag)
    {nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : Nat → Nat}
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta) ∘ phi) nu) :
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
      (fun k ↦ (generalFreeBoxCurrentMeasure J hJ (phi k) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0}) atTop (nhds 1) := by
    simpa only [generalFreeBoxCurrentMeasure_diag_zero J hJ _ beta hbeta e he]
      using (tendsto_const_nhds :
        Tendsto (fun _ : Nat ↦ (1 : ℝ≥0∞)) atTop (nhds 1))
  exact tendsto_nhds_unique hlim hone

theorem nonDiagonalEdgeFinset_subset {V : Type*} [DecidableEq V]
    (S : Finset (Sym2 V)) : nonDiagonalEdgeFinset S ⊆ S :=
  Finset.filter_subset _ _

theorem nonDiagonalEdgeFinset_nonDiag {V : Type*} [DecidableEq V]
    (S : Finset (Sym2 V)) : ∀ e ∈ nonDiagonalEdgeFinset S, ¬e.IsDiag := by
  intro e he
  exact (Finset.mem_filter.mp he).2

theorem ae_diagonal_zero_on_finset {d : Nat}
    (mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
    (S : Finset (Sym2 (Site d)))
    (hzero : ∀ e, e.IsDiag →
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1) :
    ∀ᵐ m ∂(mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))),
      ∀ e ∈ S, e.IsDiag → m e = 0 := by
  rw [Finset.eventually_all]
  intro e heS
  by_cases he : e.IsDiag
  · filter_upwards [ae_eq_zero_of_measure_eq_one mu e (hzero e he)] with m hm
    exact fun _ ↦ hm
  · filter_upwards with m hdiag
    exact (he hdiag).elim

theorem currentCylinder_singleton_reduce_nonDiagonal {d : Nat}
    (mu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
    (S : Finset (Sym2 (Site d)))
    (hzero : ∀ e, e.IsDiag →
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1)
    (a : ↑S → Nat) :
    (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      if ∀ e : ↑S, e.1.IsDiag → a e = 0 then
        (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder (nonDiagonalEdgeFinset S)
            {Finset.restrict₂ (π := fun _ : Sym2 (Site d) ↦ Nat)
              (nonDiagonalEdgeFinset_subset S) a})
      else 0 := by
  let D := nonDiagonalEdgeFinset S
  let aD := Finset.restrict₂ (π := fun _ : Sym2 (Site d) ↦ Nat)
    (nonDiagonalEdgeFinset_subset S) a
  have hae := ae_diagonal_zero_on_finset mu S hzero
  split_ifs with ha
  · apply measure_congr
    filter_upwards [hae] with m hm
    apply propext
    change (restrictCurrent S m = a) ↔ restrictCurrent D m = aD
    constructor
    · intro h
      funext e
      exact congrFun h ⟨e.1, (nonDiagonalEdgeFinset_subset S) e.2⟩
    · intro h
      funext e
      by_cases he : e.1.IsDiag
      · rw [show restrictCurrent S m e = 0 by exact hm e.1 e.2 he]
        exact (ha e he).symm
      · let eD : ↑D := ⟨e.1, Finset.mem_filter.mpr ⟨e.2, he⟩⟩
        exact congrFun h eD
  · have hempty : (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (∅ : Set (InfiniteCurrentConfig (Sym2 (Site d)))) = 0 := measure_empty
    rw [← hempty]
    apply measure_congr
    filter_upwards [hae] with m hm
    apply propext
    change (restrictCurrent S m = a) ↔ False
    constructor
    · intro h
      apply ha
      intro e he
      rw [← congrFun h e]
      exact hm e.1 e.2 he
    · exact False.elim

theorem generalFreeCurrentLimit_marginal_eq {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : Nat → Nat} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply,
    currentCylinder_singleton_reduce_nonDiagonal nu S
      (fun e he ↦ generalFreeCurrentLimit_diag_zero
        J hJ beta hbeta.le e he hnu) a,
    currentCylinder_singleton_reduce_nonDiagonal rho S
      (fun e he ↦ generalFreeCurrentLimit_diag_zero
        J hJ beta hbeta.le e he hrho) a]
  split_ifs
  · have hD := generalFreeCurrentLimit_nonDiagonalMarginal_eq
      J hJ beta hbeta (nonDiagonalEdgeFinset S)
      (nonDiagonalEdgeFinset_nonDiag S) hphi hpsi hnu hrho
    have happ := congrArg (fun p : ProbabilityMeasure
      (↑(nonDiagonalEdgeFinset S) → Nat) ↦
        (p : Measure (↑(nonDiagonalEdgeFinset S) → Nat))
          {Finset.restrict₂ (π := fun _ : Sym2 (Site d) ↦ Nat)
            (nonDiagonalEdgeFinset_subset S) a}) hD
    simpa only [currentMarginal_apply] using happ
  · rfl



theorem generalFreeCurrentLimit_eq {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : Nat → Nat} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure J hJ n beta hbeta.le) ∘ psi) rho) :
    nu = rho := by
  apply ProbabilityMeasure.ext_of_currentMarginal_eq
  intro S
  exact generalFreeCurrentLimit_marginal_eq
    J hJ beta hbeta S hphi hpsi hnu hrho

theorem generalFreeCurrentLimit_eq_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : ℝ) (hbeta : 0 < beta)
    {nu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n ↦ generalFreeBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta.le) ∘ phi) nu) :
    nu = generalInfiniteFreeCurrentMeasure I beta hbeta.le := by
  exact generalFreeCurrentLimit_eq I.coupling I.nonneg beta hbeta
    hphi (generalCurrentBoxSubsequence_strictMono I beta hbeta.le)
    hnu (generalFreeBoxCurrentMeasure_tendsto_infinite I beta hbeta.le)



theorem generalFreeBoxCurrentMeasure_tendsto_full {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : ℝ) (hbeta : 0 < beta) :
    WeakCurrentConverges
      (fun n ↦ generalFreeBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta.le)
      (generalInfiniteFreeCurrentMeasure I beta hbeta.le) := by
  let mu := fun n ↦ generalFreeBoxCurrentMeasure
    I.coupling I.nonneg n beta hbeta.le
  have hmem : generalInfiniteFreeCurrentMeasure I beta hbeta.le ∈
      closure (Set.range mu) := by
    apply isClosed_closure.mem_of_tendsto
      (generalFreeBoxCurrentMeasure_tendsto_infinite I beta hbeta.le)
    filter_upwards with k
    exact subset_closure
      ⟨generalCurrentBoxSubsequence I beta hbeta.le k, rfl⟩
  exact weakCurrent_tendsto_of_tight_of_subseq_unique mu
    (generalInfiniteFreeCurrentMeasure I beta hbeta.le)
    (generalFreeBoxCurrentMeasure_tight
      I.coupling I.nonneg beta hbeta.le) hmem
    (fun rho phi hphi hconv ↦
      generalFreeCurrentLimit_eq_infinite I beta hbeta hphi hconv)

theorem generalFreeBoxCurrentMeasure_cylinder_tendsto_full {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → Nat)) :
    Tendsto
      (fun n ↦ (generalFreeBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta.le :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A)) atTop
      (nhds ((generalInfiniteFreeCurrentMeasure I beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A))) :=
  (generalFreeBoxCurrentMeasure_tendsto_full I beta hbeta).cylinderENNReal S A

end StatMech.FrontierB
