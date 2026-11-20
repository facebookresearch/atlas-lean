/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.GeneralInteractionFreeParityLimit
import Code.FrontierB.GeneralInteractionFreeSelection
import Code.FrontierB.InhomogeneousBoundaryParityAvoidance





open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice



theorem generalPlusBoxCurrentMeasure_parityAvoid_edgeImage
    {d n : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (E : Finset (Sym2 (interactionBoxVertices d (2 * n + 1))))
    (hE : E ⊆ (interactionBoxGraph d (2 * n + 1)).edgeFinset) :
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder
          (sym2FinsetMap (Function.Embedding.subtype
            (fun x : Site d ↦ x ∈ interactionBoxVertices d (2 * n + 1))) E)) =
      ENNReal.ofReal
        (inhomogeneousBoundaryParityAvoidSum
            (interactionBoxGraph d (2 * n + 1)) beta
            (interactionBoxCoupling J (2 * n + 1))
            (interactionPlusInterior d n) E /
          inhomogeneousBoundaryParityPartition
            (interactionBoxGraph d (2 * n + 1)) beta
            (interactionBoxCoupling J (2 * n + 1))
            (interactionPlusInterior d n)) := by
  let r := 2 * n + 1
  let A := sym2FinsetMap (Function.Embedding.subtype
    (fun x : Site d ↦ x ∈ interactionBoxVertices d r)) E
  have hmeas : MeasurableSet (currentParityAvoidCylinder A) :=
    measurableSet_currentParityAvoidCylinder A
  calc
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder A) =
      (boundaryCurrentPMF (interactionBoxGraph d r) beta
        (interactionBoxCoupling J r) hbeta.le
        (fun e ↦ hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n)).toMeasure
        {m | Disjoint (currentParitySupport (interactionBoxGraph d r) m) E} := by
      change Measure.map (extendInteractionBoxCurrent d r)
        (boundaryCurrentPMF (interactionBoxGraph d r) beta
          (interactionBoxCoupling J r) hbeta.le
          (fun e ↦ hJ (Sym2.map Subtype.val e))
          (interactionPlusInterior d n)).toMeasure
          (currentParityAvoidCylinder A) = _
      rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d r) hmeas,
        preimage_currentParityAvoidCylinder_extendInteractionBoxCurrent
          d r E hE]
    _ = _ := boundaryCurrentMeasure_parityAvoid_inhomogeneous
      (interactionBoxGraph d r) beta hbeta
      (interactionBoxCoupling J r)
      (fun e ↦ hJ (Sym2.map Subtype.val e))
      (interactionPlusInterior d n) E

theorem generalPlusBoxCurrentMeasure_parityAvoid_nonDiagonal
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) (n : Nat)
    (F : Finset (Sym2 (Site d))) :
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder (nonDiagonalEdgeFinset F)) := by
  let r := 2 * n + 1
  have hmeasF := measurableSet_currentParityAvoidCylinder F
  have hmeasD := measurableSet_currentParityAvoidCylinder
    (nonDiagonalEdgeFinset F)
  change Measure.map (extendInteractionBoxCurrent d r)
      ((boundaryCurrentPMF (interactionBoxGraph d r) beta
        (interactionBoxCoupling J r) hbeta
        (fun e ↦ hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n)).toMeasure)
        (currentParityAvoidCylinder F) =
    Measure.map (extendInteractionBoxCurrent d r)
      ((boundaryCurrentPMF (interactionBoxGraph d r) beta
        (interactionBoxCoupling J r) hbeta
        (fun e ↦ hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n)).toMeasure)
        (currentParityAvoidCylinder (nonDiagonalEdgeFinset F))
  rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d r) hmeasF,
    Measure.map_apply (measurable_extendInteractionBoxCurrent d r) hmeasD,
    preimage_currentParityAvoidCylinder_nonDiagonal]

theorem boundaryNonnegativeCurrentLocalParityPMF
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (S : Finset G.edgeFinset) :
    PMF.map currentLocalParity
        (PMF.map (restrictCurrent S)
          (boundaryCurrentPMF G beta J hbeta.le hJ interior)) =
      PMF.map (restrictParity G S)
        (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior) := by
  rw [boundaryNonnegativeParityPMF, PMF.map_comp, PMF.map_comp]
  congr 1
  funext m
  exact currentLocalParity_restrictCurrent_eq_restrictParity G S m



theorem generalPlusBoxCurrentMeasure_pattern_factor_nonDiagonal
    {d n : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d (2 * n + 1))
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) (a : ↑F → Nat) :
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder F {a}) =
      (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder F (currentLocalParity a)) *
        nonnegativeFiniteParityPMF F (fun e ↦ beta * J e)
          (fun e : ↑F ↦ mul_nonneg hbeta.le (hJ e.1))
          (currentLocalParity a) a := by
  let r := 2 * n + 1
  let G := interactionBoxGraph d r
  let S := interactionBoxLiftedEdgeIndices F hFbox hFdiag
  let Jn := interactionBoxCoupling J r
  let interior := interactionPlusInterior d n
  let p := boundaryCurrentPMF G beta Jn hbeta.le
    (fun e ↦ hJ (Sym2.map Subtype.val e)) interior
  let q := PMF.map (restrictParity G S)
    (boundaryNonnegativeParityPMF G beta Jn hbeta.le
      (fun e ↦ hJ (Sym2.map Subtype.val e)) interior)
  let a' := interactionBoxPullbackPattern F hFbox hFdiag a
  have hcurrent : PMF.map (restrictCurrent S) p =
      q.bind (nonnegativeFiniteParityPMF S
        (fun e : G.edgeFinset ↦ beta * Jn e.1)
        (fun e : ↑S ↦ mul_nonneg hbeta.le
          (hJ (Sym2.map Subtype.val e.1.1)))) := by
    exact boundaryCurrentFiniteMarginal_eq_nonnegativeParity_bind
      G beta hbeta Jn (fun e ↦ hJ (Sym2.map Subtype.val e)) interior S
  have hpoint := congrArg (fun law : PMF (↑S → Nat) ↦ law a') hcurrent
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
  change Measure.map (extendInteractionBoxCurrent d r) p.toMeasure
      (currentCylinder F {a}) =
    Measure.map (extendInteractionBoxCurrent d r) p.toMeasure
      (currentParityPatternCylinder F (currentLocalParity a)) * _
  rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d r) hsingle,
    preimage_currentCylinder_singleton_extendInteractionBoxCurrent
      F hFbox hFdiag a,
    Measure.map_apply (measurable_extendInteractionBoxCurrent d r) hparMeas,
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
  rw [boundaryNonnegativeCurrentLocalParityPMF G beta hbeta Jn
    (fun e ↦ hJ (Sym2.map Subtype.val e)) interior S]

end StatMech.FrontierB
