/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsoradialKacWardFormanProduct
import Code.FrontierA.IsoradialCellularRibbonDuality













namespace StatMech.FrontierA

open Finset
open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


abbrev finiteMapFiber {A B : Type*} (map : A -> B) (b : B) :=
  {a : A // map a = b}



theorem sum_boolOrientations_eq_prod_formanCycleCoefficient
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (holonomy : Component -> Complex) :
    (∑ orientation : Component -> Bool,
        ∏ component : Component,
          if orientation component then 1 - holonomy component
          else 1 - (holonomy component)⁻¹) =
      ∏ component : Component,
        formanCycleCoefficient (holonomy component) := by
  calc
    (∑ orientation : Component -> Bool,
        ∏ component : Component,
          if orientation component then 1 - holonomy component
          else 1 - (holonomy component)⁻¹) =
      ∏ component : Component,
        ∑ orientation : Bool,
          if orientation then 1 - holonomy component
          else 1 - (holonomy component)⁻¹ :=
      (Fintype.prod_sum fun (component : Component) (orientation : Bool) =>
        if orientation then 1 - holonomy component
        else 1 - (holonomy component)⁻¹).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro component _
      simp [formanCycleCoefficient]
      ring





structure GenusZeroOneRibbonComponentIdentification
    (Component : Type*) [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex) where
  genus_le_one : C.genus <= 1
  outgoingEdgeSet : (V -> V) -> Finset E
  conductanceMonomial : forall next : V -> V,
    finiteCRSFOutgoingConductance conductance next =
      ∏ e ∈ outgoingEdgeSet next, weight e
  supported : Finset E -> Prop
  components : Finset E -> Finset Component
  componentHolonomy : Finset E -> Component -> Complex
  boundaryCoefficient_supported : forall (F : Finset E), supported F ->
    ribbonBoundaryCharacterCoefficient R character F =
      ∏ component : {component // component ∈ components F},
        formanCycleCoefficient (componentHolonomy F component)
  boundaryCoefficient_unsupported : forall (F : Finset E), ¬ supported F ->
    ribbonBoundaryCharacterCoefficient R character F = 0
  fiberEmpty_unsupported : forall (F : Finset E), ¬ supported F ->
    IsEmpty (finiteMapFiber outgoingEdgeSet F)
  fiberEquivOrientations : forall (F : Finset E), supported F ->
    finiteMapFiber outgoingEdgeSet F ≃
      ({component // component ∈ components F} -> Bool)
  formanFactor_orientation : forall (F : Finset E) (hF : supported F)
      (next : finiteMapFiber outgoingEdgeSet F),
    (∏ cycle : finiteCRSFAtomicCycle next.1,
        (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)) =
      ∏ component : {component // component ∈ components F},
        if (fiberEquivOrientations F hF next) component then
          1 - componentHolonomy F component
        else 1 - (componentHolonomy F component)⁻¹



structure GenusZeroOneRibbonFormanIdentification
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex) where
  genus_le_one : C.genus <= 1
  outgoingEdgeSet : (V -> V) -> Finset E
  conductanceMonomial : forall next : V -> V,
    finiteCRSFOutgoingConductance conductance next =
      ∏ e ∈ outgoingEdgeSet next, weight e
  boundaryCoefficientFiber : forall F : Finset E,
    ribbonBoundaryCharacterCoefficient R character F =
      ∑ next : finiteMapFiber outgoingEdgeSet F,
        ∏ cycle : finiteCRSFAtomicCycle next.1,
          (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)

namespace GenusZeroOneRibbonComponentIdentification



theorem boundaryCoefficientFiber
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (I : GenusZeroOneRibbonComponentIdentification Component
      R C character weight conductance transport) (F : Finset E) :
    ribbonBoundaryCharacterCoefficient R character F =
      ∑ next : finiteMapFiber I.outgoingEdgeSet F,
        ∏ cycle : finiteCRSFAtomicCycle next.1,
          (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
  by_cases hF : I.supported F
  · rw [I.boundaryCoefficient_supported F hF]
    calc
      (∏ component : {component // component ∈ I.components F},
          formanCycleCoefficient (I.componentHolonomy F component)) =
        ∑ orientation :
            ({component // component ∈ I.components F} -> Bool),
          ∏ component : {component // component ∈ I.components F},
            if orientation component then
              1 - I.componentHolonomy F component
            else 1 - (I.componentHolonomy F component)⁻¹ :=
        (sum_boolOrientations_eq_prod_formanCycleCoefficient
          (fun component : {component // component ∈ I.components F} =>
            I.componentHolonomy F component)).symm
      _ = ∑ next : finiteMapFiber I.outgoingEdgeSet F,
          ∏ cycle : finiteCRSFAtomicCycle next.1,
            (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
        symm
        exact Fintype.sum_equiv (I.fiberEquivOrientations F hF)
          (fun next : finiteMapFiber I.outgoingEdgeSet F =>
            ∏ cycle : finiteCRSFAtomicCycle next.1,
              (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle))
          (fun orientation :
              ({component // component ∈ I.components F} -> Bool) =>
            ∏ component : {component // component ∈ I.components F},
              if orientation component then
                1 - I.componentHolonomy F component
              else 1 - (I.componentHolonomy F component)⁻¹)
          (I.formanFactor_orientation F hF)
  · rw [I.boundaryCoefficient_unsupported F hF]
    letI : IsEmpty (finiteMapFiber I.outgoingEdgeSet F) :=
      I.fiberEmpty_unsupported F hF
    simp



noncomputable def toFormanIdentification
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (I : GenusZeroOneRibbonComponentIdentification Component
      R C character weight conductance transport) :
    GenusZeroOneRibbonFormanIdentification
      R C character weight conductance transport where
  genus_le_one := I.genus_le_one
  outgoingEdgeSet := I.outgoingEdgeSet
  conductanceMonomial := I.conductanceMonomial
  boundaryCoefficientFiber :=
    I.boundaryCoefficientFiber R C character weight conductance transport

end GenusZeroOneRibbonComponentIdentification

namespace GenusZeroOneRibbonFormanIdentification



theorem ribbonSubgraphSum_eq_laplacianDet
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (I : GenusZeroOneRibbonFormanIdentification
      R C character weight conductance transport) :
    kwDualSubgraphSum
        (ribbonBoundaryCharacterCoefficient R character) weight =
      (finiteTwistedLaplacian conductance transport).det := by
  rw [det_finiteTwistedLaplacian_eq_sum_outgoing_mul_formanProduct]
  unfold kwDualSubgraphSum
  calc
    (∑ F : Finset E,
        ribbonBoundaryCharacterCoefficient R character F *
          ∏ e ∈ F, weight e) =
      ∑ F : Finset E,
        (∑ next : finiteMapFiber I.outgoingEdgeSet F,
          ∏ cycle : finiteCRSFAtomicCycle next.1,
            (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)) *
          ∏ e ∈ F, weight e := by
      apply Finset.sum_congr rfl
      intro F _
      rw [I.boundaryCoefficientFiber F]
    _ = ∑ F : Finset E,
        ∑ next : finiteMapFiber I.outgoingEdgeSet F,
          finiteCRSFOutgoingConductance conductance next.1 *
            ∏ cycle : finiteCRSFAtomicCycle next.1,
              (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
      apply Finset.sum_congr rfl
      intro F _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro next _
      rw [I.conductanceMonomial next.1, next.2]
      ring
    _ = ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          ∏ cycle : finiteCRSFAtomicCycle next,
            (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
      exact Fintype.sum_fiberwise I.outgoingEdgeSet
        (fun next : V -> V =>
          finiteCRSFOutgoingConductance conductance next *
            ∏ cycle : finiteCRSFAtomicCycle next,
              (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle))

end GenusZeroOneRibbonFormanIdentification


noncomputable def matrixDetPermutationTerm
    (matrix : Matrix Q Q Complex) (sigma : Equiv.Perm Q) : Complex :=
  Equiv.Perm.sign sigma • ∏ q : Q, matrix (sigma q) q

theorem matrix_det_eq_sum_permutationTerm (matrix : Matrix Q Q Complex) :
    matrix.det =
      ∑ sigma : Equiv.Perm Q, matrixDetPermutationTerm matrix sigma := by
  rw [Matrix.det_apply]
  rfl



noncomputable def criticalKacWardRibbonPrefactor
    (thetaEdge : E -> Real) (exceptional : V -> Bool) : Complex :=
  (-1 : Complex) ^ Fintype.card V *
    kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
    (∏ v : V, coneQuarterPhase exceptional v) *
    kwLaplacianEdgePrefactor thetaEdge




structure CriticalKacWardRibbonCoefficientIdentification
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (thetaEdge : E -> Real)
    (exceptional : V -> Bool) where
  permutationEdgeSet : Equiv.Perm Q -> Finset E
  coefficientFiber : forall F : Finset E,
    (∑ sigma : finiteMapFiber permutationEdgeSet F,
        matrixDetPermutationTerm (1 - kacWard) sigma.1) =
      criticalKacWardRibbonPrefactor thetaEdge exceptional *
        (ribbonBoundaryCharacterCoefficient R character F *
          ∏ e ∈ F, isoradialCriticalMu (thetaEdge e))




structure CriticalKacWardRibbonExpansion
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (thetaEdge : E -> Real)
    (exceptional : V -> Bool) where
  expansion :
    (1 - kacWard).det =
      (((-1 : Complex) ^ Fintype.card V *
          kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
          (∏ v : V, coneQuarterPhase exceptional v) *
          kwLaplacianEdgePrefactor thetaEdge) *
        kwDualSubgraphSum
          (ribbonBoundaryCharacterCoefficient R character)
          (fun e => isoradialCriticalMu (thetaEdge e)))

namespace CriticalKacWardRibbonCoefficientIdentification

omit [DecidableEq V] in


theorem expansion
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (thetaEdge : E -> Real)
    (exceptional : V -> Bool)
    (I : CriticalKacWardRibbonCoefficientIdentification
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      criticalKacWardRibbonPrefactor thetaEdge exceptional *
        kwDualSubgraphSum
          (ribbonBoundaryCharacterCoefficient R character)
          (fun e => isoradialCriticalMu (thetaEdge e)) := by
  rw [matrix_det_eq_sum_permutationTerm]
  calc
    (∑ sigma : Equiv.Perm Q,
        matrixDetPermutationTerm (1 - kacWard) sigma) =
      ∑ F : Finset E,
        ∑ sigma : finiteMapFiber I.permutationEdgeSet F,
          matrixDetPermutationTerm (1 - kacWard) sigma.1 :=
      (Fintype.sum_fiberwise I.permutationEdgeSet
        (matrixDetPermutationTerm (1 - kacWard))).symm
    _ = criticalKacWardRibbonPrefactor thetaEdge exceptional *
        kwDualSubgraphSum
          (ribbonBoundaryCharacterCoefficient R character)
          (fun e => isoradialCriticalMu (thetaEdge e)) := by
      unfold kwDualSubgraphSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      rw [I.coefficientFiber F]



noncomputable def toRibbonExpansion
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (thetaEdge : E -> Real)
    (exceptional : V -> Bool)
    (I : CriticalKacWardRibbonCoefficientIdentification
      R character kacWard thetaEdge exceptional) :
    CriticalKacWardRibbonExpansion
      R character kacWard thetaEdge exceptional where
  expansion := by
    change (1 - kacWard).det =
      criticalKacWardRibbonPrefactor thetaEdge exceptional * _
    exact I.expansion R character kacWard thetaEdge exceptional

end CriticalKacWardRibbonCoefficientIdentification



theorem criticalKacWard_det_eq_laplacian_of_ribbonIdentification
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (I : GenusZeroOneRibbonFormanIdentification R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport)
    (K : CriticalKacWardRibbonExpansion
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
  rw [K.expansion,
    I.ribbonSubgraphSum_eq_laplacianDet,
    det_finiteTwistedLaplacian_isoradialMu]
  calc
    ((-1 : Complex) ^ Fintype.card V *
          kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
          (∏ v : V, coneQuarterPhase exceptional v) *
          kwLaplacianEdgePrefactor thetaEdge) *
        (Complex.I ^ Fintype.card V *
          (finiteTwistedLaplacian
            (isoradialLaplacianConductance thetaVertex) transport).det) =
      (((-1 : Complex) ^ Fintype.card V *
          (∏ v : V, coneQuarterPhase exceptional v) *
          Complex.I ^ Fintype.card V) *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det) := by
      ring
    _ = _ := by rw [conePhase_prefactor_eq_exceptionSign]

omit [DecidableEq E] in



theorem criticalKacWard_det_eq_laplacian_of_componentIdentification
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (I : GenusZeroOneRibbonComponentIdentification Component R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport)
    (K : CriticalKacWardRibbonExpansion
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
  classical
  exact criticalKacWard_det_eq_laplacian_of_ribbonIdentification
    R C character kacWard thetaVertex thetaEdge transport exceptional
    (I.toFormanIdentification R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport) K




theorem criticalKacWard_det_eq_laplacian_of_localIdentifications
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (I : GenusZeroOneRibbonComponentIdentification Component R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport)
    (K : CriticalKacWardRibbonCoefficientIdentification
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det :=
  criticalKacWard_det_eq_laplacian_of_componentIdentification
    R C character kacWard thetaVertex thetaEdge transport exceptional I
      (K.toRibbonExpansion R character kacWard thetaEdge exceptional)




structure CriticalIsoradialEmbeddingRibbonCertificate
    (Component : Type*) [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool) where
  componentIdentification :
    GenusZeroOneRibbonComponentIdentification Component R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport
  coefficientIdentification :
    CriticalKacWardRibbonCoefficientIdentification
      R character kacWard thetaEdge exceptional



theorem CriticalIsoradialEmbeddingRibbonCertificate.det_eq_laplacian
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (certificate : CriticalIsoradialEmbeddingRibbonCertificate Component
      R C character kacWard thetaVertex thetaEdge transport exceptional) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det :=
  criticalKacWard_det_eq_laplacian_of_localIdentifications
    R C character kacWard thetaVertex thetaEdge transport exceptional
      certificate.componentIdentification
      certificate.coefficientIdentification

end StatMech.FrontierA
