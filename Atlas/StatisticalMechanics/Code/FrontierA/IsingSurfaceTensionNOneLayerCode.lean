/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOneRawGenerated










open Finset

namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising


def nOneLayerCodeEquiv : Fin 512 ≃ RectangularLayerConfig 3 3 :=
  (finFunctionFinEquiv (m := 2) (n := 9)).symm |>.trans
    (Equiv.arrowCongr
      (finProdFinEquiv (m := 3) (n := 3)).symm finTwoEquiv)

@[simp] theorem nOneLayerCodeEquiv_apply
    (s : Fin 512) (p : Fin 3 × Fin 3) :
    nOneLayerCodeEquiv s p = layerCodeBit s p := by
  simp [nOneLayerCodeEquiv, layerCodeBit, finFunctionFinEquiv,
    finProdFinEquiv, finTwoEquiv, Nat.testBit_eq_decide_div_mod_eq,
    Nat.add_comm, Bool.beq_eq_decide_eq, Fin.ext_iff]

@[simp] theorem spin_nOneLayerCodeEquiv
    (s : Fin 512) (p : Fin 3 × Fin 3) :
    spin (nOneLayerCodeEquiv s) p = (spinInt s p : Real) := by
  simp [spin, spinInt, nOneLayerCodeEquiv_apply]



theorem sum_nOneLayerCodeEquiv (f : RectangularLayerConfig 3 3 -> Real) :
    (∑ s : Fin 512, f (nOneLayerCodeEquiv s)) = ∑ s, f s := by
  exact Equiv.sum_comp nOneLayerCodeEquiv f

theorem rectangularLayerInternalInteraction_nOneLayerCodeEquiv
    (s : Fin 512) :
    rectangularLayerInternalInteraction (nOneLayerCodeEquiv s) =
      (layerInternalInt s : Real) := by
  simp [rectangularLayerInternalInteraction, layerInternalInt,
    spin_nOneLayerCodeEquiv, Fin.sum_univ_succ, spinInt, layerCodeBit,
    spinCode]
  ring

theorem rectangularLayerLateralInteraction_nOneLayerCodeEquiv
    (s : Fin 512) :
    rectangularLayerInternalInteraction (nOneLayerCodeEquiv s) +
        ∑ p : Fin 3 × Fin 3,
          rectangularLayerBoundaryDegree p *
            spin (nOneLayerCodeEquiv s) p =
      (layerLateralInt s : Real) := by
  rw [Fintype.sum_prod_type]
  simp [rectangularLayerInternalInteraction, rectangularLayerBoundaryDegree,
    layerLateralInt, layerInternalInt, spin_nOneLayerCodeEquiv,
    Fin.sum_univ_succ, spinInt, layerCodeBit, spinCode]
  ring_nf

theorem rectangularLayerFaceInteraction_nOneLayerCodeEquiv
    (s : Fin 512) :
    (∑ p : Fin 3 × Fin 3, spin (nOneLayerCodeEquiv s) p) =
      (layerFaceInt s : Real) := by
  rw [Fintype.sum_prod_type]
  simp [layerFaceInt, spin_nOneLayerCodeEquiv, Fin.sum_univ_succ,
    spinInt, layerCodeBit, spinCode]
  ring

theorem rectangularLayerSeamInteraction_nOneLayerCodeEquiv
    (s t : Fin 512) :
    oddPrismLayerSeamInteraction 1
        (nOneLayerCodeEquiv s) (nOneLayerCodeEquiv t) =
      (layerDotInt s t : Real) := by
  unfold oddPrismLayerSeamInteraction
  rw [Fintype.sum_prod_type]
  simp [layerDotInt, spin_nOneLayerCodeEquiv, Fin.sum_univ_succ,
    spinInt, layerCodeBit, spinCode]
  ring

theorem rectangularLayerBoltzmannInteraction_nOneLayerCodeEquiv
    (beta : Real) (s : Fin 512) :
    rectangularLayerBoltzmannInteraction 1 beta (nOneLayerCodeEquiv s) =
      beta * (layerLateralInt s : Real) := by
  rw [rectangularLayerBoltzmannInteraction]
  rw [rectangularLayerLateralInteraction_nOneLayerCodeEquiv]
  ring

theorem rectangularLayerFaceBoundary_nOneLayerCodeEquiv
    (beta : Real) (s : Fin 512) :
    rectangularLayerFaceBoundary 1 beta (nOneLayerCodeEquiv s) =
      beta * (layerFaceInt s : Real) := by
  rw [rectangularLayerFaceBoundary]
  rw [rectangularLayerFaceInteraction_nOneLayerCodeEquiv]
  ring

theorem rectangularLayerVerticalInteraction_nOneLayerCodeEquiv
    (beta : Real) (s t : Fin 512) :
    rectangularLayerVerticalInteraction 1 beta
        (nOneLayerCodeEquiv s) (nOneLayerCodeEquiv t) =
      beta * (layerDotInt s t : Real) := by
  rw [rectangularLayerVerticalInteraction]
  rw [show (∑ p : Fin 3 × Fin 3,
      spin (nOneLayerCodeEquiv s) p * spin (nOneLayerCodeEquiv t) p) =
        oddPrismLayerSeamInteraction 1
          (nOneLayerCodeEquiv s) (nOneLayerCodeEquiv t) by rfl]
  rw [rectangularLayerSeamInteraction_nOneLayerCodeEquiv]
  ring

theorem oddPrismUpperConditionedVector_nOneLayerCodeEquiv
    (beta : Real) (q : Fin 512) :
    oddPrismUpperConditionedVector beta 1 (nOneLayerCodeEquiv q) =
      Real.exp (beta *
        ((layerLateralInt q : Real) + layerFaceInt q)) := by
  simp [oddPrismUpperConditionedVector, oddPrismUpperTransferTail,
    oddPrismLayerHalfWeight, rectangularPrismTransferBoundaryVector,
    rectangularLayerBoltzmannInteraction_nOneLayerCodeEquiv,
    rectangularLayerFaceBoundary_nOneLayerCodeEquiv, Matrix.one_mulVec]
  rw [← Real.exp_add]
  congr 1
  ring

theorem oddPrismLowerConditionedVector_nOneLayerCodeEquiv
    (beta : Real) (s : Fin 512) :
    oddPrismLowerConditionedVector beta 1 (nOneLayerCodeEquiv s) =
      ∑ v : Fin 512, Real.exp (beta *
        ((layerLateralInt s : Real) + layerDotInt s v +
          layerLateralInt v + layerFaceInt v)) := by
  rw [oddPrismLowerConditionedVector, oddPrismLayerHalfWeight,
    oddPrismLowerTransferTail, pow_one]
  unfold Matrix.mulVec dotProduct
  rw [← sum_nOneLayerCodeEquiv (fun v =>
    rectangularPrismTransfer 1 beta 3 3 (nOneLayerCodeEquiv s) v *
      rectangularPrismTransferBoundaryVector 1 beta 3 3 v)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [rectangularPrismTransfer, rectangularPrismTransferBoundaryVector]
  simp only [rectangularLayerBoltzmannInteraction_nOneLayerCodeEquiv,
    rectangularLayerVerticalInteraction_nOneLayerCodeEquiv,
    rectangularLayerFaceBoundary_nOneLayerCodeEquiv]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem oddPrismPureSeamKernel_nOneLayerCodeEquiv
    (r : Real) (s q : Fin 512) :
    oddPrismPureSeamKernel r 1
        (nOneLayerCodeEquiv s) (nOneLayerCodeEquiv q) =
      Real.exp (r * (layerDotInt s q : Real)) := by
  rw [oddPrismPureSeamKernel]
  rw [rectangularLayerSeamInteraction_nOneLayerCodeEquiv]





noncomputable def nOneTransferBridgeRawMomentCodeSum (beta r : Real) : Real :=
  ∑ s : Fin 512, ∑ q : Fin 512, ∑ v : Fin 512,
    Real.exp (beta *
        ((layerLateralInt s : Real) + layerDotInt s v +
          layerLateralInt v + layerFaceInt v +
          layerLateralInt q + layerFaceInt q) +
      r * (layerDotInt s q : Real))

theorem oddPrismTransferBridgeRawMoment_one_eq_codeSum
    (beta r : Real) :
    oddPrismTransferBridgeRawMoment beta 1 r =
      nOneTransferBridgeRawMomentCodeSum beta r := by
  unfold oddPrismTransferBridgeRawMoment
    nOneTransferBridgeRawMomentCodeSum
  rw [← sum_nOneLayerCodeEquiv (fun s => ∑ q,
    oddPrismLowerConditionedVector beta 1 s *
      oddPrismUpperConditionedVector beta 1 q *
      oddPrismPureSeamKernel r 1 s q)]
  apply Finset.sum_congr rfl
  intro s _
  rw [← sum_nOneLayerCodeEquiv (fun q =>
    oddPrismLowerConditionedVector beta 1 (nOneLayerCodeEquiv s) *
      oddPrismUpperConditionedVector beta 1 q *
      oddPrismPureSeamKernel r 1 (nOneLayerCodeEquiv s) q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [oddPrismLowerConditionedVector_nOneLayerCodeEquiv,
    oddPrismUpperConditionedVector_nOneLayerCodeEquiv,
    oddPrismPureSeamKernel_nOneLayerCodeEquiv,
    Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end StatMech.FrontierA.NOneSymmetricMeanCertificate
