/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Certificate
import Code.Exact3D.FinitePlusTailClosedBall













namespace StatMech
namespace Exact3D

namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type}



abbrev hamiltonian (_C : FinitePlusTailClosedBallContractionCertificate n α) :
    EffectiveHamiltonian where
  carrier := FinitePlusTailState n α



noncomputable def rgMap
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) : BlockSpinMap C.hamiltonian where
  scale := scale
  map := C.contraction.map

@[simp] theorem rgMap_map
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) :
    (C.rgMap scale).map = C.contraction.map :=
  rfl



@[simp] theorem rgMap_scale
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) :
    (C.rgMap scale).scale = scale :=
  rfl



noncomputable def fixedPointData
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (thermal : ℝ) (hthermal : 1 < thermal) :
    RGFixedPointData C.hamiltonian (C.rgMap scale) where
  fixedPoint := C.fixedPoint
  fixedPoint_eq := C.fixedPoint_isFixed
  thermalEigenvalue := thermal
  thermal_gt_one := hthermal


noncomputable def certificate {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) : RGCertificate M where
  H := C.hamiltonian
  R := C.rgMap scale
  fixedPointData := C.fixedPointData scale thermal hthermal


@[simp] theorem certificate_thermalEigenvalue_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).thermalEigenvalue = thermal :=
  rfl


@[simp] theorem certificate_scale_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).scale = scale :=
  rfl

@[simp] theorem certificate_fixedPoint_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).fixedPointData.fixedPoint =
      C.fixedPoint :=
  rfl

@[simp] theorem certificate_R_map_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).R.map = C.contraction.map :=
  rfl



theorem certificate_predictedExponent_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).predictedExponent =
      predictedNu scale thermal :=
  rfl


theorem certificate_fixedPointEnclosure {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).FixedPointEnclosure :=
  C.fixedPoint_isFixed



theorem certificate_finiteCaseChecks {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).FiniteCaseChecks :=
  trivial



theorem certificate_tailBounds {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).TailBounds :=
  trivial



theorem certificate_linearizationEnclosure {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).LinearizationEnclosure :=
  (C.certificate scale M thermal hthermal).linearizationEnclosure_of_thermal_gt_one



theorem certificate_hyperbolicSplitting {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).HyperbolicSplitting :=
  (C.certificate scale M thermal hthermal).hyperbolicSplitting_of_thermal_gt_one



theorem certificate_orbitEntry {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.certificate scale M thermal hthermal).OrbitEntry :=
  trivial



theorem certificate_fixedPoint_mem_closedBall {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    FinitePlusTailState.ClosedBall C.center C.radius
      (C.certificate scale M thermal hthermal).fixedPointData.fixedPoint := by
  simpa [certificate, fixedPointData] using C.fixedPoint_mem


theorem rgMap_iterate_eq
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (k : ℕ) (x : FinitePlusTailState n α) :
    ((C.rgMap scale).map^[k]) x = C.contraction.iterate k x := by
  induction k with
  | zero =>
      simp [FinitePlusTailLipschitzCertificate.iterate]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simpa [rgMap, FinitePlusTailLipschitzCertificate.iterate] using
        congrArg C.contraction.map ih


theorem rgMap_iterate_mem_closedBall
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale)
    {x : FinitePlusTailState n α}
    (hx : FinitePlusTailState.ClosedBall C.center C.radius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall C.center C.radius
      (((C.rgMap scale).map^[k]) x) := by
  rw [C.rgMap_iterate_eq scale k x]
  exact C.iterate_mem hx k



theorem certificate_iterate_mem_closedBall {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {x : (C.certificate scale M thermal hthermal).H.carrier}
    (hx : FinitePlusTailState.ClosedBall C.center C.radius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall C.center C.radius
      ((((C.certificate scale M thermal hthermal).R.map)^[k]) x) := by
  simpa [certificate] using C.rgMap_iterate_mem_closedBall scale hx k



theorem certificate_valid_of_bridge {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (C.certificate scale M thermal hthermal).RGToExponentBridge
        correlationLength) :
    (C.certificate scale M thermal hthermal).Valid correlationLength where
  finiteCaseChecks :=
    C.certificate_finiteCaseChecks scale M thermal hthermal
  tailBounds := C.certificate_tailBounds scale M thermal hthermal
  fixedPointEnclosure :=
    C.certificate_fixedPointEnclosure scale M thermal hthermal
  linearizationEnclosure :=
    C.certificate_linearizationEnclosure scale M thermal hthermal
  hyperbolicSplitting :=
    C.certificate_hyperbolicSplitting scale M thermal hthermal
  orbitEntry := C.certificate_orbitEntry scale M thermal hthermal
  bridge := hbridge



theorem certificate_rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (C.certificate scale M thermal hthermal).predictedExponent) :
    (C.certificate scale M thermal hthermal).RGToExponentBridge
      correlationLength := by
  simpa [RGCertificate.RGToExponentBridge] using hν



theorem certificate_valid_of_hasCriticalNu {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (C.certificate scale M thermal hthermal).predictedExponent) :
    (C.certificate scale M thermal hthermal).Valid correlationLength :=
  C.certificate_valid_of_bridge
    scale M thermal hthermal correlationLength
    (C.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M thermal hthermal correlationLength hν)


theorem certificate_hasCriticalNu_of_bridge {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (C.certificate scale M thermal hthermal).RGToExponentBridge
        correlationLength) :
    HasCriticalNu M correlationLength
      (C.certificate scale M thermal hthermal).predictedExponent :=
  (C.certificate_valid_of_bridge
    scale M thermal hthermal correlationLength hbridge).hasCriticalNu




@[simp] theorem with_larger_radius_certificate_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.with_larger_radius hradius).certificate scale M thermal hthermal =
      C.certificate scale M thermal hthermal :=
  rfl



theorem with_larger_radius_rgToExponentBridge {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (C.certificate scale M thermal hthermal).RGToExponentBridge
        correlationLength) :
    ((C.with_larger_radius hradius).certificate scale M thermal hthermal).RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_radius_valid {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (C.certificate scale M thermal hthermal).Valid correlationLength) :
    ((C.with_larger_radius hradius).certificate scale M thermal hthermal).Valid
      correlationLength := by
  simpa using hvalid



theorem with_larger_radius_hasCriticalNu {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (C.certificate scale M thermal hthermal).predictedExponent) :
    HasCriticalNu M correlationLength
      ((C.with_larger_radius hradius).certificate
        scale M thermal hthermal).predictedExponent := by
  simpa using hν




@[simp] theorem with_larger_residual_certificate_eq {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget :
      residual' + C.contraction.c * C.radius ≤ C.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal) :
    (C.with_larger_residual hresidual hbudget).certificate
      scale M thermal hthermal =
      C.certificate scale M thermal hthermal :=
  rfl



theorem with_larger_residual_rgToExponentBridge {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget :
      residual' + C.contraction.c * C.radius ≤ C.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hbridge :
      (C.certificate scale M thermal hthermal).RGToExponentBridge
        correlationLength) :
    ((C.with_larger_residual hresidual hbudget).certificate
      scale M thermal hthermal).RGToExponentBridge correlationLength := by
  simpa using hbridge



theorem with_larger_residual_valid {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget :
      residual' + C.contraction.c * C.radius ≤ C.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hvalid :
      (C.certificate scale M thermal hthermal).Valid correlationLength) :
    ((C.with_larger_residual hresidual hbudget).certificate
      scale M thermal hthermal).Valid correlationLength := by
  simpa using hvalid



theorem with_larger_residual_hasCriticalNu {ι : Type*}
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget :
      residual' + C.contraction.c * C.radius ≤ C.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    (thermal : ℝ) (hthermal : 1 < thermal)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (C.certificate scale M thermal hthermal).predictedExponent) :
    HasCriticalNu M correlationLength
      ((C.with_larger_residual hresidual hbudget).certificate
        scale M thermal hthermal).predictedExponent := by
  simpa using hν

end FinitePlusTailClosedBallContractionCertificate






structure FinitePlusTailClosedBallRGPackage (n : ℕ) (α : Type) where
  closedBall : FinitePlusTailClosedBallContractionCertificate n α
  thermal : ℝ
  thermal_gt_one : 1 < thermal

namespace FinitePlusTailClosedBallRGPackage

variable {n : ℕ} {α : Type}


noncomputable def certificate {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) : RGCertificate M :=
  P.closedBall.certificate scale M P.thermal P.thermal_gt_one

@[simp] theorem certificate_retarget {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ) :
    P.certificate scale N = (P.certificate scale M).retarget N :=
  rfl


@[simp] theorem certificate_thermalEigenvalue_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).thermalEigenvalue = P.thermal :=
  rfl


@[simp] theorem certificate_scale_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).scale = scale :=
  rfl



@[simp] theorem certificate_fixedPoint_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).fixedPointData.fixedPoint =
      P.closedBall.fixedPoint :=
  rfl



@[simp] theorem certificate_R_map_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).R.map = P.closedBall.contraction.map :=
  rfl



theorem certificate_predictedExponent_eq {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).predictedExponent =
      predictedNu scale P.thermal :=
  rfl


theorem mapsClosedBall
    (P : FinitePlusTailClosedBallRGPackage n α) :
    FinitePlusTailState.MapsClosedBall
      P.closedBall.contraction.map P.closedBall.center P.closedBall.radius :=
  P.closedBall.mapsClosedBall



theorem fixedPoint_mem_closedBall
    (P : FinitePlusTailClosedBallRGPackage n α) :
    FinitePlusTailState.ClosedBall
      P.closedBall.center P.closedBall.radius P.closedBall.fixedPoint :=
  P.closedBall.fixedPoint_mem


theorem certificate_fixedPointEnclosure {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).FixedPointEnclosure := by
  simpa [certificate] using
    P.closedBall.certificate_fixedPointEnclosure
      scale M P.thermal P.thermal_gt_one



theorem certificate_finiteCaseChecks {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).FiniteCaseChecks := by
  simpa [certificate] using
    P.closedBall.certificate_finiteCaseChecks
      scale M P.thermal P.thermal_gt_one



theorem certificate_tailBounds {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).TailBounds := by
  simpa [certificate] using
    P.closedBall.certificate_tailBounds
      scale M P.thermal P.thermal_gt_one



theorem certificate_linearizationEnclosure {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).LinearizationEnclosure := by
  simpa [certificate] using
    P.closedBall.certificate_linearizationEnclosure
      scale M P.thermal P.thermal_gt_one



theorem certificate_hyperbolicSplitting {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).HyperbolicSplitting := by
  simpa [certificate] using
    P.closedBall.certificate_hyperbolicSplitting
      scale M P.thermal P.thermal_gt_one



theorem certificate_orbitEntry {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).OrbitEntry := by
  simpa [certificate] using
    P.closedBall.certificate_orbitEntry
      scale M P.thermal P.thermal_gt_one



theorem certificate_fixedPoint_mem_closedBall {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    FinitePlusTailState.ClosedBall
      P.closedBall.center P.closedBall.radius
      (P.certificate scale M).fixedPointData.fixedPoint := by
  simpa [certificate] using
    P.closedBall.certificate_fixedPoint_mem_closedBall
      scale M P.thermal P.thermal_gt_one



theorem certificate_iterate_mem_closedBall {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {x : (P.certificate scale M).H.carrier}
    (hx :
      FinitePlusTailState.ClosedBall
        P.closedBall.center P.closedBall.radius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall
      P.closedBall.center P.closedBall.radius
      ((((P.certificate scale M).R.map)^[k]) x) := by
  simpa [certificate] using
    P.closedBall.certificate_iterate_mem_closedBall
      scale M P.thermal P.thermal_gt_one hx k



theorem certificate_valid_of_bridge {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    (P.certificate scale M).Valid correlationLength := by
  simpa [certificate] using
    P.closedBall.certificate_valid_of_bridge
      scale M P.thermal P.thermal_gt_one correlationLength hbridge



theorem certificate_rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    (P.certificate scale M).RGToExponentBridge correlationLength := by
  simpa [certificate] using
    P.closedBall.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M P.thermal P.thermal_gt_one correlationLength hν



theorem certificate_valid_of_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M correlationLength hν)


theorem certificate_hasCriticalNu_of_bridge {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_bridge
    scale M correlationLength hbridge).hasCriticalNu



theorem certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
    {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred



theorem certificate_valid_of_bridge_congr_predictedExponent {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
      scale M hpred hbridge)



theorem certificate_hasCriticalNu_of_bridge_congr_predictedExponent
    {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_bridge_congr_predictedExponent
    scale M hpred hbridge).hasCriticalNu



theorem certificate_retarget_rgToExponentBridge {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc



theorem certificate_retarget_valid {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale M).Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale N).Valid correlationLength := by
  simpa using hvalid.retarget hβc



theorem certificate_retarget_hasCriticalNu {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      (P.certificate scale N).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc



theorem certificate_retarget_rgToExponentBridge_iff {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale M).RGToExponentBridge correlationLength ↔
      (P.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := P.certificate scale M) (N := N) hβc)



theorem certificate_retarget_valid_iff {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale M).Valid correlationLength ↔
      (P.certificate scale N).Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := P.certificate scale M) (N := N) hβc)



theorem certificate_retarget_hasCriticalNu_iff {ι κ : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent ↔
      HasCriticalNu N correlationLength
        (P.certificate scale N).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := P.certificate scale M) (N := N) hβc)



def with_larger_radius
    (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius') :
    FinitePlusTailClosedBallRGPackage n α where
  closedBall := P.closedBall.with_larger_radius hradius
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one

@[simp] theorem with_larger_radius_closedBall
    (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius') :
    (P.with_larger_radius hradius).closedBall =
      P.closedBall.with_larger_radius hradius :=
  rfl

@[simp] theorem with_larger_radius_closedBall_radius
    (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius') :
    (P.with_larger_radius hradius).closedBall.radius = radius' :=
  rfl

@[simp] theorem with_larger_radius_closedBall_fixedPoint
    (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius') :
    (P.with_larger_radius hradius).closedBall.fixedPoint =
      P.closedBall.fixedPoint :=
  rfl

@[simp] theorem with_larger_radius_thermal
    (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius') :
    (P.with_larger_radius hradius).thermal = P.thermal :=
  rfl

@[simp] theorem with_larger_radius_certificate_thermalEigenvalue_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_radius hradius).certificate scale M).thermalEigenvalue =
      P.thermal :=
  rfl



@[simp] theorem with_larger_radius_certificate_scale_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_radius hradius).certificate scale M).scale = scale :=
  rfl




@[simp] theorem with_larger_radius_certificate_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.with_larger_radius hradius).certificate scale M =
      P.certificate scale M :=
  rfl



theorem with_larger_radius_certificate_predictedExponent_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_radius hradius).certificate scale M).predictedExponent =
      (P.certificate scale M).predictedExponent :=
  rfl



theorem with_larger_radius_rgToExponentBridge {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    ((P.with_larger_radius hradius).certificate scale M).RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_radius_valid {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale M).Valid correlationLength) :
    ((P.with_larger_radius hradius).certificate scale M).Valid
      correlationLength := by
  simpa using hvalid



theorem with_larger_radius_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {radius' : ℝ} (hradius : P.closedBall.radius ≤ radius')
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_radius hradius).certificate
        scale M).predictedExponent := by
  simpa using hν



def with_larger_residual
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    FinitePlusTailClosedBallRGPackage n α where
  closedBall := P.closedBall.with_larger_residual hresidual hbudget
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one

@[simp] theorem with_larger_residual_closedBall
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    (P.with_larger_residual hresidual hbudget).closedBall =
      P.closedBall.with_larger_residual hresidual hbudget :=
  rfl

@[simp] theorem with_larger_residual_closedBall_residual
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    (P.with_larger_residual hresidual hbudget).closedBall.residual =
      residual' :=
  rfl

@[simp] theorem with_larger_residual_closedBall_fixedPoint
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    (P.with_larger_residual hresidual hbudget).closedBall.fixedPoint =
      P.closedBall.fixedPoint :=
  rfl

@[simp] theorem with_larger_residual_thermal
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    (P.with_larger_residual hresidual hbudget).thermal = P.thermal :=
  rfl

@[simp] theorem with_larger_residual_certificate_thermalEigenvalue_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_residual hresidual hbudget).certificate
      scale M).thermalEigenvalue = P.thermal :=
  rfl



@[simp] theorem with_larger_residual_certificate_scale_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_residual hresidual hbudget).certificate scale M).scale =
      scale :=
  rfl




@[simp] theorem with_larger_residual_certificate_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.with_larger_residual hresidual hbudget).certificate scale M =
      P.certificate scale M :=
  rfl



theorem with_larger_residual_certificate_predictedExponent_eq
    {ι : Type*} (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_residual hresidual hbudget).certificate
      scale M).predictedExponent =
      (P.certificate scale M).predictedExponent :=
  rfl



theorem with_larger_residual_rgToExponentBridge {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    ((P.with_larger_residual hresidual hbudget).certificate scale M).RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_residual_valid {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale M).Valid correlationLength) :
    ((P.with_larger_residual hresidual hbudget).certificate scale M).Valid
      correlationLength := by
  simpa using hvalid



theorem with_larger_residual_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_residual hresidual hbudget).certificate
        scale M).predictedExponent := by
  simpa using hν

end FinitePlusTailClosedBallRGPackage

end Exact3D
end StatMech
