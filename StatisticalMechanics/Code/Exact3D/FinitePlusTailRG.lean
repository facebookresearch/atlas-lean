/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Certificate
import Code.Exact3D.FinitePlusTailCone










namespace StatMech
namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type}



abbrev hamiltonian (_H : FinitePlusTailHyperbolicSplitting n α) :
    EffectiveHamiltonian where
  carrier := State n α



noncomputable def rgMap (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) : BlockSpinMap H.hamiltonian where
  scale := scale
  map := H.step


noncomputable def fixedPointData
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) : RGFixedPointData H.hamiltonian (H.rgMap scale) where
  fixedPoint := origin
  fixedPoint_eq := H.step_origin
  thermalEigenvalue := H.thermal
  thermal_gt_one := H.thermal_gt_one



noncomputable def certificate {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) : RGCertificate M where
  H := H.hamiltonian
  R := H.rgMap scale
  fixedPointData := H.fixedPointData scale

@[simp] theorem certificate_retarget {ι κ : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ) :
    H.certificate scale N = (H.certificate scale M).retarget N :=
  rfl


theorem certificate_fixedPointEnclosure {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).FixedPointEnclosure :=
  H.step_origin



theorem certificate_finiteCaseChecks {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).FiniteCaseChecks :=
  trivial



theorem certificate_tailBounds {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).TailBounds :=
  trivial



theorem certificate_linearizationEnclosure {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).LinearizationEnclosure :=
  (H.certificate scale M).linearizationEnclosure_of_thermal_gt_one



theorem certificate_hyperbolicSplitting {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).HyperbolicSplitting :=
  (H.certificate scale M).hyperbolicSplitting_of_thermal_gt_one



theorem certificate_orbitEntry {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).OrbitEntry :=
  trivial


theorem rgMap_iterate_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (k : ℕ) (x : State n α) :
    ((H.rgMap scale).map^[k]) x = H.iterate k x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simpa [iterate, rgMap] using congrArg H.step ih



theorem rgMap_cone_iterate
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) {η : ℝ} (hη : 0 ≤ η)
    {x : State n α} (hx : H.cone η x) (k : ℕ) :
    H.cone η (((H.rgMap scale).map^[k]) x) := by
  rw [H.rgMap_iterate_eq scale k x]
  exact H.cone_iterate hη hx k



theorem certificate_cone_iterate {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) {η : ℝ} (hη : 0 ≤ η)
    {x : (H.certificate scale M).H.carrier}
    (hx : H.cone η x) (k : ℕ) :
    H.cone η ((((H.certificate scale M).R.map)^[k]) x) := by
  simpa [certificate] using H.rgMap_cone_iterate scale hη hx k



theorem certificate_valid_of_bridge {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hbridge :
      (H.certificate scale M).RGToExponentBridge correlationLength) :
    (H.certificate scale M).Valid correlationLength where
  finiteCaseChecks := H.certificate_finiteCaseChecks scale M
  tailBounds := H.certificate_tailBounds scale M
  fixedPointEnclosure := H.certificate_fixedPointEnclosure scale M
  linearizationEnclosure := H.certificate_linearizationEnclosure scale M
  hyperbolicSplitting := H.certificate_hyperbolicSplitting scale M
  orbitEntry := H.certificate_orbitEntry scale M
  bridge := hbridge



theorem certificate_rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent) :
    (H.certificate scale M).RGToExponentBridge correlationLength := by
  simpa [RGCertificate.RGToExponentBridge] using hν



theorem certificate_valid_of_hasCriticalNu {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M correlationLength hν)


theorem certificate_hasCriticalNu_of_bridge {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hbridge :
      (H.certificate scale M).RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_bridge scale M correlationLength hbridge).hasCriticalNu




theorem certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
    {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred




theorem certificate_valid_of_bridge_congr_predictedExponent {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
      scale M hpred hbridge)



theorem certificate_hasCriticalNu_of_bridge_congr_predictedExponent
    {ι : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_bridge_congr_predictedExponent
    scale M hpred hbridge).hasCriticalNu



theorem certificate_retarget_rgToExponentBridge {ι κ : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (H.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc



theorem certificate_retarget_valid {ι κ : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hvalid : (H.certificate scale M).Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (H.certificate scale N).Valid correlationLength := by
  simpa using hvalid.retarget hβc



theorem certificate_retarget_hasCriticalNu {ι κ : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      (H.certificate scale N).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc



theorem certificate_retarget_rgToExponentBridge_iff {ι κ : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (H.certificate scale M).RGToExponentBridge correlationLength ↔
      (H.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := H.certificate scale M) (N := N) hβc)



theorem certificate_retarget_valid_iff {ι κ : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (H.certificate scale M).Valid correlationLength ↔
      (H.certificate scale N).Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := H.certificate scale M) (N := N) hβc)



theorem certificate_retarget_hasCriticalNu_iff {ι κ : Type*}
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent ↔
      HasCriticalNu N correlationLength
        (H.certificate scale N).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := H.certificate scale M) (N := N) hβc)

end FinitePlusTailHyperbolicSplitting

end Exact3D
end StatMech
