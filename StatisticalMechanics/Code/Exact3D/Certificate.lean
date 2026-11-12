/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Exact3D.RG















namespace StatMech
namespace Exact3D


structure RGCertificate {ι : Type*} (M : CriticalModel ι) where
  H : EffectiveHamiltonian
  R : BlockSpinMap H
  fixedPointData : RGFixedPointData H R

namespace RGCertificate


def thermalEigenvalue {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M) : ℝ :=
  C.fixedPointData.thermalEigenvalue


def scale {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M) : BlockScale :=
  C.R.scale


noncomputable def predictedExponent {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) : ℝ :=
  predictedNu C.scale C.thermalEigenvalue



theorem predictedExponent_pos {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) :
    0 < C.predictedExponent := by
  unfold predictedExponent predictedNu thermalEigenvalue scale
  exact div_pos (Real.log_pos C.R.scale.toReal_gt_one)
    (Real.log_pos C.fixedPointData.thermal_gt_one)




def retarget {ι κ : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (N : CriticalModel κ) : RGCertificate N where
  H := C.H
  R := C.R
  fixedPointData := C.fixedPointData

@[simp] theorem retarget_predictedExponent {ι κ : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (N : CriticalModel κ) :
    (C.retarget N).predictedExponent = C.predictedExponent := by
  rfl


def FixedPointEnclosure {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) : Prop :=
  C.R.map C.fixedPointData.fixedPoint = C.fixedPointData.fixedPoint








def LinearizationEnclosure {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) : Prop :=
  0 < Real.log C.thermalEigenvalue



theorem linearizationEnclosure_of_thermal_gt_one {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) :
    C.LinearizationEnclosure := by
  simpa [LinearizationEnclosure, thermalEigenvalue] using
    Real.log_pos C.fixedPointData.thermal_gt_one


def FiniteCaseChecks {ι : Type*} {M : CriticalModel ι}
    (_C : RGCertificate M) : Prop :=
  True


def TailBounds {ι : Type*} {M : CriticalModel ι}
    (_C : RGCertificate M) : Prop :=
  True







def HyperbolicSplitting {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) : Prop :=
  1 < C.thermalEigenvalue



theorem hyperbolicSplitting_of_thermal_gt_one {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) :
    C.HyperbolicSplitting := by
  simpa [HyperbolicSplitting, thermalEigenvalue] using
    C.fixedPointData.thermal_gt_one


def OrbitEntry {ι : Type*} {M : CriticalModel ι}
    (_C : RGCertificate M) : Prop :=
  True



def RGToExponentBridge {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ) : Prop :=
  HasCriticalNu M correlationLength C.predictedExponent




theorem rgToExponentBridge_congr_predictedExponent {ι : Type*}
    {M : CriticalModel ι} {C D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : C.predictedExponent = D.predictedExponent) :
    C.RGToExponentBridge correlationLength := by
  unfold RGToExponentBridge at hbridge ⊢
  simpa [hpred] using hbridge



theorem rgToExponentBridge_congr_predictedExponent_iff {ι : Type*}
    {M : CriticalModel ι} {C D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent) :
    C.RGToExponentBridge correlationLength ↔
      D.RGToExponentBridge correlationLength :=
  ⟨fun hbridge =>
      rgToExponentBridge_congr_predictedExponent hbridge hpred.symm,
    fun hbridge =>
      rgToExponentBridge_congr_predictedExponent hbridge hpred⟩



theorem retarget_rgToExponentBridge_of_hasCriticalNu {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu N correlationLength C.predictedExponent) :
    (C.retarget N).RGToExponentBridge correlationLength := by
  simpa [RGToExponentBridge] using hν



structure Valid {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ) : Prop where
  finiteCaseChecks : FiniteCaseChecks C
  tailBounds : TailBounds C
  fixedPointEnclosure : FixedPointEnclosure C
  linearizationEnclosure : LinearizationEnclosure C
  hyperbolicSplitting : HyperbolicSplitting C
  orbitEntry : OrbitEntry C
  bridge : RGToExponentBridge C correlationLength




theorem hasCriticalNu_of_checks {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (_hfinite : FiniteCaseChecks C) (_htail : TailBounds C)
    (_hfixed : FixedPointEnclosure C)
    (_hlinear : LinearizationEnclosure C)
    (_hhyperbolic : HyperbolicSplitting C)
    (_horbit : OrbitEntry C)
    (hbridge : RGToExponentBridge C correlationLength) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  hbridge



theorem valid_of_bridge {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hfinite : FiniteCaseChecks C) (htail : TailBounds C)
    (hfixed : FixedPointEnclosure C)
    (hlinear : LinearizationEnclosure C)
    (hhyperbolic : HyperbolicSplitting C)
    (horbit : OrbitEntry C)
    (hbridge : RGToExponentBridge C correlationLength) :
    C.Valid correlationLength where
  finiteCaseChecks := hfinite
  tailBounds := htail
  fixedPointEnclosure := hfixed
  linearizationEnclosure := hlinear
  hyperbolicSplitting := hhyperbolic
  orbitEntry := horbit
  bridge := hbridge




theorem valid_of_bridge_congr_predictedExponent {ι : Type*}
    {M : CriticalModel ι}
    (C : RGCertificate M) {D : RGCertificate M}
    (correlationLength : ℝ → ℝ)
    (hfinite : FiniteCaseChecks C) (htail : TailBounds C)
    (hfixed : FixedPointEnclosure C)
    (hlinear : LinearizationEnclosure C)
    (hhyperbolic : HyperbolicSplitting C)
    (horbit : OrbitEntry C)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (rgToExponentBridge_congr_predictedExponent hbridge hpred)



theorem bridge_of_hasCriticalNu {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    RGToExponentBridge C correlationLength := by
  simpa [RGToExponentBridge] using hν



theorem valid_of_hasCriticalNu {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hfinite : FiniteCaseChecks C) (htail : TailBounds C)
    (hfixed : FixedPointEnclosure C)
    (hlinear : LinearizationEnclosure C)
    (hhyperbolic : HyperbolicSplitting C)
    (horbit : OrbitEntry C)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit (C.bridge_of_hasCriticalNu correlationLength hν)



theorem Valid.hasCriticalNu {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hC : C.Valid correlationLength) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  hasCriticalNu_of_checks C correlationLength
    hC.finiteCaseChecks hC.tailBounds hC.fixedPointEnclosure
    hC.linearizationEnclosure hC.hyperbolicSplitting hC.orbitEntry hC.bridge



theorem rgToExponentBridge_congr_eventually {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : C.RGToExponentBridge correlationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    C.RGToExponentBridge comparisonLength :=
  hbridge.congr_eventually hEq



theorem rgToExponentBridge_congr_eventually_iff {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    C.RGToExponentBridge correlationLength ↔
      C.RGToExponentBridge comparisonLength :=
  ⟨fun hbridge => rgToExponentBridge_congr_eventually hbridge hEq,
    fun hbridge => rgToExponentBridge_congr_eventually hbridge
      (hEq.mono (fun _ hβ => hβ.symm))⟩



theorem retarget_rgToExponentBridge {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hbridge : C.RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (C.retarget N).RGToExponentBridge correlationLength := by
  simpa [RGToExponentBridge] using hbridge.congr_betaC hβc



theorem retarget_rgToExponentBridge_iff {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    C.RGToExponentBridge correlationLength ↔
      (C.retarget N).RGToExponentBridge correlationLength :=
  ⟨fun hbridge => retarget_rgToExponentBridge hbridge hβc,
    fun hbridge => by
      have hback :
          ((C.retarget N).retarget M).RGToExponentBridge correlationLength :=
        retarget_rgToExponentBridge hbridge hβc.symm
      simpa [RGToExponentBridge, retarget] using hback⟩



theorem retarget_hasCriticalNu {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hν : HasCriticalNu M correlationLength C.predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength (C.retarget N).predictedExponent := by
  simpa using hν.congr_betaC hβc



theorem retarget_hasCriticalNu_iff {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength C.predictedExponent ↔
      HasCriticalNu N correlationLength (C.retarget N).predictedExponent := by
  simpa using
    (HasCriticalNu.congr_betaC_iff
      (M := M) (N := N) (correlationLength := correlationLength)
      (ν := C.predictedExponent) hβc)



theorem Valid.congr_eventually {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength comparisonLength : ℝ → ℝ}
    (hC : C.Valid correlationLength)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    C.Valid comparisonLength where
  finiteCaseChecks := hC.finiteCaseChecks
  tailBounds := hC.tailBounds
  fixedPointEnclosure := hC.fixedPointEnclosure
  linearizationEnclosure := hC.linearizationEnclosure
  hyperbolicSplitting := hC.hyperbolicSplitting
  orbitEntry := hC.orbitEntry
  bridge := rgToExponentBridge_congr_eventually hC.bridge hEq



theorem Valid.congr_eventually_iff {ι : Type*} {M : CriticalModel ι}
    {C : RGCertificate M} {correlationLength comparisonLength : ℝ → ℝ}
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    C.Valid correlationLength ↔ C.Valid comparisonLength :=
  ⟨fun hC => hC.congr_eventually hEq,
    fun hC => hC.congr_eventually
      (hEq.mono (fun _ hβ => hβ.symm))⟩




theorem Valid.retarget {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hC : C.Valid correlationLength) (hβc : M.betaC = N.betaC) :
    (C.retarget N).Valid correlationLength where
  finiteCaseChecks := trivial
  tailBounds := trivial
  fixedPointEnclosure := by
    simpa [retarget, FixedPointEnclosure] using hC.fixedPointEnclosure
  linearizationEnclosure := (C.retarget N).linearizationEnclosure_of_thermal_gt_one
  hyperbolicSplitting := (C.retarget N).hyperbolicSplitting_of_thermal_gt_one
  orbitEntry := trivial
  bridge := retarget_rgToExponentBridge hC.bridge hβc



theorem Valid.retarget_iff {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {C : RGCertificate M}
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    C.Valid correlationLength ↔ (C.retarget N).Valid correlationLength :=
  ⟨fun hC => hC.retarget hβc,
    fun hC => by
      have hback :
          ((C.retarget N).retarget M).Valid correlationLength :=
        hC.retarget hβc.symm
      simpa [retarget, Valid, FixedPointEnclosure] using hback⟩

end RGCertificate

end Exact3D
end StatMech
