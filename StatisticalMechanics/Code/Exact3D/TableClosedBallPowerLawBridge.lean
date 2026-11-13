/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.PowerLawBridge
import Code.Exact3D.InfiniteTailTableClosedBallRGPackage











namespace StatMech
namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}
variable [DecidableEq Case] [DecidableEq Coord]
variable {M : CriticalModel ι} {n : ℕ}



theorem certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale).rgToExponentBridge_of_eventually_exact_power_prefactor
    correlationLength hA hξ



theorem certificate_valid_of_eventually_exact_power_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
      scale correlationLength hA hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_prefactor
    scale correlationLength hA hξ).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)
    hpred


theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred
    scale D correlationLength hpred hA hξ



theorem
    certificate_valid_of_eventually_exact_power_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred
      scale D correlationLength hpred hA hξ)



theorem
    certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_prefactor_congr_pred
    scale D correlationLength hpred hA hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale).rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    correlationLength δ hA hδ hξ



theorem certificate_valid_of_exact_power_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      scale correlationLength δ hA hδ hξ)



theorem certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_exact_power_prefactor_on_Ioo
    scale correlationLength δ hA hδ hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale)
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ


theorem
    certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_pred
    scale D correlationLength δ hpred hA hδ hξ



theorem certificate_valid_of_exact_power_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_pred
      scale D correlationLength δ hpred hA hδ hξ)



theorem certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_exact_power_prefactor_on_Ioo_congr_pred
    scale D correlationLength δ hpred hA hδ hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale).rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    correlationLength A hA hlogA hξ



theorem certificate_valid_of_eventually_exact_power_variable_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      scale correlationLength A hA hlogA hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_variable_prefactor
    scale correlationLength A hA hlogA hξ).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)
    hpred

theorem
certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    scale D correlationLength A hpred hA hlogA hξ



theorem
    certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
      scale D correlationLength A hpred hA hlogA hξ)



theorem
    certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred
    scale D correlationLength A hpred hA hlogA hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale).rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    correlationLength A δ hδ hA hlogA hξ



theorem certificate_valid_of_exact_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      scale correlationLength A δ hδ hA hlogA hξ)



theorem certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_exact_power_variable_prefactor_on_Ioo
    scale correlationLength A δ hδ hA hlogA hξ).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength A : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale)
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ


theorem
    certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength A : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    scale D correlationLength A δ hpred hδ hA hlogA hξ



theorem
    certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength A : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
        scale D correlationLength A δ hpred hδ hA hlogA hξ)



theorem
    certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength A : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    scale D correlationLength A δ hpred hδ hA hlogA hξ).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength mass B : ℝ → ℝ)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale).rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    correlationLength mass B hB hlogB hmass hξ



theorem certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength mass B : ℝ → ℝ)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      scale correlationLength mass B hB hlogB hmass hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength mass B : ℝ → ℝ)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    scale correlationLength mass B hB hlogB hmass hξ).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)
    hpred

set_option linter.style.longLine false in


theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale D correlationLength mass B hpred hB hlogB hmass hξ



theorem
    certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
      scale D correlationLength mass B hpred hB hlogB hmass hξ)



theorem
    certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale D correlationLength mass B hpred hB hlogB hmass hξ).hasCriticalNu

set_option linter.style.longLine false in


theorem
    certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale D correlationLength mass B hpred hB hlogB hmass hξ

set_option linter.style.longLine false in


theorem
    certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp
            (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  P.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale D correlationLength mass B hpred hB hlogB hmass hξ


theorem certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp
            ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale).rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    correlationLength mass B δ hδ hB hlogB hmass hξ


theorem certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp
            ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      scale correlationLength mass B δ hδ hB hlogB hmass hξ)



theorem certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp
            ((P.certificate scale).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo
    scale correlationLength mass B δ hδ hB hlogB hmass hξ).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  (P.certificate scale)
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

set_option linter.style.longLine false in


theorem
    certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ



theorem
    certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
        scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ)



theorem
    certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ).hasCriticalNu

set_option linter.style.longLine false in


theorem
    certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

set_option linter.style.longLine false in


theorem
    certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent :=
  P.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

end InfiniteTailTableClosedBallRGPackage

end Exact3D
end StatMech
