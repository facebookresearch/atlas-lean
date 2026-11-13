/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Reparameterization
import Code.Exact3D.InfiniteTailTableClosedBallRGPackage










namespace StatMech
namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι κ Case Coord : Type*} {TailIndex : Type}
variable [DecidableEq Case] [DecidableEq Coord]
variable {M : CriticalModel ι} {N : CriticalModel κ} {n : ℕ}



theorem certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).RGToExponentBridge comparisonLength :=
  (P.certificate scale).rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    hν hφ hEq

theorem certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    scale
    (by
      have hpred' :
          (P.closedBallRG.certificate scale M).predictedExponent = ν := by
        simpa [InfiniteTailTableClosedBallRGPackage.certificate] using hpred
      simpa [hpred'] using hν)
    hφ hEq



theorem
    certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    scale hpred hν hφ hEq



theorem certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).RGToExponentBridge comparisonLength :=
  (P.certificate scale).rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq



theorem
    certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    scale D hpred.symm hbridge hφ hEq



theorem certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).RGToExponentBridge comparisonLength :=
  (P.certificate scale).rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq



theorem certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale comparisonLength
    ((P.certificate scale).rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hν hφ hEq)



theorem certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    scale hν hφ hEq).hasCriticalNu

theorem
    certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).Valid comparisonLength :=
  P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    scale
    (by
      have hpred' :
          (P.closedBallRG.certificate scale M).predictedExponent = ν := by
        simpa [InfiniteTailTableClosedBallRGPackage.certificate] using hpred
      simpa [hpred'] using hν)
    hφ hEq

theorem
    certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    scale hpred hν hφ hEq).hasCriticalNu



theorem certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale comparisonLength
    ((P.certificate scale).rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      D hpred hbridge hφ hEq)



theorem certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    scale D hpred hbridge hφ hEq).hasCriticalNu



theorem certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale comparisonLength
    ((P.certificate scale).rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hbridge hφ hEq)



theorem certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    scale hbridge hφ hEq).hasCriticalNu

end InfiniteTailTableClosedBallRGPackage

end Exact3D
end StatMech
