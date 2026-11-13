/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Reparameterization
import Code.Exact3D.FinitePlusTailRG
import Code.Exact3D.FinitePlusTailBlockRG
import Code.Exact3D.FinitePlusTailClosedBallRG










namespace StatMech
namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type} {ι κ : Type*}
variable {M : CriticalModel ι} {N : CriticalModel κ}

theorem certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (H.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).RGToExponentBridge comparisonLength :=
  (H.certificate scale M).rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    hν hφ hEq

theorem
    certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (H.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).RGToExponentBridge comparisonLength :=
  H.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale (by simpa [hpred] using hν) hφ hEq



theorem
    certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (H.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).RGToExponentBridge comparisonLength :=
  H.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    (M := M) scale hpred hν hφ hEq

theorem certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (H.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).RGToExponentBridge comparisonLength :=
  (H.certificate scale M).rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq



theorem
    certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).RGToExponentBridge comparisonLength :=
  H.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (M := M) scale D hpred.symm hbridge hφ hEq

theorem certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((H.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).RGToExponentBridge comparisonLength :=
  (H.certificate scale M).rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq

theorem certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (H.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).Valid comparisonLength :=
  H.certificate_valid_of_bridge scale M comparisonLength
    ((H.certificate scale M).rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hν hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (H.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale hν hφ hEq).hasCriticalNu

theorem
    certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (H.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).Valid comparisonLength :=
  H.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale (by simpa [hpred] using hν) hφ hEq

theorem
    certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (H.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (M := M) scale hpred hν hφ hEq).hasCriticalNu

theorem certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (H.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).Valid comparisonLength :=
  H.certificate_valid_of_bridge scale M comparisonLength
    ((H.certificate scale M).rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      D hpred hbridge hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (H.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (M := M) scale D hpred hbridge hφ hEq).hasCriticalNu

theorem certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((H.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (H.certificate scale M).Valid comparisonLength :=
  H.certificate_valid_of_bridge scale M comparisonLength
    ((H.certificate scale M).rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hbridge hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((H.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    (M := M) scale hbridge hφ hEq).hasCriticalNu

end FinitePlusTailHyperbolicSplitting

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type} {ι κ : Type*}
variable {M : CriticalModel ι} {N : CriticalModel κ}

theorem certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  (P.certificate scale M).rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    hν hφ hEq

theorem
    certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale (by simpa [hpred] using hν) hφ hEq



theorem
    certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    (M := M) scale hpred hν hφ hEq

theorem certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  (P.certificate scale M).rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq



theorem
    certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (M := M) scale D hpred.symm hbridge hφ hEq

theorem certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  (P.certificate scale M).rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq

theorem certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    ((P.certificate scale M).rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hν hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale hν hφ hEq).hasCriticalNu

theorem
    certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale (by simpa [hpred] using hν) hφ hEq

theorem
    certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (M := M) scale hpred hν hφ hEq).hasCriticalNu

theorem certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    ((P.certificate scale M).rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      D hpred hbridge hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (M := M) scale D hpred hbridge hφ hEq).hasCriticalNu

theorem certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    ((P.certificate scale M).rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hbridge hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    (M := M) scale hbridge hφ hEq).hasCriticalNu

end FinitePlusTailBlockRGPackage

namespace FinitePlusTailClosedBallRGPackage

variable {n : ℕ} {α : Type} {ι κ : Type*}
variable {M : CriticalModel ι} {N : CriticalModel κ}

theorem certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  (P.certificate scale M).rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    hν hφ hEq

theorem
    certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale (by simpa [hpred] using hν) hφ hEq



theorem
    certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    (M := M) scale hpred hν hφ hEq

theorem certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  (P.certificate scale M).rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq



theorem
    certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (M := M) scale D hpred.symm hbridge hφ hEq

theorem certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  (P.certificate scale M).rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq

theorem certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    ((P.certificate scale M).rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hν hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength
        (P.certificate scale M).predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale hν hφ hEq).hasCriticalNu

theorem
    certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    (M := M) scale (by simpa [hpred] using hν) hφ hEq

theorem
    certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (M := M) scale hpred hν hφ hEq).hasCriticalNu

theorem certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    ((P.certificate scale M).rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      D hpred hbridge hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (M := M) scale D hpred hbridge hφ hEq).hasCriticalNu

theorem certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    ((P.certificate scale M).rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hbridge hφ hEq)

theorem certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge
      correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    (M := M) scale hbridge hφ hEq).hasCriticalNu

end FinitePlusTailClosedBallRGPackage

end Exact3D
end StatMech
