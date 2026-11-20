/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Reparameterization
import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.InfiniteTailWitnessPackage
import Code.Exact3D.InfiniteTailTableWitnessPackage










namespace StatMech
namespace Exact3D

namespace FiniteWitnessPackage

variable {ι κ α : Type*} [DecidableEq α]
variable {M : CriticalModel ι} {N : CriticalModel κ}



theorem rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    hν hφ hEq



theorem
    rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (by simpa [hpred] using hν) hφ hEq



theorem rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq



theorem rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq



theorem valid_of_reparameterized_hasCriticalNu_eventually_eq
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hν hφ hEq)



theorem hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_hasCriticalNu_eventually_eq hν hφ hEq).hasCriticalNu



theorem valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_reparameterized_hasCriticalNu_eventually_eq
    (by simpa [hpred] using hν) hφ hEq



theorem
    hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    hpred hν hφ hEq).hasCriticalNu



theorem valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      D hpred hbridge hφ hEq)



theorem hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq).hasCriticalNu



theorem valid_of_reparameterized_retargetBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hbridge hφ hEq)



theorem hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq).hasCriticalNu

end FiniteWitnessPackage

namespace InfiniteTailWitnessPackage

variable {ι κ α : Type*} [DecidableEq α]
variable {M : CriticalModel ι} {N : CriticalModel κ}



theorem rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    hν hφ hEq



theorem
    rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (by simpa [hpred] using hν) hφ hEq



theorem rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq



theorem rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq



theorem valid_of_reparameterized_hasCriticalNu_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hν hφ hEq)



theorem hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_hasCriticalNu_eventually_eq hν hφ hEq).hasCriticalNu




theorem valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_reparameterized_hasCriticalNu_eventually_eq
    (by simpa [hpred] using hν) hφ hEq




theorem
    hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    hpred hν hφ hEq).hasCriticalNu



theorem valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      D hpred hbridge hφ hEq)



theorem hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq).hasCriticalNu



theorem valid_of_reparameterized_retargetBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hbridge hφ hEq)



theorem hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq).hasCriticalNu

end InfiniteTailWitnessPackage

namespace InfiniteTailTableWitnessPackage

variable {ι κ Case α : Type*} [DecidableEq Case] [DecidableEq α]
variable {M : CriticalModel ι} {N : CriticalModel κ}



theorem rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    hν hφ hEq




theorem
    rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (by simpa [hpred] using hν) hφ hEq



theorem rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq



theorem rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq



theorem valid_of_reparameterized_hasCriticalNu_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hν hφ hEq)



theorem hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν :
      HasCriticalNu N correlationLength W.certificate.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_hasCriticalNu_eventually_eq hν hφ hEq).hasCriticalNu




theorem valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_reparameterized_hasCriticalNu_eventually_eq
    (by simpa [hpred] using hν) hφ hEq




theorem
    hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : W.certificate.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    hpred hν hφ hEq).hasCriticalNu



theorem valid_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      D hpred hbridge hφ hEq)



theorem hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = W.certificate.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq).hasCriticalNu



theorem valid_of_reparameterized_retargetBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hbridge hφ hEq)



theorem hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge :
      (W.certificate.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq).hasCriticalNu

end InfiniteTailTableWitnessPackage

end Exact3D
end StatMech
