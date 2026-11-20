/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.PowerLawBridge
import Code.Exact3D.FiniteWitnessPackage
import Code.Exact3D.InfiniteTailWitnessPackage
import Code.Exact3D.InfiniteTailTableWitnessPackage
import Code.Exact3D.FinitePlusTailRG
import Code.Exact3D.FinitePlusTailBlockRG
import Code.Exact3D.FinitePlusTailClosedBallRG
import Code.Exact3D.InfiniteTailTableClosedBallRGPackage











namespace StatMech
namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}

theorem valid_mul_log_negligible_prefactor
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.Valid (fun β => A β * correlationLength β) :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_mul_log_negligible_prefactor
      hbridge hξpos hApos hlogA)

theorem hasCriticalNu_mul_log_negligible_prefactor
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      W.certificate.predictedExponent :=
  (W.valid_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA).hasCriticalNu

theorem valid_mul_log_negligible_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.Valid (fun β => A β * correlationLength β) :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
      hbridge hpred hξpos hApos hlogA)

theorem hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      W.certificate.predictedExponent :=
  (W.valid_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA).hasCriticalNu



theorem rgToExponentBridge_mul_log_negligible_prefactor
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  W.certificate.rgToExponentBridge_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA



theorem
    rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA



theorem rgToExponentBridge_of_eventually_const_mul_le_le
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare

theorem valid_of_eventually_const_mul_le_le
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_eventually_const_mul_le_le
      hbridge hpos hcLo hcHi hcompare)

theorem hasCriticalNu_of_eventually_const_mul_le_le
    (W : FiniteWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare).hasCriticalNu



theorem
    rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.RGToExponentBridge comparisonLength :=
  RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare

theorem valid_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      hbridge hpred hpos hcLo hcHi hcompare)

theorem hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare).hasCriticalNu

end FiniteWitnessPackage

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}

theorem valid_mul_log_negligible_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.Valid (fun β => A β * correlationLength β) :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_mul_log_negligible_prefactor
      hbridge hξpos hApos hlogA)

theorem hasCriticalNu_mul_log_negligible_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      W.certificate.predictedExponent :=
  (W.valid_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA).hasCriticalNu

theorem valid_mul_log_negligible_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.Valid (fun β => A β * correlationLength β) :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
      hbridge hpred hξpos hApos hlogA)

theorem hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      W.certificate.predictedExponent :=
  (W.valid_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA).hasCriticalNu



theorem rgToExponentBridge_mul_log_negligible_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  W.certificate.rgToExponentBridge_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA



theorem
    rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA



theorem rgToExponentBridge_of_eventually_const_mul_le_le
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare

theorem valid_of_eventually_const_mul_le_le
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_eventually_const_mul_le_le
      hbridge hpos hcLo hcHi hcompare)

theorem hasCriticalNu_of_eventually_const_mul_le_le
    (W : InfiniteTailWitnessPackage (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare).hasCriticalNu



theorem
    rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.RGToExponentBridge comparisonLength :=
  RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare

theorem valid_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      hbridge hpred hpos hcLo hcHi hcompare)

theorem hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare).hasCriticalNu

end InfiniteTailWitnessPackage

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]
variable {M : CriticalModel ι}

theorem valid_mul_log_negligible_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.Valid (fun β => A β * correlationLength β) :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_mul_log_negligible_prefactor
      hbridge hξpos hApos hlogA)

theorem hasCriticalNu_mul_log_negligible_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      W.certificate.predictedExponent :=
  (W.valid_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA).hasCriticalNu

theorem valid_mul_log_negligible_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.Valid (fun β => A β * correlationLength β) :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
      hbridge hpred hξpos hApos hlogA)

theorem hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      W.certificate.predictedExponent :=
  (W.valid_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA).hasCriticalNu



theorem rgToExponentBridge_mul_log_negligible_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  W.certificate.rgToExponentBridge_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA




theorem
    rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    W.certificate.RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA



theorem rgToExponentBridge_of_eventually_const_mul_le_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.RGToExponentBridge comparisonLength :=
  W.certificate.rgToExponentBridge_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare

theorem valid_of_eventually_const_mul_le_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (W.certificate.rgToExponentBridge_of_eventually_const_mul_le_le
      hbridge hpos hcLo hcHi hcompare)

theorem hasCriticalNu_of_eventually_const_mul_le_le
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : W.certificate.RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare).hasCriticalNu




theorem
    rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.RGToExponentBridge comparisonLength :=
  RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare

theorem valid_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    W.certificate.Valid comparisonLength :=
  W.valid_of_bridge
    (RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      hbridge hpred hpos hcLo hcHi hcompare)

theorem hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare).hasCriticalNu

end InfiniteTailTableWitnessPackage

namespace FinitePlusTailHyperbolicSplitting

variable {ι : Type*} {n : ℕ} {α : Type} {M : CriticalModel ι}

theorem certificate_valid_mul_log_negligible_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (H.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (H.certificate scale M).Valid (fun β => A β * correlationLength β) :=
  H.certificate_valid_of_bridge scale M
    (fun β => A β * correlationLength β)
    ((H.certificate scale M).rgToExponentBridge_mul_log_negligible_prefactor
      hbridge hξpos hApos hlogA)

theorem certificate_hasCriticalNu_mul_log_negligible_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (H.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_mul_log_negligible_prefactor
    scale M hbridge hξpos hApos hlogA).hasCriticalNu

theorem certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (H.certificate scale M).Valid (fun β => A β * correlationLength β) :=
  H.certificate_valid_of_bridge scale M
    (fun β => A β * correlationLength β)
    (RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
      hbridge hpred hξpos hApos hlogA)

theorem certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent
    scale M hbridge hpred hξpos hApos hlogA).hasCriticalNu



theorem certificate_rgToExponentBridge_mul_log_negligible_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (H.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (H.certificate scale M).RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  (H.certificate scale M).rgToExponentBridge_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA



theorem
    certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (H.certificate scale M).RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA



theorem certificate_rgToExponentBridge_of_eventually_const_mul_le_le
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (H.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (H.certificate scale M).RGToExponentBridge comparisonLength :=
  (H.certificate scale M).rgToExponentBridge_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare

theorem certificate_valid_of_eventually_const_mul_le_le
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (H.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (H.certificate scale M).Valid comparisonLength :=
  H.certificate_valid_of_bridge scale M comparisonLength
    ((H.certificate scale M).rgToExponentBridge_of_eventually_const_mul_le_le
      hbridge hpos hcLo hcHi hcompare)

theorem certificate_hasCriticalNu_of_eventually_const_mul_le_le
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (H.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_eventually_const_mul_le_le
    scale M hbridge hpos hcLo hcHi hcompare).hasCriticalNu




theorem
    certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (H.certificate scale M).RGToExponentBridge comparisonLength :=
  RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare

theorem certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (H.certificate scale M).Valid comparisonLength :=
  H.certificate_valid_of_bridge scale M comparisonLength
    (RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      hbridge hpred hpos hcLo hcHi hcompare)

theorem
    certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
    scale M hbridge hpred hpos hcLo hcHi hcompare).hasCriticalNu

end FinitePlusTailHyperbolicSplitting

namespace FinitePlusTailBlockRGPackage

variable {ι : Type*} {n : ℕ} {α : Type} {M : CriticalModel ι}

theorem certificate_valid_mul_log_negligible_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale M).Valid (fun β => A β * correlationLength β) :=
  P.certificate_valid_of_bridge scale M
    (fun β => A β * correlationLength β)
    ((P.certificate scale M).rgToExponentBridge_mul_log_negligible_prefactor
      hbridge hξpos hApos hlogA)

theorem certificate_hasCriticalNu_mul_log_negligible_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_mul_log_negligible_prefactor
    scale M hbridge hξpos hApos hlogA).hasCriticalNu

theorem certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale M).Valid (fun β => A β * correlationLength β) :=
  P.certificate_valid_of_bridge scale M
    (fun β => A β * correlationLength β)
    (RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
      hbridge hpred hξpos hApos hlogA)

theorem certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent
    scale M hbridge hpred hξpos hApos hlogA).hasCriticalNu



theorem certificate_rgToExponentBridge_mul_log_negligible_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale M).RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  (P.certificate scale M).rgToExponentBridge_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA



theorem
    certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale M).RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA



theorem certificate_rgToExponentBridge_of_eventually_const_mul_le_le
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  (P.certificate scale M).rgToExponentBridge_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare

theorem certificate_valid_of_eventually_const_mul_le_le
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    ((P.certificate scale M).rgToExponentBridge_of_eventually_const_mul_le_le
      hbridge hpos hcLo hcHi hcompare)

theorem certificate_hasCriticalNu_of_eventually_const_mul_le_le
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_const_mul_le_le
    scale M hbridge hpos hcLo hcHi hcompare).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare

theorem certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    (RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      hbridge hpred hpos hcLo hcHi hcompare)

theorem
    certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
    scale M hbridge hpred hpos hcLo hcHi hcompare).hasCriticalNu

end FinitePlusTailBlockRGPackage

namespace FinitePlusTailClosedBallRGPackage

variable {ι : Type*} {n : ℕ} {α : Type} {M : CriticalModel ι}

theorem certificate_valid_mul_log_negligible_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale M).Valid (fun β => A β * correlationLength β) :=
  P.certificate_valid_of_bridge scale M
    (fun β => A β * correlationLength β)
    ((P.certificate scale M).rgToExponentBridge_mul_log_negligible_prefactor
      hbridge hξpos hApos hlogA)

theorem certificate_hasCriticalNu_mul_log_negligible_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_mul_log_negligible_prefactor
    scale M hbridge hξpos hApos hlogA).hasCriticalNu

theorem certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale M).Valid (fun β => A β * correlationLength β) :=
  P.certificate_valid_of_bridge scale M
    (fun β => A β * correlationLength β)
    (RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
      hbridge hpred hξpos hApos hlogA)

theorem certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent
    scale M hbridge hpred hξpos hApos hlogA).hasCriticalNu



theorem certificate_rgToExponentBridge_mul_log_negligible_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength A : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale M).RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  (P.certificate scale M).rgToExponentBridge_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA



theorem
    certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale M).RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA



theorem certificate_rgToExponentBridge_of_eventually_const_mul_le_le
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  (P.certificate scale M).rgToExponentBridge_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare

theorem certificate_valid_of_eventually_const_mul_le_le
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    ((P.certificate scale M).rgToExponentBridge_of_eventually_const_mul_le_le
      hbridge hpos hcLo hcHi hcompare)

theorem certificate_hasCriticalNu_of_eventually_const_mul_le_le
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge :
      (P.certificate scale M).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_const_mul_le_le
    scale M hbridge hpos hcLo hcHi hcompare).hasCriticalNu




theorem
    certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale M).RGToExponentBridge comparisonLength :=
  RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare

theorem certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale M).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale M comparisonLength
    (RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      hbridge hpred hpos hcLo hcHi hcompare)

theorem
    certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
    scale M hbridge hpred hpos hcLo hcHi hcompare).hasCriticalNu

end FinitePlusTailClosedBallRGPackage

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}
variable [DecidableEq Case] [DecidableEq Coord]
variable {M : CriticalModel ι} {n : ℕ}

theorem certificate_valid_mul_log_negligible_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength A : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale).Valid (fun β => A β * correlationLength β) :=
  P.certificate_valid_of_bridge scale
    (fun β => A β * correlationLength β)
    ((P.certificate scale).rgToExponentBridge_mul_log_negligible_prefactor
      hbridge hξpos hApos hlogA)

theorem certificate_hasCriticalNu_mul_log_negligible_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength A : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_mul_log_negligible_prefactor
    scale hbridge hξpos hApos hlogA).hasCriticalNu

theorem certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale).Valid (fun β => A β * correlationLength β) :=
  P.certificate_valid_of_bridge scale
    (fun β => A β * correlationLength β)
    (RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
      hbridge hpred hξpos hApos hlogA)

theorem certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β)
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent
    scale hbridge hpred hξpos hApos hlogA).hasCriticalNu



theorem certificate_rgToExponentBridge_mul_log_negligible_prefactor
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength A : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale).RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  (P.certificate scale).rgToExponentBridge_mul_log_negligible_prefactor
    hbridge hξpos hApos hlogA




theorem
    certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M} {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    (P.certificate scale).RGToExponentBridge
      (fun β => A β * correlationLength β) :=
  RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    hbridge hpred hξpos hApos hlogA



theorem certificate_rgToExponentBridge_of_eventually_const_mul_le_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale).RGToExponentBridge comparisonLength :=
  (P.certificate scale).rgToExponentBridge_of_eventually_const_mul_le_le
    hbridge hpos hcLo hcHi hcompare

theorem certificate_valid_of_eventually_const_mul_le_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale comparisonLength
    ((P.certificate scale).rgToExponentBridge_of_eventually_const_mul_le_le
      hbridge hpos hcLo hcHi hcompare)

theorem certificate_hasCriticalNu_of_eventually_const_mul_le_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {correlationLength comparisonLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    {cLo cHi : ℝ} (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_eventually_const_mul_le_le
    scale hbridge hpos hcLo hcHi hcompare).hasCriticalNu



theorem
    certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale).RGToExponentBridge comparisonLength :=
  RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    hbridge hpred hpos hcLo hcHi hcompare

theorem certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    (P.certificate scale).Valid comparisonLength :=
  P.certificate_valid_of_bridge scale comparisonLength
    (RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      hbridge hpred hpos hcLo hcHi hcompare)

theorem
    certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength
      (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
    scale hbridge hpred hpos hcLo hcHi hcompare).hasCriticalNu

end InfiniteTailTableClosedBallRGPackage

end Exact3D
end StatMech
