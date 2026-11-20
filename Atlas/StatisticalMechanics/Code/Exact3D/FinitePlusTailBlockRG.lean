/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FinitePlusTailBlockBounds
import Code.Exact3D.FinitePlusTailRG










namespace StatMech
namespace Exact3D



structure FinitePlusTailBlockRGPackage (n : ℕ) (α : Type) where
  blockBounds : FinitePlusTailBlockBounds n α
  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  finite_column_sum_le : blockBounds.finiteToFinite + blockBounds.finiteToTail ≤ c
  tail_column_sum_le : blockBounds.tailToFinite + blockBounds.tailToTail ≤ c
  origin_fixed :
    blockBounds.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
      FinitePlusTailState.origin
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable_dominated : c ≤ |thermal|

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}



noncomputable def stableCertificate
    (P : FinitePlusTailBlockRGPackage n α) :
    FinitePlusTailLipschitzCertificate n α :=
  P.blockBounds.toLipschitzCertificate
    P.c_nonneg P.c_lt_one
    P.finite_column_sum_le P.tail_column_sum_le

@[simp] theorem stableCertificate_map
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.map = P.blockBounds.map :=
  rfl

@[simp] theorem stableCertificate_c
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.c = P.c :=
  rfl

@[simp] theorem stableCertificate_finiteToFinite
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.finiteToFinite = P.blockBounds.finiteToFinite :=
  rfl

@[simp] theorem stableCertificate_tailToFinite
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.tailToFinite = P.blockBounds.tailToFinite :=
  rfl

@[simp] theorem stableCertificate_finiteToTail
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.finiteToTail = P.blockBounds.finiteToTail :=
  rfl

@[simp] theorem stableCertificate_tailToTail
    (P : FinitePlusTailBlockRGPackage n α) :
    P.stableCertificate.tailToTail = P.blockBounds.tailToTail :=
  rfl




noncomputable def with_larger_c
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    FinitePlusTailBlockRGPackage n α where
  blockBounds := P.blockBounds
  c := c'
  c_nonneg := le_trans P.c_nonneg hc
  c_lt_one := hc_lt_one
  finite_column_sum_le := le_trans P.finite_column_sum_le hc
  tail_column_sum_le := le_trans P.tail_column_sum_le hc
  origin_fixed := P.origin_fixed
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one
  stable_dominated := hdominated

@[simp] theorem with_larger_c_blockBounds
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_c hc hc_lt_one hdominated).blockBounds =
      P.blockBounds :=
  rfl

@[simp] theorem with_larger_c_c
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_c hc hc_lt_one hdominated).c = c' :=
  rfl

@[simp] theorem with_larger_c_thermal
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_c hc hc_lt_one hdominated).thermal = P.thermal :=
  rfl




noncomputable def with_larger_constants
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|) :
    FinitePlusTailBlockRGPackage n α where
  blockBounds :=
    P.blockBounds.with_larger_constants hff htf hft htt
  c := c'
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_column_sum_le := hfinite_column_sum_le
  tail_column_sum_le := htail_column_sum_le
  origin_fixed := by
    simpa [FinitePlusTailBlockBounds.with_larger_constants,
      FinitePlusTailBlockBounds.map] using P.origin_fixed
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one
  stable_dominated := hdominated

@[simp] theorem with_larger_constants_c
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).c = c' :=
  rfl

@[simp] theorem with_larger_constants_blockBounds
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).blockBounds =
        P.blockBounds.with_larger_constants hff htf hft htt :=
  rfl

@[simp] theorem with_larger_constants_thermal
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).thermal =
        P.thermal :=
  rfl

@[simp] theorem with_larger_constants_stableCertificate_map
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|) :
    ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).stableCertificate).map =
      P.stableCertificate.map := by
  simp [stableCertificate]


noncomputable def hyperbolicSplitting
    (P : FinitePlusTailBlockRGPackage n α) :
    FinitePlusTailHyperbolicSplitting n α where
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one
  stable := P.stableCertificate
  stable_origin := by
    simpa [stableCertificate] using P.origin_fixed
  stable_dominated := by
    simpa [stableCertificate] using P.stable_dominated


@[simp] theorem hyperbolicSplitting_thermal
    (P : FinitePlusTailBlockRGPackage n α) :
    P.hyperbolicSplitting.thermal = P.thermal :=
  rfl



@[simp] theorem hyperbolicSplitting_stable
    (P : FinitePlusTailBlockRGPackage n α) :
    P.hyperbolicSplitting.stable = P.stableCertificate :=
  rfl



@[simp] theorem with_larger_c_hyperbolicSplitting_stable_map
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    (P.with_larger_c hc hc_lt_one hdominated).hyperbolicSplitting.stable.map =
      P.hyperbolicSplitting.stable.map :=
  rfl



@[simp] theorem with_larger_constants_hyperbolicSplitting_stable_map
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|) :
    (let Q :=
      P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le hdominated;
      Q.hyperbolicSplitting.stable.map = P.hyperbolicSplitting.stable.map) := by
  dsimp



theorem cone_iterate
    (P : FinitePlusTailBlockRGPackage n α)
    {η : ℝ} (hη : 0 ≤ η)
    {x : FinitePlusTailHyperbolicSplitting.State n α}
    (hx : P.hyperbolicSplitting.cone η x) (k : ℕ) :
    P.hyperbolicSplitting.cone η
      (P.hyperbolicSplitting.iterate k x) :=
  P.hyperbolicSplitting.cone_iterate hη hx k


noncomputable def certificate {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) : RGCertificate M :=
  P.hyperbolicSplitting.certificate scale M

@[simp] theorem certificate_retarget {ι κ : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ) :
    P.certificate scale N = (P.certificate scale M).retarget N :=
  rfl


@[simp] theorem certificate_thermalEigenvalue_eq {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).thermalEigenvalue = P.thermal :=
  rfl


@[simp] theorem certificate_scale_eq {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).scale = scale :=
  rfl



theorem certificate_predictedExponent_eq {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).predictedExponent =
      predictedNu scale P.thermal :=
  rfl

@[simp] theorem with_larger_c_certificate_eq {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.with_larger_c hc hc_lt_one hdominated).certificate scale M =
      P.certificate scale M :=
  rfl



theorem with_larger_c_certificate_predictedExponent_eq {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_c hc hc_lt_one hdominated).certificate
      scale M).predictedExponent =
      (P.certificate scale M).predictedExponent :=
  rfl



theorem with_larger_c_rgToExponentBridge {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    ((P.with_larger_c hc hc_lt_one hdominated).certificate scale M).RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_c_valid {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale M).Valid correlationLength) :
    ((P.with_larger_c hc hc_lt_one hdominated).certificate scale M).Valid
      correlationLength := by
  simpa using hvalid



theorem with_larger_c_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_c hc hc_lt_one hdominated).certificate
        scale M).predictedExponent := by
  simpa using hν

@[simp] theorem with_larger_constants_certificate_eq {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).certificate
        scale M =
      P.certificate scale M :=
  rfl



theorem with_larger_constants_certificate_predictedExponent_eq {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι) :
    ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).certificate
        scale M).predictedExponent =
      (P.certificate scale M).predictedExponent :=
  rfl



theorem with_larger_constants_rgToExponentBridge {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).certificate
        scale M).RGToExponentBridge correlationLength := by
  simpa using hbridge



theorem with_larger_constants_valid {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale M).Valid correlationLength) :
    ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).certificate
        scale M).Valid correlationLength := by
  simpa using hvalid



theorem with_larger_constants_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|)
    (scale : BlockScale) (M : CriticalModel ι)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le hdominated).certificate
          scale M).predictedExponent := by
  simpa using hν


theorem certificate_fixedPointEnclosure {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).FixedPointEnclosure :=
  P.hyperbolicSplitting.certificate_fixedPointEnclosure scale M


theorem certificate_finiteCaseChecks {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).FiniteCaseChecks := by
  simpa [certificate] using
    P.hyperbolicSplitting.certificate_finiteCaseChecks scale M


theorem certificate_tailBounds {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).TailBounds := by
  simpa [certificate] using
    P.hyperbolicSplitting.certificate_tailBounds scale M



theorem certificate_linearizationEnclosure {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).LinearizationEnclosure := by
  simpa [certificate] using
    P.hyperbolicSplitting.certificate_linearizationEnclosure scale M



theorem certificate_hyperbolicSplitting {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).HyperbolicSplitting := by
  simpa [certificate] using
    P.hyperbolicSplitting.certificate_hyperbolicSplitting scale M


theorem certificate_orbitEntry {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) :
    (P.certificate scale M).OrbitEntry := by
  simpa [certificate] using
    P.hyperbolicSplitting.certificate_orbitEntry scale M


theorem certificate_cone_iterate {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {η : ℝ} (hη : 0 ≤ η)
    {x : (P.certificate scale M).H.carrier}
    (hx : P.hyperbolicSplitting.cone η x) (k : ℕ) :
    P.hyperbolicSplitting.cone η
      ((((P.certificate scale M).R.map)^[k]) x) := by
  simpa [certificate] using
    P.hyperbolicSplitting.certificate_cone_iterate scale M hη hx k



theorem certificate_valid_of_bridge {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    (P.certificate scale M).Valid correlationLength := by
  simpa [certificate] using
    P.hyperbolicSplitting.certificate_valid_of_bridge
      scale M correlationLength hbridge



theorem certificate_rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale M).predictedExponent) :
    (P.certificate scale M).RGToExponentBridge correlationLength := by
  simpa [certificate] using
    P.hyperbolicSplitting.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M correlationLength hν



theorem certificate_valid_of_hasCriticalNu {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
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
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_bridge scale M correlationLength hbridge).hasCriticalNu



theorem certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
    {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred



theorem certificate_valid_of_bridge_congr_predictedExponent {ι : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
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
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_bridge_congr_predictedExponent
    scale M hpred hbridge).hasCriticalNu



theorem certificate_retarget_rgToExponentBridge {ι κ : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc



theorem certificate_retarget_valid {ι κ : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale M).Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale N).Valid correlationLength := by
  simpa using hvalid.retarget hβc



theorem certificate_retarget_hasCriticalNu {ι κ : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
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
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale M).RGToExponentBridge correlationLength ↔
      (P.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := P.certificate scale M) (N := N) hβc)



theorem certificate_retarget_valid_iff {ι κ : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale M).Valid correlationLength ↔
      (P.certificate scale N).Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := P.certificate scale M) (N := N) hβc)



theorem certificate_retarget_hasCriticalNu_iff {ι κ : Type*}
    (P : FinitePlusTailBlockRGPackage n α)
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

end FinitePlusTailBlockRGPackage

end Exact3D
end StatMech
