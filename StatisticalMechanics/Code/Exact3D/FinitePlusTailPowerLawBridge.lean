/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.PowerLawBridge
import Code.Exact3D.FinitePlusTailRG
import Code.Exact3D.FinitePlusTailBlockRG
import Code.Exact3D.FinitePlusTailClosedBallRG










namespace StatMech
namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {ι : Type*} {n : ℕ} {α : Type} {M : CriticalModel ι}



theorem certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M).rgToExponentBridge_of_eventually_exact_power_prefactor
    correlationLength hA hξ



theorem certificate_valid_of_eventually_exact_power_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
      scale M correlationLength hA hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_eventually_exact_power_prefactor
    scale M correlationLength hA hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M).rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    correlationLength δ hA hδ hξ



theorem certificate_valid_of_exact_power_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      scale M correlationLength δ hA hδ hξ)



theorem certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_exact_power_prefactor_on_Ioo
    scale M correlationLength δ hA hδ hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M)
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ



theorem certificate_valid_of_eventually_exact_power_variable_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      scale M correlationLength A hA hlogA hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_eventually_exact_power_variable_prefactor
    scale M correlationLength A hA hlogA hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ



theorem certificate_valid_of_exact_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      scale M correlationLength A δ hδ hA hlogA hξ)



theorem certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(H.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_exact_power_variable_prefactor_on_Ioo
    scale M correlationLength A δ hδ hA hlogA hξ).hasCriticalNu


theorem certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M)
    |>.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ



theorem certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      scale M correlationLength mass B hB hlogB hmass hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    scale M correlationLength mass B hB hlogB hmass hξ).hasCriticalNu


theorem certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M)
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ


theorem certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      scale M correlationLength mass B δ hδ hB hlogB hmass hξ)



theorem certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo
    scale M correlationLength mass B δ hδ hB hlogB hmass hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ

theorem certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H
      |>.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
        scale M correlationLength δ hpred hA hδ hξ)

theorem certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    scale M correlationLength δ hpred hA hδ hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ

theorem
    certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  H.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength A δ hpred hδ hA hlogA hξ

theorem
    certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H
      |>.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
        scale M correlationLength A δ hpred hδ hA hlogA hξ)

theorem
    certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength A δ hpred hδ hA hlogA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M)
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  H.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H
      |>.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
        scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ)

theorem
    certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ).hasCriticalNu

set_option linter.style.longLine false in
theorem
    certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
      (H.certificate scale M).predictedExponent :=
  H.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)
    hpred

theorem
    certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H
      |>.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
        scale M correlationLength hpred hA hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    scale M correlationLength hpred hA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)
    hpred

theorem
certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  H.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    scale M correlationLength A hpred hA hlogA hξ

theorem
    certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H
      |>.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
        scale M correlationLength A hpred hA hlogA hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
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
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    scale M correlationLength A hpred hA hlogA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)
    hpred

set_option linter.style.longLine false in
theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  H.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

theorem
    certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H
      |>.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
        scale M correlationLength mass B hpred hB hlogB hmass hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ).hasCriticalNu

set_option linter.style.longLine false in
theorem
    certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (H : FinitePlusTailHyperbolicSplitting n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  H.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

end FinitePlusTailHyperbolicSplitting

namespace FinitePlusTailBlockRGPackage

variable {ι : Type*} {n : ℕ} {α : Type} {M : CriticalModel ι}



theorem certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M).rgToExponentBridge_of_eventually_exact_power_prefactor
    correlationLength hA hξ



theorem certificate_valid_of_eventually_exact_power_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
      scale M correlationLength hA hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_prefactor
    scale M correlationLength hA hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M).rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    correlationLength δ hA hδ hξ



theorem certificate_valid_of_exact_power_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      scale M correlationLength δ hA hδ hξ)



theorem certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_power_prefactor_on_Ioo
    scale M correlationLength δ hA hδ hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ



theorem certificate_valid_of_eventually_exact_power_variable_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      scale M correlationLength A hA hlogA hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_variable_prefactor
    scale M correlationLength A hA hlogA hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ



theorem certificate_valid_of_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      scale M correlationLength A δ hδ hA hlogA hξ)



theorem certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_power_variable_prefactor_on_Ioo
    scale M correlationLength A δ hδ hA hlogA hξ).hasCriticalNu


theorem certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ



theorem certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      scale M correlationLength mass B hB hlogB hmass hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    scale M correlationLength mass B hB hlogB hmass hξ).hasCriticalNu


theorem certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ


theorem certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      scale M correlationLength mass B δ hδ hB hlogB hmass hξ)



theorem certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo
    scale M correlationLength mass B δ hδ hB hlogB hmass hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ

theorem certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
        scale M correlationLength δ hpred hA hδ hξ)

theorem certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    scale M correlationLength δ hpred hA hδ hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ

theorem
    certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength A δ hpred hδ hA hlogA hξ

theorem
    certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
        scale M correlationLength A δ hpred hδ hA hlogA hξ)

theorem
    certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength A δ hpred hδ hA hlogA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
        scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ)

theorem
    certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ).hasCriticalNu

set_option linter.style.longLine false in
theorem
    certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
      (P.certificate scale M).predictedExponent :=
  P.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)
    hpred

theorem
    certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
        scale M correlationLength hpred hA hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    scale M correlationLength hpred hA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)
    hpred

theorem
certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    scale M correlationLength A hpred hA hlogA hξ

theorem
    certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
        scale M correlationLength A hpred hA hlogA hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    scale M correlationLength A hpred hA hlogA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)
    hpred

set_option linter.style.longLine false in
theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

theorem
    certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
        scale M correlationLength mass B hpred hB hlogB hmass hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ).hasCriticalNu

set_option linter.style.longLine false in
theorem
    certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailBlockRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  P.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

end FinitePlusTailBlockRGPackage

namespace FinitePlusTailClosedBallRGPackage

variable {ι : Type*} {n : ℕ} {α : Type} {M : CriticalModel ι}



theorem certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M).rgToExponentBridge_of_eventually_exact_power_prefactor
    correlationLength hA hξ



theorem certificate_valid_of_eventually_exact_power_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
      scale M correlationLength hA hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_prefactor
    scale M correlationLength hA hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M).rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    correlationLength δ hA hδ hξ



theorem certificate_valid_of_exact_power_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      scale M correlationLength δ hA hδ hξ)



theorem certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_power_prefactor_on_Ioo
    scale M correlationLength δ hA hδ hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ



theorem certificate_valid_of_eventually_exact_power_variable_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      scale M correlationLength A hA hlogA hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_variable_prefactor
    scale M correlationLength A hA hlogA hξ).hasCriticalNu



theorem certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ



theorem certificate_valid_of_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      scale M correlationLength A δ hδ hA hlogA hξ)



theorem certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-(P.certificate scale M).predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_power_variable_prefactor_on_Ioo
    scale M correlationLength A δ hδ hA hlogA hξ).hasCriticalNu


theorem certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ



theorem certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      scale M correlationLength mass B hB hlogB hmass hξ)



theorem certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    scale M correlationLength mass B hB hlogB hmass hξ).hasCriticalNu


theorem certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ


theorem certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      scale M correlationLength mass B δ hδ hB hlogB hmass hξ)



theorem certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    (correlationLength mass B : ℝ → ℝ)
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
            ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo
    scale M correlationLength mass B δ hδ hB hlogB hmass hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ

theorem certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
        scale M correlationLength δ hpred hA hδ hξ)

theorem certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    scale M correlationLength δ hpred hA hδ hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ

theorem
    certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength A δ hpred hδ hA hlogA hξ

theorem
    certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
        scale M correlationLength A δ hpred hδ hA hlogA hξ)

theorem
    certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength A δ hpred hδ hA hlogA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  (P.certificate scale M)
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
        scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ)

theorem
    certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ).hasCriticalNu

set_option linter.style.longLine false in
theorem
    certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
      (P.certificate scale M).predictedExponent :=
  P.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)
    hpred

theorem
    certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
        scale M correlationLength hpred hA hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ}
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    scale M correlationLength hpred hA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)
    hpred

theorem
certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    scale M correlationLength A hpred hA hlogA hξ

theorem
    certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
        scale M correlationLength A hpred hA hlogA hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
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
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    scale M correlationLength A hpred hA hlogA hξ).hasCriticalNu

theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)
    hpred

set_option linter.style.longLine false in
theorem
    certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).RGToExponentBridge correlationLength :=
  P.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

theorem
    certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_bridge scale M correlationLength
    (P
      |>.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
        scale M correlationLength mass B hpred hB hlogB hmass hξ)

theorem
    certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  (P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ).hasCriticalNu

set_option linter.style.longLine false in
theorem
    certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    (P.certificate scale M).Valid correlationLength :=
  P.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

set_option linter.style.longLine false in
theorem
    certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (P : FinitePlusTailClosedBallRGPackage n α)
    (scale : BlockScale) (M : CriticalModel ι)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength
      (P.certificate scale M).predictedExponent :=
  P.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    scale M correlationLength mass B hpred hB hlogB hmass hξ

end FinitePlusTailClosedBallRGPackage

end Exact3D
end StatMech
