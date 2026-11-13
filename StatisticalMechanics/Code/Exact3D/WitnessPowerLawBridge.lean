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










namespace StatMech
namespace Exact3D

namespace FiniteWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}



theorem rgToExponentBridge_of_eventually_exact_power_prefactor
    (W : FiniteWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_power_prefactor
    correlationLength hA hξ



theorem valid_of_eventually_exact_power_prefactor
    (W : FiniteWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)



theorem hasCriticalNu_of_eventually_exact_power_prefactor
    (W : FiniteWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)



theorem rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    correlationLength δ hA hδ hξ



theorem valid_of_exact_power_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)



theorem hasCriticalNu_of_exact_power_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)



theorem rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    (W : FiniteWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    correlationLength A hA hlogA hξ



theorem valid_of_eventually_exact_power_variable_prefactor
    (W : FiniteWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)



theorem hasCriticalNu_of_eventually_exact_power_variable_prefactor
    (W : FiniteWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)



theorem rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    correlationLength A δ hδ hA hlogA hξ



theorem valid_of_exact_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)



theorem hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)



theorem rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    (W : FiniteWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    correlationLength mass B hB hlogB hmass hξ



theorem valid_of_eventually_exact_mass_power_variable_prefactor
    (W : FiniteWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)



theorem hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    (W : FiniteWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)


theorem rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    correlationLength mass B δ hδ hB hlogB hmass hξ


theorem valid_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)



theorem hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : FiniteWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)

theorem
    rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ

theorem valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      correlationLength δ hpred hA hδ hξ)

theorem hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    correlationLength δ hpred hA hδ hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ

theorem
    valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W
      |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
        correlationLength A δ hpred hδ hA hlogA hξ)

theorem
    hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    correlationLength A δ hpred hδ hA hlogA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W
      |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
        correlationLength mass B δ hpred hδ hB hlogB hmass hξ)

theorem
    hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    correlationLength mass B δ hpred hδ hB hlogB hmass hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)
    hpred

theorem valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
      correlationLength hpred hA hξ)

theorem hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    correlationLength hpred hA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)
    hpred

theorem
    valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
      correlationLength A hpred hA hlogA hξ)

theorem
    hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    correlationLength A hpred hA hlogA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)
    hpred

theorem
    valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
      correlationLength mass B hpred hB hlogB hmass hξ)

theorem
    hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : FiniteWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    correlationLength mass B hpred hB hlogB hmass hξ).hasCriticalNu

end FiniteWitnessPackage

namespace InfiniteTailWitnessPackage

variable {ι α : Type*} [DecidableEq α] {M : CriticalModel ι}



theorem rgToExponentBridge_of_eventually_exact_power_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_power_prefactor
    correlationLength hA hξ



theorem valid_of_eventually_exact_power_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)



theorem hasCriticalNu_of_eventually_exact_power_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)



theorem rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    correlationLength δ hA hδ hξ



theorem valid_of_exact_power_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)



theorem hasCriticalNu_of_exact_power_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)



theorem rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    correlationLength A hA hlogA hξ



theorem valid_of_eventually_exact_power_variable_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)



theorem hasCriticalNu_of_eventually_exact_power_variable_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)



theorem rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    correlationLength A δ hδ hA hlogA hξ



theorem valid_of_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)



theorem hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)



theorem rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    correlationLength mass B hB hlogB hmass hξ



theorem valid_of_eventually_exact_mass_power_variable_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)



theorem hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    (W : InfiniteTailWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)



theorem rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    correlationLength mass B δ hδ hB hlogB hmass hξ



theorem valid_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)



theorem hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailWitnessPackage (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)

theorem
    rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ

theorem valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      correlationLength δ hpred hA hδ hξ)

theorem hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    correlationLength δ hpred hA hδ hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ

theorem
    valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W
      |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
        correlationLength A δ hpred hδ hA hlogA hξ)

theorem
    hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    correlationLength A δ hpred hδ hA hlogA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W
      |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
        correlationLength mass B δ hpred hδ hB hlogB hmass hξ)

theorem
    hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    correlationLength mass B δ hpred hδ hB hlogB hmass hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)
    hpred

theorem valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
      correlationLength hpred hA hξ)

theorem hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    correlationLength hpred hA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)
    hpred

theorem
    valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
      correlationLength A hpred hA hlogA hξ)

theorem
    hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    correlationLength A hpred hA hlogA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)
    hpred

theorem
    valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
      correlationLength mass B hpred hB hlogB hmass hξ)

theorem
    hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailWitnessPackage (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    correlationLength mass B hpred hB hlogB hmass hξ).hasCriticalNu

end InfiniteTailWitnessPackage

namespace InfiniteTailTableWitnessPackage

variable {ι Case α : Type*} [DecidableEq Case] [DecidableEq α]
variable {M : CriticalModel ι}



theorem rgToExponentBridge_of_eventually_exact_power_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_power_prefactor
    correlationLength hA hξ




theorem valid_of_eventually_exact_power_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)



theorem hasCriticalNu_of_eventually_exact_power_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)



theorem rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    correlationLength δ hA hδ hξ



theorem valid_of_exact_power_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)




theorem hasCriticalNu_of_exact_power_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)



theorem rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    correlationLength A hA hlogA hξ



theorem valid_of_eventually_exact_power_variable_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)



theorem hasCriticalNu_of_eventually_exact_power_variable_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)



theorem rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    correlationLength A δ hδ hA hlogA hξ



theorem valid_of_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)



theorem hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
          A β * Real.exp (-W.certificate.predictedExponent *
            Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)



theorem rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    correlationLength mass B hB hlogB hmass hξ



theorem valid_of_eventually_exact_mass_power_variable_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)



theorem hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)



theorem rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    correlationLength mass B δ hδ hB hlogB hmass hξ



theorem valid_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)



theorem hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
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
            (W.certificate.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  W.hasCriticalNu_of_bridge
    (W.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)

theorem
    rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ

theorem valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      correlationLength δ hpred hA hδ hξ)

theorem hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    correlationLength δ hpred hA hδ hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ

theorem
    valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W
      |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
        correlationLength A δ hpred hδ hA hlogA hξ)

theorem
    hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    correlationLength A δ hpred hδ hA hlogA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  W.certificate
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

theorem
    valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W
      |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
        correlationLength mass B δ hpred hδ hB hlogB hmass hξ)

theorem
    hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    correlationLength mass B δ hpred hδ hB hlogB hmass hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)
    hpred

theorem valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
      correlationLength hpred hA hξ)

theorem hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength : ℝ → ℝ)
    {A : ℝ} (hpred : W.certificate.predictedExponent = D.predictedExponent)
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    correlationLength hpred hA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)
    hpred

theorem
    valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
      correlationLength A hpred hA hlogA hξ)

theorem
    hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength A : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    correlationLength A hpred hA hlogA hξ).hasCriticalNu

theorem
    rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)
    hpred

theorem
    valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    W.certificate.Valid correlationLength :=
  W.valid_of_bridge
    (W.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
      correlationLength mass B hpred hB hlogB hmass hξ)

theorem
    hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
    {D : RGCertificate M} (correlationLength mass B : ℝ → ℝ)
    (hpred : W.certificate.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength W.certificate.predictedExponent :=
  (W.valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    correlationLength mass B hpred hB hlogB hmass hξ).hasCriticalNu

end InfiniteTailTableWitnessPackage

end Exact3D
end StatMech
