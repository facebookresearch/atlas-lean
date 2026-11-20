/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.PowerLawBridge











namespace StatMech
namespace Exact3D





structure LeftCriticalReparam {ι κ : Type*} (M : CriticalModel ι)
    (N : CriticalModel κ) (φ : ℝ → ℝ) : Prop where
  tendsto_left :
    Filter.Tendsto φ (nhdsWithin M.betaC (Set.Iio M.betaC))
      (nhdsWithin N.betaC (Set.Iio N.betaC))
  log_distance_ratio :
    Filter.Tendsto
      (fun β : ℝ => Real.log (N.betaC - φ β) / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 1)

namespace LeftCriticalReparam


theorem id {ι : Type*} (M : CriticalModel ι) :
    LeftCriticalReparam M M id where
  tendsto_left := Filter.tendsto_id
  log_distance_ratio := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards
      [Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)] with β hβ
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβ.1, hβ.2]
    have hlog_ne : Real.log (M.betaC - β) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    rw [show _root_.id β = β by rfl]
    field_simp [hlog_ne]



def linearMap {ι κ : Type*} (M : CriticalModel ι) (N : CriticalModel κ)
    (a : ℝ) (β : ℝ) : ℝ :=
  N.betaC - a * (M.betaC - β)



theorem linear {ι κ : Type*} (M : CriticalModel ι) (N : CriticalModel κ)
    {a : ℝ} (ha : 0 < a) :
    LeftCriticalReparam M N (linearMap M N a) where
  tendsto_left := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hd :
          Filter.Tendsto (fun β : ℝ => M.betaC - β)
            (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) :=
        (tendsto_betaC_sub_nhdsWithin_Iio M).mono_right nhdsWithin_le_nhds
      have hcont : ContinuousAt (fun d : ℝ => N.betaC - a * d) 0 := by
        fun_prop
      simpa [linearMap] using hcont.tendsto.comp hd
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      have hdpos : 0 < M.betaC - β := sub_pos.mpr hβ
      have hprod : 0 < a * (M.betaC - β) := mul_pos ha hdpos
      change N.betaC - a * (M.betaC - β) < N.betaC
      exact sub_lt_self N.betaC hprod
  log_distance_ratio := by
    let L := nhdsWithin M.betaC (Set.Iio M.betaC)
    have hlogd :
        Filter.Tendsto (fun β : ℝ => Real.log (M.betaC - β)) L Filter.atBot := by
      simpa [L] using tendsto_log_betaC_sub_atBot M
    have hconst :
        Filter.Tendsto
          (fun β : ℝ => Real.log a / Real.log (M.betaC - β))
          L (nhds 0) :=
      hlogd.const_div_atBot (Real.log a)
    have hlim :
        Filter.Tendsto
          (fun β : ℝ => 1 + Real.log a / Real.log (M.betaC - β))
          L (nhds (1 + 0)) :=
      tendsto_const_nhds.add hconst
    refine Filter.Tendsto.congr' ?_ (by simpa using hlim)
    filter_upwards
      [Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)] with β hβ
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβ.1, hβ.2]
    have hlog_ne : Real.log (M.betaC - β) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    have ha_ne : a ≠ 0 := ha.ne'
    have hdiff_ne : M.betaC - β ≠ 0 := hdiff.1.ne'
    dsimp [linearMap]
    rw [show N.betaC - (N.betaC - a * (M.betaC - β)) =
        a * (M.betaC - β) by ring]
    rw [Real.log_mul ha_ne hdiff_ne]
    field_simp [hlog_ne]
    ring



theorem eventually_comp_left {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {φ : ℝ → ℝ}
    (hφ : LeftCriticalReparam M N φ) {P : ℝ → Prop}
    (hP : ∀ᶠ γ in nhdsWithin N.betaC (Set.Iio N.betaC), P γ) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), P (φ β) :=
  hφ.tendsto_left.eventually hP



theorem eventually_eq_comp_left {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ} {φ f g : ℝ → ℝ}
    (hφ : LeftCriticalReparam M N φ)
    (hEq : ∀ᶠ γ in nhdsWithin N.betaC (Set.Iio N.betaC), f γ = g γ) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
      f (φ β) = g (φ β) :=
  hφ.eventually_comp_left hEq

end LeftCriticalReparam


theorem HasCriticalNu.comp_leftCriticalReparam {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ}
    {correlationLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ) :
    HasCriticalNu M (fun β => correlationLength (φ β)) ν := by
  unfold HasCriticalNu at hν ⊢
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hslope :
      Filter.Tendsto (fun β : ℝ => logSlope N correlationLength (φ β))
        L (nhds ν) := by
    simpa [L] using hν.comp hφ.tendsto_left
  have hprod :
      Filter.Tendsto
        (fun β : ℝ =>
          logSlope N correlationLength (φ β) *
            (Real.log (N.betaC - φ β) / Real.log (M.betaC - β)))
        L (nhds (ν * 1)) :=
    hslope.mul hφ.log_distance_ratio
  have heq :
      ∀ᶠ β in L,
        logSlope M (fun β => correlationLength (φ β)) β =
          logSlope N correlationLength (φ β) *
            (Real.log (N.betaC - φ β) / Real.log (M.betaC - β)) := by
    have hNevent :
        ∀ᶠ β in L, φ β ∈ Set.Ioo (N.betaC - 1) N.betaC := by
      change ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        φ β ∈ Set.Ioo (N.betaC - 1) N.betaC
      exact hφ.tendsto_left.eventually
        (Ioo_mem_nhdsLT (show N.betaC - 1 < N.betaC by linarith))
    have hMevent :
        ∀ᶠ β in L, β ∈ Set.Ioo (M.betaC - 1) M.betaC := by
      change ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        β ∈ Set.Ioo (M.betaC - 1) M.betaC
      exact Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)
    filter_upwards [hNevent, hMevent] with β hNβ hMβ
    have hNdiff : N.betaC - φ β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hNβ.1, hNβ.2]
    have hMdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hMβ.1, hMβ.2]
    have hlogN_ne : Real.log (N.betaC - φ β) ≠ 0 :=
      (Real.log_neg hNdiff.1 hNdiff.2).ne
    have hlogM_ne : Real.log (M.betaC - β) ≠ 0 :=
      (Real.log_neg hMdiff.1 hMdiff.2).ne
    unfold logSlope
    field_simp [hlogN_ne, hlogM_ne]
  have hmain := Filter.Tendsto.congr' (heq.mono fun _ h => h.symm) hprod
  simpa using hmain



theorem HasCriticalNu.comp_leftCriticalReparam_congr_eventually {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ}
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength ν :=
  (hν.comp_leftCriticalReparam hφ).congr_eventually hEq

namespace RGCertificate




theorem rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν : HasCriticalNu N correlationLength C.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    C.RGToExponentBridge comparisonLength :=
  hν.comp_leftCriticalReparam_congr_eventually hφ hEq



theorem
    rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : C.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    C.RGToExponentBridge comparisonLength :=
  C.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    (by simpa [hpred] using hν) hφ hEq



theorem rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    C.RGToExponentBridge comparisonLength := by
  refine C.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    ?_ hφ hEq
  simpa [RGToExponentBridge, hpred] using hbridge



theorem
    rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : C.predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    C.RGToExponentBridge comparisonLength :=
  C.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred.symm hbridge hφ hEq



theorem rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : (C.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    C.RGToExponentBridge comparisonLength :=
  C.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    (C.retarget N) rfl hbridge hφ hEq




theorem valid_of_reparameterized_rgToExponentBridge_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid comparisonLength :=
  C.valid_of_bridge comparisonLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      D hpred hbridge hφ hEq)




theorem valid_of_reparameterized_retargetBridge_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : (C.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid comparisonLength :=
  C.valid_of_bridge comparisonLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hbridge hφ hEq)



theorem valid_of_reparameterized_hasCriticalNu_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν : HasCriticalNu N correlationLength C.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid comparisonLength :=
  C.valid_of_bridge comparisonLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hν hφ hEq)




theorem
    valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : C.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid comparisonLength :=
  C.valid_of_reparameterized_hasCriticalNu_eventually_eq
    (by simpa [hpred] using hν) hφ hEq
    hfinite htail hfixed hlinear hhyperbolic horbit




theorem hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M) (D : RGCertificate N)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength C.predictedExponent :=
  C.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    D hpred hbridge hφ hEq




theorem hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hbridge : (C.retarget N).RGToExponentBridge correlationLength)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength C.predictedExponent :=
  C.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    hbridge hφ hEq



theorem hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ}
    (hν : HasCriticalNu N correlationLength C.predictedExponent)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength C.predictedExponent :=
  C.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    hν hφ hEq




theorem
    hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    {ι κ : Type*} {M : CriticalModel ι} {N : CriticalModel κ}
    (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ} {φ : ℝ → ℝ} {ν : ℝ}
    (hpred : C.predictedExponent = ν)
    (hν : HasCriticalNu N correlationLength ν)
    (hφ : LeftCriticalReparam M N φ)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength (φ β)) :
    HasCriticalNu M comparisonLength C.predictedExponent :=
  C.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    hpred hν hφ hEq

end RGCertificate

end Exact3D
end StatMech
