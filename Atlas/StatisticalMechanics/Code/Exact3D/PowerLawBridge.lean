/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.RGBridgeCriteria










namespace StatMech
namespace Exact3D



theorem tendsto_betaC_sub_nhdsWithin_Iio {ι : Type*} (M : CriticalModel ι) :
    Filter.Tendsto (fun β : ℝ => M.betaC - β)
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhdsWithin 0 (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : ContinuousAt (fun β : ℝ => M.betaC - β) M.betaC := by
      simpa using (continuous_const.sub continuous_id).continuousAt
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact sub_pos.mpr (show β < M.betaC by simpa using hβ)


theorem tendsto_log_betaC_sub_atBot {ι : Type*} (M : CriticalModel ι) :
    Filter.Tendsto (fun β : ℝ => Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) Filter.atBot := by
  exact Real.tendsto_log_nhdsGT_zero.comp (tendsto_betaC_sub_nhdsWithin_Iio M)



theorem logSlope_eq_of_exact_power_prefactor {ι : Type*} (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ) (A ν β : ℝ) (hA : 0 < A)
    (hβ : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1)
    (hξ :
      correlationLength β =
        A * Real.exp (-ν * Real.log (M.betaC - β))) :
    logSlope M correlationLength β =
      ν - Real.log A / Real.log (M.betaC - β) := by
  have hpos : 0 < M.betaC - β := hβ.1
  have hlt : M.betaC - β < 1 := hβ.2
  have hlog_ne : Real.log (M.betaC - β) ≠ 0 :=
    (Real.log_neg hpos hlt).ne
  have hA_ne : A ≠ 0 := hA.ne'
  have hexp_ne : Real.exp (-ν * Real.log (M.betaC - β)) ≠ 0 :=
    Real.exp_ne_zero _
  unfold logSlope
  rw [hξ, Real.log_mul hA_ne hexp_ne, Real.log_exp]
  field_simp [hlog_ne]
  ring



theorem logSlope_eq_of_exact_power_variable_prefactor {ι : Type*}
    (M : CriticalModel ι) (correlationLength A : ℝ → ℝ) (ν β : ℝ)
    (hA : 0 < A β)
    (hβ : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1)
    (hξ :
      correlationLength β =
        A β * Real.exp (-ν * Real.log (M.betaC - β))) :
    logSlope M correlationLength β =
      ν - Real.log (A β) / Real.log (M.betaC - β) := by
  exact logSlope_eq_of_exact_power_prefactor M correlationLength (A β) ν β hA hβ hξ



theorem hasCriticalNu_of_eventually_exact_power_prefactor {ι : Type*}
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ) {A ν : ℝ}
    (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-ν * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength ν := by
  unfold HasCriticalNu
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hlog :
      Filter.Tendsto (fun β : ℝ => Real.log (M.betaC - β)) L Filter.atBot := by
    simpa [L] using tendsto_log_betaC_sub_atBot M
  have hpref :
      Filter.Tendsto
        (fun β : ℝ => Real.log A / Real.log (M.betaC - β)) L (nhds 0) :=
    hlog.const_div_atBot (Real.log A)
  have hlimit :
      Filter.Tendsto
        (fun β : ℝ => ν - Real.log A / Real.log (M.betaC - β)) L (nhds ν) := by
    simpa using (tendsto_const_nhds.sub hpref)
  refine Filter.Tendsto.congr' ?_ hlimit
  filter_upwards
    [hξ,
      Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)] with β hξβ hβ
  have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hβ.1, hβ.2]
  exact (logSlope_eq_of_exact_power_prefactor M correlationLength A ν β hA hdiff hξβ).symm



theorem hasCriticalNu_of_exact_power_prefactor_on_Ioo {ι : Type*}
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ) {A ν : ℝ}
    (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-ν * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength ν := by
  refine hasCriticalNu_of_eventually_exact_power_prefactor M correlationLength hA ?_
  filter_upwards [Ioo_mem_nhdsLT (by linarith : M.betaC - δ < M.betaC)] with β hβ
  exact hξ β hβ




theorem hasCriticalNu_of_eventually_exact_power_variable_prefactor {ι : Type*}
    (M : CriticalModel ι) (correlationLength A : ℝ → ℝ) (ν : ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-ν * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength ν := by
  unfold HasCriticalNu
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hlimit :
      Filter.Tendsto
        (fun β : ℝ => ν - Real.log (A β) / Real.log (M.betaC - β))
        L (nhds ν) := by
    simpa [L] using (tendsto_const_nhds.sub hlogA)
  refine Filter.Tendsto.congr' ?_ hlimit
  filter_upwards
    [hA, hξ, Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)]
    with β hAβ hξβ hβ
  have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hβ.1, hβ.2]
  exact (logSlope_eq_of_exact_power_variable_prefactor
    M correlationLength A ν β hAβ hdiff hξβ).symm



theorem hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo {ι : Type*}
    (M : CriticalModel ι) (correlationLength A : ℝ → ℝ) (ν δ : ℝ)
    (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-ν * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength ν := by
  refine hasCriticalNu_of_eventually_exact_power_variable_prefactor
    M correlationLength A ν ?_ hlogA ?_
  · filter_upwards [Ioo_mem_nhdsLT (by linarith : M.betaC - δ < M.betaC)] with β hβ
    exact hA β hβ
  · filter_upwards [Ioo_mem_nhdsLT (by linarith : M.betaC - δ < M.betaC)] with β hβ
    exact hξ β hβ


theorem tendsto_log_inv_prefactor_div_log_betaC_sub {ι : Type*}
    (M : CriticalModel ι) {A : ℝ → ℝ}
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ => Real.log ((A β)⁻¹) / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ (by simpa using hlogA.neg)
  filter_upwards [hA] with β hAβ
  calc
    -(Real.log (A β) / Real.log (M.betaC - β)) =
        (-Real.log (A β)) / Real.log (M.betaC - β) := by
      ring
    _ = Real.log ((A β)⁻¹) / Real.log (M.betaC - β) := by
      rw [Real.log_inv]



theorem hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo {ι : Type*}
    (M : CriticalModel ι) (correlationLength mass B : ℝ → ℝ) (ν δ : ℝ)
    (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β = B β * Real.exp (ν * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength ν := by
  refine hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    M correlationLength (fun β => (B β)⁻¹) ν δ hδ ?_ ?_ ?_
  · intro β hβ
    exact inv_pos.mpr (hB β hβ)
  · refine tendsto_log_inv_prefactor_div_log_betaC_sub M ?_ hlogB
    filter_upwards [Ioo_mem_nhdsLT (by linarith : M.betaC - δ < M.betaC)] with β hβ
    exact hB β hβ
  · intro β hβ
    rw [hξ β hβ, hmass β hβ]
    have hBne : B β ≠ 0 := (hB β hβ).ne'
    have hexpne :
        Real.exp (ν * Real.log (M.betaC - β)) ≠ 0 :=
      Real.exp_ne_zero _
    rw [show -ν * Real.log (M.betaC - β) =
        -(ν * Real.log (M.betaC - β)) by ring, Real.exp_neg]
    field_simp [hBne, hexpne]



theorem hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    {ι : Type*} (M : CriticalModel ι) (correlationLength mass B : ℝ → ℝ)
    (ν : ℝ)
    (hB :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β = B β * Real.exp (ν * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength ν := by
  refine hasCriticalNu_of_eventually_exact_power_variable_prefactor
    M correlationLength (fun β => (B β)⁻¹) ν ?_ ?_ ?_
  · filter_upwards [hB] with β hBβ
    exact inv_pos.mpr hBβ
  · exact tendsto_log_inv_prefactor_div_log_betaC_sub M hB hlogB
  · filter_upwards [hB, hmass, hξ] with β hBβ hmassβ hξβ
    rw [hξβ, hmassβ]
    have hBne : B β ≠ 0 := hBβ.ne'
    have hexpne :
        Real.exp (ν * Real.log (M.betaC - β)) ≠ 0 :=
      Real.exp_ne_zero _
    rw [show -ν * Real.log (M.betaC - β) =
        -(ν * Real.log (M.betaC - β)) by ring, Real.exp_neg]
    field_simp [hBne, hexpne]




theorem HasCriticalNu.mul_log_negligible_prefactor {ι : Type*}
    {M : CriticalModel ι} {correlationLength A : ℝ → ℝ} {ν : ℝ}
    (hν : HasCriticalNu M correlationLength ν)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    HasCriticalNu M (fun β => A β * correlationLength β) ν := by
  unfold HasCriticalNu at hν ⊢
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hlimit :
      Filter.Tendsto
        (fun β : ℝ =>
          logSlope M correlationLength β -
            Real.log (A β) / Real.log (M.betaC - β))
        L (nhds ν) := by
    simpa [L] using hν.sub hlogA
  refine Filter.Tendsto.congr' ?_ hlimit
  filter_upwards [hξpos, hApos] with β hξβ hAβ
  have hξ_ne : correlationLength β ≠ 0 := hξβ.ne'
  have hA_ne : A β ≠ 0 := hAβ.ne'
  have hEq :
      logSlope M (fun β => A β * correlationLength β) β =
        logSlope M correlationLength β -
          Real.log (A β) / Real.log (M.betaC - β) := by
    unfold logSlope
    rw [Real.log_mul hA_ne hξ_ne]
    ring
  exact hEq.symm



theorem HasCriticalNu.const_mul {ι : Type*}
    {M : CriticalModel ι} {correlationLength : ℝ → ℝ} {ν A : ℝ}
    (hν : HasCriticalNu M correlationLength ν)
    (hA : 0 < A)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β) :
    HasCriticalNu M (fun β => A * correlationLength β) ν := by
  let Apref : ℝ → ℝ := fun _ => A
  refine hν.mul_log_negligible_prefactor (A := Apref) hξpos ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => hA
  · let L := nhdsWithin M.betaC (Set.Iio M.betaC)
    have hlogd :
        Filter.Tendsto (fun β : ℝ => Real.log (M.betaC - β)) L Filter.atBot := by
      simpa [L] using tendsto_log_betaC_sub_atBot M
    simpa [Apref, L] using hlogd.const_div_atBot (Real.log A)




theorem tendsto_log_bounded_prefactor_div_log_betaC_sub {ι : Type*}
    (M : CriticalModel ι) {A : ℝ → ℝ} {cLo cHi : ℝ}
    (hcLo : 0 < cLo) (_hcHi : 0 < cHi)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ A β ∧ A β ≤ cHi) :
    Filter.Tendsto
      (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hlogd :
      Filter.Tendsto (fun β : ℝ => Real.log (M.betaC - β)) L Filter.atBot := by
    simpa [L] using tendsto_log_betaC_sub_atBot M
  have hlo_tendsto :
      Filter.Tendsto
        (fun β : ℝ => Real.log cHi / Real.log (M.betaC - β))
        L (nhds 0) :=
    hlogd.const_div_atBot (Real.log cHi)
  have hhi_tendsto :
      Filter.Tendsto
        (fun β : ℝ => Real.log cLo / Real.log (M.betaC - β))
        L (nhds 0) :=
    hlogd.const_div_atBot (Real.log cLo)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_tendsto hhi_tendsto ?_ ?_
  · filter_upwards
      [hA, Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)]
      with β hAβ hβ
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβ.1, hβ.2]
    have hlog_neg : Real.log (M.betaC - β) < 0 :=
      Real.log_neg hdiff.1 hdiff.2
    have hApos : 0 < A β := lt_of_lt_of_le hcLo hAβ.1
    have hlog_le : Real.log (A β) ≤ Real.log cHi :=
      Real.log_le_log hApos hAβ.2
    exact div_le_div_of_nonpos_of_le hlog_neg.le hlog_le
  · filter_upwards
      [hA, Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)]
      with β hAβ hβ
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβ.1, hβ.2]
    have hlog_neg : Real.log (M.betaC - β) < 0 :=
      Real.log_neg hdiff.1 hdiff.2
    have hlog_le : Real.log cLo ≤ Real.log (A β) :=
      Real.log_le_log hcLo hAβ.1
    exact div_le_div_of_nonpos_of_le hlog_neg.le hlog_le



theorem HasCriticalNu.of_eventually_const_mul_le_le {ι : Type*}
    {M : CriticalModel ι} {correlationLength comparisonLength : ℝ → ℝ}
    {ν cLo cHi : ℝ}
    (hν : HasCriticalNu M correlationLength ν)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength ν := by
  let A : ℝ → ℝ := fun β => comparisonLength β / correlationLength β
  have hAbounds :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ A β ∧ A β ≤ cHi := by
    filter_upwards [hξpos, hcompare] with β hξβ hβ
    constructor
    · rw [le_div_iff₀ hξβ]
      exact hβ.1
    · rw [div_le_iff₀ hξβ]
      exact hβ.2
  have hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β := by
    filter_upwards [hAbounds] with β hβ
    exact lt_of_lt_of_le hcLo hβ.1
  have hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) :=
    tendsto_log_bounded_prefactor_div_log_betaC_sub M hcLo hcHi hAbounds
  have hmul :
      HasCriticalNu M (fun β => A β * correlationLength β) ν :=
    hν.mul_log_negligible_prefactor hξpos hApos hlogA
  unfold HasCriticalNu at hmul ⊢
  refine Filter.Tendsto.congr' ?_ hmul
  filter_upwards [hξpos] with β hξβ
  have hξ_ne : correlationLength β ≠ 0 := hξβ.ne'
  have hpoint :
      A β * correlationLength β = comparisonLength β := by
    dsimp [A]
    field_simp [hξ_ne]
  unfold logSlope
  change -Real.log (A β * correlationLength β) / Real.log (M.betaC - β) =
    -Real.log (comparisonLength β) / Real.log (M.betaC - β)
  rw [hpoint]





theorem hasCriticalNu_of_eventually_const_mul_exact_power_le_le {ι : Type*}
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ) {ν cLo cHi : ℝ}
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * Real.exp (-ν * Real.log (M.betaC - β)) ≤
            correlationLength β ∧
          correlationLength β ≤
            cHi * Real.exp (-ν * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength ν := by
  let base : ℝ → ℝ :=
    fun β => Real.exp (-ν * Real.log (M.betaC - β))
  have hbase : HasCriticalNu M base ν := by
    refine hasCriticalNu_of_eventually_exact_power M base ν ?_
    exact Filter.Eventually.of_forall fun β => rfl
  have hbasepos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < base β :=
    Filter.Eventually.of_forall fun β => Real.exp_pos _
  exact hbase.of_eventually_const_mul_le_le hbasepos hcLo hcHi (by
    simpa [base] using hcompare)



theorem hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo {ι : Type*}
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ) {ν cLo cHi δ : ℝ}
    (hδ : 0 < δ) (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        cLo * Real.exp (-ν * Real.log (M.betaC - β)) ≤
            correlationLength β ∧
          correlationLength β ≤
            cHi * Real.exp (-ν * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength ν := by
  refine hasCriticalNu_of_eventually_const_mul_exact_power_le_le
    M correlationLength hcLo hcHi ?_
  filter_upwards [Ioo_mem_nhdsLT (by linarith : M.betaC - δ < M.betaC)]
    with β hβ
  exact hcompare β hβ

namespace RGCertificate



theorem rgToExponentBridge_mul_log_negligible_prefactor {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength A : ℝ → ℝ}
    (hbridge : C.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    C.RGToExponentBridge (fun β => A β * correlationLength β) :=
  hbridge.mul_log_negligible_prefactor hξpos hApos hlogA



theorem
    rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} {C D : RGCertificate M}
    {correlationLength A : ℝ → ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    C.RGToExponentBridge (fun β => A β * correlationLength β) :=
  rgToExponentBridge_mul_log_negligible_prefactor
    (rgToExponentBridge_congr_predictedExponent hbridge hpred)
    hξpos hApos hlogA



theorem hasCriticalNu_mul_log_negligible_prefactor {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M)
    {correlationLength A : ℝ → ℝ}
    (hbridge : C.RGToExponentBridge correlationLength)
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
      C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (rgToExponentBridge_mul_log_negligible_prefactor
      hbridge hξpos hApos hlogA)



theorem Valid.mul_log_negligible_prefactor {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength A : ℝ → ℝ}
    (hC : C.Valid correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hApos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    C.Valid (fun β => A β * correlationLength β) where
  finiteCaseChecks := hC.finiteCaseChecks
  tailBounds := hC.tailBounds
  fixedPointEnclosure := hC.fixedPointEnclosure
  linearizationEnclosure := hC.linearizationEnclosure
  hyperbolicSplitting := hC.hyperbolicSplitting
  orbitEntry := hC.orbitEntry
  bridge :=
    rgToExponentBridge_mul_log_negligible_prefactor
      hC.bridge hξpos hApos hlogA



theorem Valid.hasCriticalNu_mul_log_negligible_prefactor {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength A : ℝ → ℝ}
    (hC : C.Valid correlationLength)
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
      C.predictedExponent :=
  (hC.mul_log_negligible_prefactor hξpos hApos hlogA).hasCriticalNu



theorem rgToExponentBridge_of_eventually_const_mul_le_le {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    {cLo cHi : ℝ}
    (hbridge : C.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    C.RGToExponentBridge comparisonLength :=
  hbridge.of_eventually_const_mul_le_le hξpos hcLo hcHi hcompare



theorem
    rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} {C D : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ} {cLo cHi : ℝ}
    (hbridge : D.RGToExponentBridge correlationLength)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    C.RGToExponentBridge comparisonLength :=
  rgToExponentBridge_of_eventually_const_mul_le_le
    (rgToExponentBridge_congr_predictedExponent hbridge hpred)
    hξpos hcLo hcHi hcompare



theorem hasCriticalNu_of_eventually_const_mul_le_le {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M)
    {correlationLength comparisonLength : ℝ → ℝ}
    {cLo cHi : ℝ}
    (hbridge : C.RGToExponentBridge correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (rgToExponentBridge_of_eventually_const_mul_le_le
      hbridge hξpos hcLo hcHi hcompare)



theorem Valid.of_eventually_const_mul_le_le {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    {cLo cHi : ℝ}
    (hC : C.Valid correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    C.Valid comparisonLength where
  finiteCaseChecks := hC.finiteCaseChecks
  tailBounds := hC.tailBounds
  fixedPointEnclosure := hC.fixedPointEnclosure
  linearizationEnclosure := hC.linearizationEnclosure
  hyperbolicSplitting := hC.hyperbolicSplitting
  orbitEntry := hC.orbitEntry
  bridge :=
    rgToExponentBridge_of_eventually_const_mul_le_le
      hC.bridge hξpos hcLo hcHi hcompare



theorem Valid.hasCriticalNu_of_eventually_const_mul_le_le {ι : Type*}
    {M : CriticalModel ι} {C : RGCertificate M}
    {correlationLength comparisonLength : ℝ → ℝ}
    {cLo cHi : ℝ}
    (hC : C.Valid correlationLength)
    (hξpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < correlationLength β)
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo * correlationLength β ≤ comparisonLength β ∧
          comparisonLength β ≤ cHi * correlationLength β) :
    HasCriticalNu M comparisonLength C.predictedExponent :=
  (hC.of_eventually_const_mul_le_le hξpos hcLo hcHi hcompare).hasCriticalNu



theorem rgToExponentBridge_of_eventually_const_mul_exact_power_le_le
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength : ℝ → ℝ) {cLo cHi : ℝ}
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤
            correlationLength β ∧
          correlationLength β ≤
            cHi *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength :=
  hasCriticalNu_of_eventually_const_mul_exact_power_le_le
    M correlationLength hcLo hcHi hcompare



theorem hasCriticalNu_of_eventually_const_mul_exact_power_le_le
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength : ℝ → ℝ) {cLo cHi : ℝ}
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤
            correlationLength β ∧
          correlationLength β ≤
            cHi *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_eventually_const_mul_exact_power_le_le
      correlationLength hcLo hcHi hcompare)



theorem valid_of_eventually_const_mul_exact_power_le_le
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength : ℝ → ℝ) {cLo cHi : ℝ}
    (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤
            correlationLength β ∧
          correlationLength β ≤
            cHi *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_eventually_const_mul_exact_power_le_le
      correlationLength hcLo hcHi hcompare)



theorem rgToExponentBridge_of_const_mul_exact_power_le_le_on_Ioo
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength : ℝ → ℝ) {cLo cHi δ : ℝ}
    (hδ : 0 < δ) (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        cLo *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤
            correlationLength β ∧
          correlationLength β ≤
            cHi *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength :=
  hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo
    M correlationLength hδ hcLo hcHi hcompare



theorem hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength : ℝ → ℝ) {cLo cHi δ : ℝ}
    (hδ : 0 < δ) (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        cLo *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤
            correlationLength β ∧
          correlationLength β ≤
            cHi *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_const_mul_exact_power_le_le_on_Ioo
      correlationLength hδ hcLo hcHi hcompare)



theorem valid_of_const_mul_exact_power_le_le_on_Ioo
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength : ℝ → ℝ) {cLo cHi δ : ℝ}
    (hδ : 0 < δ) (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hcompare :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        cLo *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤
            correlationLength β ∧
          correlationLength β ≤
            cHi *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_const_mul_exact_power_le_le_on_Ioo
      correlationLength hδ hcLo hcHi hcompare)




theorem rgToExponentBridge_of_eventually_exact_power_prefactor {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength := by
  exact hasCriticalNu_of_eventually_exact_power_prefactor
    M correlationLength hA hξ



theorem hasCriticalNu_of_eventually_exact_power_prefactor {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)



theorem valid_of_eventually_exact_power_prefactor {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)



theorem
    rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (hpred : C.predictedExponent = D.predictedExponent) (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength :=
  rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_prefactor
      correlationLength hA hξ)
    hpred



theorem
    hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (hpred : C.predictedExponent = D.predictedExponent) (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
      D correlationLength hpred hA hξ)



theorem
    valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (hpred : C.predictedExponent = D.predictedExponent) (hA : 0 < A)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
      D correlationLength hpred hA hξ)



theorem rgToExponentBridge_of_exact_power_prefactor_on_Ioo {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength := by
  exact hasCriticalNu_of_exact_power_prefactor_on_Ioo
    M correlationLength δ hA hδ hξ



theorem hasCriticalNu_of_exact_power_prefactor_on_Ioo {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)



theorem valid_of_exact_power_prefactor_on_Ioo {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    {A : ℝ} (δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)




theorem
    rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength :=
  rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      correlationLength δ hA hδ hξ)
    hpred



theorem
    hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ)




theorem
    valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength : ℝ → ℝ) {A : ℝ}
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
    (hA : 0 < A) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      D correlationLength δ hpred hA hδ hξ)


theorem rgToExponentBridge_of_eventually_exact_power_variable_prefactor {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength A : ℝ → ℝ)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength := by
  exact hasCriticalNu_of_eventually_exact_power_variable_prefactor
    M correlationLength A C.predictedExponent hA hlogA hξ



theorem hasCriticalNu_of_eventually_exact_power_variable_prefactor {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M)
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
          A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)



theorem valid_of_eventually_exact_power_variable_prefactor {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M)
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
          A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)



theorem
    rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
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
    C.RGToExponentBridge correlationLength :=
  rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      correlationLength A hA hlogA hξ)
    hpred



theorem
    hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
      D correlationLength A hpred hA hlogA hξ)



theorem
    valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hA :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
      D correlationLength A hpred hA hlogA hξ)


theorem rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength := by
  exact hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo
    M correlationLength A C.predictedExponent δ hδ hA hlogA hξ



theorem hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)



theorem valid_of_exact_power_variable_prefactor_on_Ioo {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength A : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)




theorem
    rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
    C.RGToExponentBridge correlationLength :=
  rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      correlationLength A δ hδ hA hlogA hξ)
    hpred

theorem
rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
    C.RGToExponentBridge correlationLength :=
  C.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    D correlationLength A δ hpred hδ hA hlogA hξ



theorem
    hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ)

theorem
hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength C.predictedExponent :=
  C.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    D correlationLength A δ hpred hδ hA hlogA hξ




theorem
    valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength A δ hpred hδ hA hlogA hξ)

theorem
valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength A : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
    (hδ : 0 < δ)
    (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
    (hlogA :
      Filter.Tendsto
        (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    D correlationLength A δ hpred hδ hA hlogA hξ
    hfinite htail hfixed hlinear hhyperbolic horbit




theorem rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    C.RGToExponentBridge correlationLength := by
  exact hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    M correlationLength mass B C.predictedExponent δ hδ hB hlogB hmass hξ



theorem hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)



theorem valid_of_exact_mass_power_variable_prefactor_on_Ioo
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
    (hlogB :
      Filter.Tendsto
        (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        mass β =
          B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β = (mass β)⁻¹)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)




theorem
    rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
    C.RGToExponentBridge correlationLength :=
  rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      correlationLength mass B δ hδ hB hlogB hmass hξ)
    hpred

theorem
rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
    C.RGToExponentBridge correlationLength :=
  C.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    D correlationLength mass B δ hpred hδ hB hlogB hmass hξ



theorem
    hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ)

theorem
hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength C.predictedExponent :=
  C.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    D correlationLength mass B δ hpred hδ hB hlogB hmass hξ




theorem
    valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
        correlationLength β = (mass β)⁻¹)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      D correlationLength mass B δ hpred hδ hB hlogB hmass hξ)

theorem
valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (δ : ℝ) (hpred : C.predictedExponent = D.predictedExponent)
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
        correlationLength β = (mass β)⁻¹)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    D correlationLength mass B δ hpred hδ hB hlogB hmass hξ
    hfinite htail hfixed hlinear hhyperbolic horbit



theorem rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
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
            (C.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    C.RGToExponentBridge correlationLength := by
  exact hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    M correlationLength mass B C.predictedExponent hB hlogB hmass hξ



theorem hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
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
            (C.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)



theorem valid_of_eventually_exact_mass_power_variable_prefactor
    {ι : Type*} {M : CriticalModel ι} (C : RGCertificate M)
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
            (C.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)




theorem
    rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
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
    C.RGToExponentBridge correlationLength :=
  rgToExponentBridge_congr_predictedExponent
    (D.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
      correlationLength mass B hB hlogB hmass hξ)
    hpred



theorem
    hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
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
    HasCriticalNu M correlationLength C.predictedExponent := by
  simpa [RGToExponentBridge] using
    (C.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
      D correlationLength mass B hpred hB hlogB hmass hξ)




theorem
    valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
    {ι : Type*} {M : CriticalModel ι} (C D : RGCertificate M)
    (correlationLength mass B : ℝ → ℝ)
    (hpred : C.predictedExponent = D.predictedExponent)
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
        correlationLength β = (mass β)⁻¹)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure)
    (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting)
    (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit
    (C.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent
      D correlationLength mass B hpred hB hlogB hmass hξ)

end RGCertificate

end Exact3D
end StatMech
