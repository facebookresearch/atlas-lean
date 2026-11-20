/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.PowerLawBridge










namespace StatMech
namespace Exact3D

set_option linter.style.longLine false in






theorem tendsto_scaleClock_ratio_of_eventually_annulus {ι : Type*}
    (M : CriticalModel ι) (clock : ℝ → ℝ)
    (relevantEigenvalue cLo cHi : ℝ)
    (heigen : 1 < relevantEigenvalue) (hcLo : 0 < cLo)
    (_hcHi : 0 < cHi)
    (hannulus :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ∧
          Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ≤ cHi) :
    Filter.Tendsto
      (fun β : ℝ => clock β / (-Real.log (M.betaC - β)))
      (nhdsWithin M.betaC (Set.Iio M.betaC))
      (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  let logEigen := Real.log relevantEigenvalue
  have hlogEigen_pos : 0 < logEigen := by
    simpa [logEigen] using Real.log_pos heigen
  have hneglog :
      Filter.Tendsto (fun β : ℝ => -Real.log (M.betaC - β))
        L Filter.atTop := by
    change
      Filter.Tendsto (fun β : ℝ => -(Real.log (M.betaC - β)))
        L Filter.atTop
    exact
      ((Filter.tendsto_neg_atBot_atTop :
        Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop).comp
          (by simpa [L] using tendsto_log_betaC_sub_atBot M))
  have hlo_term :
      Filter.Tendsto
        (fun β : ℝ => Real.log cLo / (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hneglog
  have hhi_term :
      Filter.Tendsto
        (fun β : ℝ => Real.log cHi / (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hneglog
  have hlo_limit :
      Filter.Tendsto
        (fun β : ℝ =>
          (1 + Real.log cLo / (-Real.log (M.betaC - β))) / logEigen)
        L (nhds (logEigen⁻¹)) := by
    have hsum :=
      ((tendsto_const_nhds (x := (1 : ℝ))).add hlo_term).const_mul
        logEigen⁻¹
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hhi_limit :
      Filter.Tendsto
        (fun β : ℝ =>
          (1 + Real.log cHi / (-Real.log (M.betaC - β))) / logEigen)
        L (nhds (logEigen⁻¹)) := by
    have hsum :=
      ((tendsto_const_nhds (x := (1 : ℝ))).add hhi_term).const_mul
        logEigen⁻¹
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_limit hhi_limit ?_ ?_
  · filter_upwards
      [hannulus,
        Ioo_mem_nhdsLT (show M.betaC - (1 : ℝ) < M.betaC by norm_num)]
      with β hb hβdist
    let x := -Real.log (M.betaC - β)
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβdist.1, hβdist.2]
    have hxpos : 0 < x := by
      have hlogneg : Real.log (M.betaC - β) < 0 :=
        Real.log_neg hdiff.1 hdiff.2
      dsimp [x]
      linarith
    have hlog_lo := Real.log_le_log hcLo hb.1
    rw [Real.log_mul (Real.exp_ne_zero _) hdiff.1.ne', Real.log_exp]
      at hlog_lo
    have hnum : x + Real.log cLo ≤ clock β * logEigen := by
      dsimp [x, logEigen]
      linarith
    have hclock_lower : (x + Real.log cLo) / logEigen ≤ clock β := by
      exact (div_le_iff₀ hlogEigen_pos).2 hnum
    have hclock_lower_div :
        (x + Real.log cLo) / logEigen / x ≤ clock β / x := by
      exact div_le_div_of_nonneg_right hclock_lower hxpos.le
    calc
      (1 + Real.log cLo / (-Real.log (M.betaC - β))) / logEigen =
          (x + Real.log cLo) / logEigen / x := by
        change (1 + Real.log cLo / x) / logEigen =
          (x + Real.log cLo) / logEigen / x
        field_simp [hlogEigen_pos.ne', hxpos.ne']
      _ ≤ clock β / x := hclock_lower_div
      _ = clock β / (-Real.log (M.betaC - β)) := by rfl
  · filter_upwards
      [hannulus,
        Ioo_mem_nhdsLT (show M.betaC - (1 : ℝ) < M.betaC by norm_num)]
      with β hb hβdist
    let x := -Real.log (M.betaC - β)
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβdist.1, hβdist.2]
    have hxpos : 0 < x := by
      have hlogneg : Real.log (M.betaC - β) < 0 :=
        Real.log_neg hdiff.1 hdiff.2
      dsimp [x]
      linarith
    have hprod_pos :
        0 < Real.exp (clock β * Real.log relevantEigenvalue) *
            (M.betaC - β) :=
      lt_of_lt_of_le hcLo hb.1
    have hlog_hi := Real.log_le_log hprod_pos hb.2
    rw [Real.log_mul (Real.exp_ne_zero _) hdiff.1.ne', Real.log_exp]
      at hlog_hi
    have hnum : clock β * logEigen ≤ x + Real.log cHi := by
      dsimp [x, logEigen]
      linarith
    have hclock_upper : clock β ≤ (x + Real.log cHi) / logEigen := by
      exact (le_div_iff₀ hlogEigen_pos).2 hnum
    have hclock_upper_div :
        clock β / x ≤ (x + Real.log cHi) / logEigen / x := by
      exact div_le_div_of_nonneg_right hclock_upper hxpos.le
    calc
      clock β / (-Real.log (M.betaC - β)) = clock β / x := by rfl
      _ ≤ (x + Real.log cHi) / logEigen / x := hclock_upper_div
      _ = (1 + Real.log cHi / (-Real.log (M.betaC - β))) / logEigen := by
        change (x + Real.log cHi) / logEigen / x =
          (1 + Real.log cHi / x) / logEigen
        field_simp [hlogEigen_pos.ne', hxpos.ne']

set_option linter.style.longLine false in



noncomputable def criticalDistanceScaleClock {ι : Type*}
    (M : CriticalModel ι) (relevantEigenvalue : ℝ) : ℝ → ℝ :=
  fun β => -Real.log (M.betaC - β) / Real.log relevantEigenvalue

set_option linter.style.longLine false in


theorem criticalDistanceScaleClock_annulus_eq {ι : Type*}
    (M : CriticalModel ι) {relevantEigenvalue β : ℝ}
    (heigen : 1 < relevantEigenvalue) (hβ : 0 < M.betaC - β) :
    Real.exp (criticalDistanceScaleClock M relevantEigenvalue β *
        Real.log relevantEigenvalue) * (M.betaC - β) = 1 := by
  have hlog_ne : Real.log relevantEigenvalue ≠ 0 :=
    (Real.log_pos heigen).ne'
  unfold criticalDistanceScaleClock
  have hmul :
      (-Real.log (M.betaC - β) / Real.log relevantEigenvalue) *
          Real.log relevantEigenvalue = -Real.log (M.betaC - β) := by
    field_simp [hlog_ne]
  rw [hmul, Real.exp_neg, Real.exp_log hβ]
  field_simp [hβ.ne']

set_option linter.style.longLine false in


theorem criticalDistanceScaleClock_annulus_eventually {ι : Type*}
    (M : CriticalModel ι) {relevantEigenvalue : ℝ}
    (heigen : 1 < relevantEigenvalue) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
      (1 : ℝ) ≤
          Real.exp (criticalDistanceScaleClock M relevantEigenvalue β *
            Real.log relevantEigenvalue) * (M.betaC - β) ∧
        Real.exp (criticalDistanceScaleClock M relevantEigenvalue β *
            Real.log relevantEigenvalue) * (M.betaC - β) ≤ 1 := by
  filter_upwards [self_mem_nhdsWithin] with β hβlt
  have hβ : 0 < M.betaC - β := sub_pos.mpr (by simpa using hβlt)
  have hEq := criticalDistanceScaleClock_annulus_eq M heigen hβ
  constructor <;> rw [hEq]

set_option linter.style.longLine false in



theorem tendsto_criticalDistanceScaleClock_ratio {ι : Type*}
    (M : CriticalModel ι) {relevantEigenvalue : ℝ}
    (heigen : 1 < relevantEigenvalue) :
    Filter.Tendsto
      (fun β : ℝ =>
        criticalDistanceScaleClock M relevantEigenvalue β /
          (-Real.log (M.betaC - β)))
      (nhdsWithin M.betaC (Set.Iio M.betaC))
      (nhds ((Real.log relevantEigenvalue)⁻¹)) :=
  tendsto_scaleClock_ratio_of_eventually_annulus
    M (criticalDistanceScaleClock M relevantEigenvalue)
    relevantEigenvalue 1 1 heigen zero_lt_one zero_lt_one
    (criticalDistanceScaleClock_annulus_eventually M heigen)

set_option linter.style.longLine false in


theorem tendsto_sublinear_criticalDistanceScaleClock_self {ι : Type*}
    (M : CriticalModel ι) (relevantEigenvalue : ℝ) :
    Filter.Tendsto
      (fun β : ℝ =>
        (criticalDistanceScaleClock M relevantEigenvalue β -
            criticalDistanceScaleClock M relevantEigenvalue β) /
          (-Real.log (M.betaC - β)))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  simp

set_option linter.style.longLine false in



theorem tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock
    {ι : Type*} (M : CriticalModel ι) (clock : ℝ → ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue)
    (hcompare :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
            (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ => clock β / (-Real.log (M.betaC - β)))
      (nhdsWithin M.betaC (Set.Iio M.betaC))
      (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hcrit := tendsto_criticalDistanceScaleClock_ratio M heigen
  have hsum :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
              (-Real.log (M.betaC - β)) +
            criticalDistanceScaleClock M relevantEigenvalue β /
              (-Real.log (M.betaC - β)))
        L (nhds (0 + (Real.log relevantEigenvalue)⁻¹)) := by
    simpa [L] using hcompare.add hcrit
  have hlimit :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
              (-Real.log (M.betaC - β)) +
            criticalDistanceScaleClock M relevantEigenvalue β /
              (-Real.log (M.betaC - β)))
        L (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
    simpa using hsum
  refine Filter.Tendsto.congr' ?_ hlimit
  filter_upwards with β
  ring

set_option linter.style.longLine false in








theorem tendsto_sublinear_criticalDistanceScaleClock_of_scaleClock_ratio
    {ι : Type*} (M : CriticalModel ι) (clock : ℝ → ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue)
    (hclock :
      Filter.Tendsto
        (fun β : ℝ => clock β / (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC))
        (nhds ((Real.log relevantEigenvalue)⁻¹))) :
    Filter.Tendsto
      (fun β : ℝ =>
        (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
          (-Real.log (M.betaC - β)))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hcrit := tendsto_criticalDistanceScaleClock_ratio M heigen
  have hdiff :
      Filter.Tendsto
        (fun β : ℝ =>
          clock β / (-Real.log (M.betaC - β)) -
            criticalDistanceScaleClock M relevantEigenvalue β /
              (-Real.log (M.betaC - β)))
        L (nhds (((Real.log relevantEigenvalue)⁻¹) -
          ((Real.log relevantEigenvalue)⁻¹))) := by
    simpa [L] using hclock.sub hcrit
  have hzero :
      Filter.Tendsto
        (fun β : ℝ =>
          clock β / (-Real.log (M.betaC - β)) -
            criticalDistanceScaleClock M relevantEigenvalue β /
              (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    simpa using hdiff
  refine Filter.Tendsto.congr' ?_ hzero
  filter_upwards with β
  ring

set_option linter.style.longLine false in


theorem tendsto_scaleClock_ratio_iff_sublinear_criticalDistanceScaleClock
    {ι : Type*} (M : CriticalModel ι) (clock : ℝ → ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue) :
    Filter.Tendsto
        (fun β : ℝ => clock β / (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC))
        (nhds ((Real.log relevantEigenvalue)⁻¹)) ↔
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
            (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  constructor
  · exact tendsto_sublinear_criticalDistanceScaleClock_of_scaleClock_ratio
      M clock heigen
  · exact tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock
      M clock heigen

set_option linter.style.longLine false in


theorem tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
    {ι : Type*} (M : CriticalModel ι) (clock : ℝ → ℝ)
    (relevantEigenvalue cLo cHi : ℝ)
    (heigen : 1 < relevantEigenvalue) (hcLo : 0 < cLo)
    (hcHi : 0 < cHi)
    (hannulus :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ∧
          Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ≤ cHi) :
    Filter.Tendsto
      (fun β : ℝ =>
        (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
          (-Real.log (M.betaC - β)))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  exact
    tendsto_sublinear_criticalDistanceScaleClock_of_scaleClock_ratio
      M clock heigen
      (tendsto_scaleClock_ratio_of_eventually_annulus
        M clock relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus)

set_option linter.style.longLine false in






theorem eventually_pos_of_sublinear_criticalDistanceScaleClock
    {ι : Type*} (M : CriticalModel ι) (clock : ℝ → ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue)
    (hcompare :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
            (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < clock β := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hclock_ratio :
      Filter.Tendsto
        (fun β : ℝ => clock β / (-Real.log (M.betaC - β)))
        L (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
    simpa [L] using
      tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock
        M clock heigen hcompare
  have hlimit_pos : 0 < (Real.log relevantEigenvalue)⁻¹ := by
    exact inv_pos.mpr (Real.log_pos heigen)
  have hratio_pos :
      ∀ᶠ β in L, 0 < clock β / (-Real.log (M.betaC - β)) := by
    exact hclock_ratio.eventually (eventually_gt_nhds hlimit_pos)
  have hneglog :
      Filter.Tendsto (fun β : ℝ => -Real.log (M.betaC - β))
        L Filter.atTop := by
    change
      Filter.Tendsto (fun β : ℝ => -(Real.log (M.betaC - β)))
        L Filter.atTop
    exact
      ((Filter.tendsto_neg_atBot_atTop :
        Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop).comp
          (by simpa [L] using tendsto_log_betaC_sub_atBot M))
  have hden_pos : ∀ᶠ β in L, 0 < -Real.log (M.betaC - β) := by
    exact hneglog.eventually_ge_atTop 1 |>.mono (by intro β hβ; linarith)
  filter_upwards [hratio_pos, hden_pos] with β hratio hden
  have hprod :
      0 < (clock β / (-Real.log (M.betaC - β))) *
          (-Real.log (M.betaC - β)) := mul_pos hratio hden
  have hlog_ne : Real.log (M.betaC - β) ≠ 0 := by
    intro hlog
    rw [hlog] at hden
    norm_num at hden
  have hEq :
      (clock β / (-Real.log (M.betaC - β))) *
          (-Real.log (M.betaC - β)) = clock β := by
    field_simp [hlog_ne]
  simpa [hEq] using hprod

set_option linter.style.longLine false in






theorem tendsto_terminal_add_error_div_log_betaC_sub
    {ι : Type*} (M : CriticalModel ι)
    (terminalLog accumulatedError : ℝ → ℝ) (terminalLimit : ℝ)
    (hterminal :
      Filter.Tendsto terminalLog
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds terminalLimit))
    (herror :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ =>
        (terminalLog β + accumulatedError β) /
          Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hneglog :
      Filter.Tendsto (fun β : ℝ => -Real.log (M.betaC - β))
        L Filter.atTop := by
    change
      Filter.Tendsto (fun β : ℝ => -(Real.log (M.betaC - β)))
        L Filter.atTop
    exact
      ((Filter.tendsto_neg_atBot_atTop :
        Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop).comp
          (by simpa [L] using tendsto_log_betaC_sub_atBot M))
  have hterminal_div_neg :
      Filter.Tendsto
        (fun β : ℝ => (-terminalLog β) / (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    exact (hterminal.neg).div_atTop hneglog
  have hterminal_div :
      Filter.Tendsto
        (fun β : ℝ => terminalLog β / Real.log (M.betaC - β))
        L (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hterminal_div_neg
    filter_upwards with β
    ring
  have hsum :
      Filter.Tendsto
        (fun β : ℝ =>
          terminalLog β / Real.log (M.betaC - β) +
            accumulatedError β / Real.log (M.betaC - β))
        L (nhds (0 + 0)) := by
    simpa [L] using hterminal_div.add herror
  have hzero :
      Filter.Tendsto
        (fun β : ℝ =>
          terminalLog β / Real.log (M.betaC - β) +
            accumulatedError β / Real.log (M.betaC - β))
        L (nhds 0) := by
    simpa using hsum
  refine Filter.Tendsto.congr' ?_ hzero
  filter_upwards with β
  ring

set_option linter.style.longLine false in





theorem eventually_abs_le_abs_limit_add_one_of_tendsto
    {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (hf : Filter.Tendsto f l (nhds a)) :
    ∀ᶠ x in l, |f x| ≤ |a| + 1 := by
  have hnear : ∀ᶠ x in l, f x ∈ Set.Ioo (a - 1) (a + 1) := by
    exact hf.eventually
      (Ioo_mem_nhds (by linarith : a - 1 < a) (by linarith : a < a + 1))
  filter_upwards [hnear] with x hx
  have hdist : |f x - a| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  calc
    |f x| = |(f x - a) + a| := by ring_nf
    _ ≤ |f x - a| + |a| := abs_add_le (f x - a) a
    _ ≤ 1 + |a| := by linarith
    _ = |a| + 1 := by ring

set_option linter.style.longLine false in






theorem tendsto_bounded_terminal_add_error_div_log_betaC_sub
    {ι : Type*} (M : CriticalModel ι)
    (terminalLog accumulatedError : ℝ → ℝ) (terminalBound : ℝ)
    (hterminal :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        |terminalLog β| ≤ terminalBound)
    (herror :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ =>
        (terminalLog β + accumulatedError β) /
          Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hneglog :
      Filter.Tendsto (fun β : ℝ => -Real.log (M.betaC - β))
        L Filter.atTop := by
    change
      Filter.Tendsto (fun β : ℝ => -(Real.log (M.betaC - β)))
        L Filter.atTop
    exact
      ((Filter.tendsto_neg_atBot_atTop :
        Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop).comp
          (by simpa [L] using tendsto_log_betaC_sub_atBot M))
  have hden_nonneg :
      ∀ᶠ β in L, 0 ≤ -Real.log (M.betaC - β) := by
    exact hneglog.eventually_ge_atTop 0
  have hupper :
      Filter.Tendsto
        (fun β : ℝ => terminalBound / (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hneglog
  have hlower :
      Filter.Tendsto
        (fun β : ℝ => (-terminalBound) / (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hneglog
  have hterminal_div_neg :
      Filter.Tendsto
        (fun β : ℝ => (-terminalLog β) / (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
    · filter_upwards [hterminal, hden_nonneg] with β hb hden
      have hbneg : -terminalBound ≤ -terminalLog β := by
        have hle : terminalLog β ≤ terminalBound := (abs_le.mp hb).2
        linarith
      exact div_le_div_of_nonneg_right hbneg hden
    · filter_upwards [hterminal, hden_nonneg] with β hb hden
      have hle : -terminalLog β ≤ terminalBound := by
        have hle' : -terminalBound ≤ terminalLog β := (abs_le.mp hb).1
        linarith
      exact div_le_div_of_nonneg_right hle hden
  have hterminal_div :
      Filter.Tendsto
        (fun β : ℝ => terminalLog β / Real.log (M.betaC - β))
        L (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hterminal_div_neg
    filter_upwards with β
    ring
  have hsum :
      Filter.Tendsto
        (fun β : ℝ =>
          terminalLog β / Real.log (M.betaC - β) +
            accumulatedError β / Real.log (M.betaC - β))
        L (nhds (0 + 0)) := by
    simpa [L] using hterminal_div.add herror
  have hzero :
      Filter.Tendsto
        (fun β : ℝ =>
          terminalLog β / Real.log (M.betaC - β) +
            accumulatedError β / Real.log (M.betaC - β))
        L (nhds 0) := by
    simpa using hsum
  refine Filter.Tendsto.congr' ?_ hzero
  filter_upwards with β
  ring

set_option linter.style.longLine false in


theorem tendsto_error_div_neg_log_betaC_sub_iff_log_betaC_sub
    {ι : Type*} (M : CriticalModel ι) (accumulatedError : ℝ → ℝ) :
    Filter.Tendsto
        (fun β : ℝ => accumulatedError β / (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) ↔
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  constructor
  · intro hneglog
    have hneg :
        Filter.Tendsto
          (fun β : ℝ =>
            -(accumulatedError β / (-Real.log (M.betaC - β))))
          (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds (-0)) :=
      hneglog.neg
    refine Filter.Tendsto.congr' ?_ (by simpa using hneg)
    filter_upwards with β
    ring
  · intro hlog
    have hneg :
        Filter.Tendsto
          (fun β : ℝ =>
            -(accumulatedError β / Real.log (M.betaC - β)))
          (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds (-0)) :=
      hlog.neg
    refine Filter.Tendsto.congr' ?_ (by simpa using hneg)
    filter_upwards with β
    ring

set_option linter.style.longLine false in






theorem tendsto_error_div_clock_of_log_betaC_sub
    {ι : Type*} (M : CriticalModel ι) (clock accumulatedError : ℝ → ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue)
    (hclock_compare :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
            (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (herror :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / clock β)
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hclock_ratio :
      Filter.Tendsto
        (fun β : ℝ => clock β / (-Real.log (M.betaC - β)))
        L (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
    simpa [L] using
      (tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock
        M clock heigen hclock_compare)
  have hlogEigen_ne : Real.log relevantEigenvalue ≠ 0 :=
    (Real.log_pos heigen).ne'
  have hclock_ratio_inv :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β / (-Real.log (M.betaC - β)))⁻¹)
        L (nhds (((Real.log relevantEigenvalue)⁻¹)⁻¹)) := by
    exact hclock_ratio.inv₀ (inv_ne_zero hlogEigen_ne)
  have hclock_pos : ∀ᶠ β in L, 0 < clock β := by
    simpa [L] using
      eventually_pos_of_sublinear_criticalDistanceScaleClock
        M clock heigen hclock_compare
  have hneglog :
      Filter.Tendsto (fun β : ℝ => -Real.log (M.betaC - β))
        L Filter.atTop := by
    change
      Filter.Tendsto (fun β : ℝ => -(Real.log (M.betaC - β)))
        L Filter.atTop
    exact
      ((Filter.tendsto_neg_atBot_atTop :
        Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop).comp
          (by simpa [L] using tendsto_log_betaC_sub_atBot M))
  have hden_pos : ∀ᶠ β in L, 0 < -Real.log (M.betaC - β) := by
    exact hneglog.eventually_ge_atTop 1 |>.mono (by intro β hβ; linarith)
  have hlog_div_clock :
      Filter.Tendsto
        (fun β : ℝ => Real.log (M.betaC - β) / clock β)
        L (nhds (-(Real.log relevantEigenvalue))) := by
    have hneglog_div_clock :
        Filter.Tendsto
          (fun β : ℝ =>
            (-Real.log (M.betaC - β)) / clock β)
          L (nhds (Real.log relevantEigenvalue)) := by
      have hlimit :
          (((Real.log relevantEigenvalue)⁻¹)⁻¹) =
            Real.log relevantEigenvalue := by
        field_simp [hlogEigen_ne]
      refine Filter.Tendsto.congr' ?_ (by simpa [hlimit] using hclock_ratio_inv)
      filter_upwards [hclock_pos, hden_pos] with β hclockβ hdenβ
      have hclock_ne : clock β ≠ 0 := hclockβ.ne'
      have hden_ne : -Real.log (M.betaC - β) ≠ 0 := hdenβ.ne'
      field_simp [hclock_ne, hden_ne]
    have hneg :
        Filter.Tendsto
          (fun β : ℝ =>
            -((-Real.log (M.betaC - β)) / clock β))
          L (nhds (-(Real.log relevantEigenvalue))) := by
      simpa using hneglog_div_clock.neg
    refine Filter.Tendsto.congr' ?_ hneg
    filter_upwards [hclock_pos] with β hclockβ
    have hclock_ne : clock β ≠ 0 := hclockβ.ne'
    field_simp [hclock_ne]
  have hprod :
      Filter.Tendsto
        (fun β : ℝ =>
          (accumulatedError β / Real.log (M.betaC - β)) *
            (Real.log (M.betaC - β) / clock β))
        L (nhds (0 * (-(Real.log relevantEigenvalue)))) := by
    simpa [L] using herror.mul hlog_div_clock
  have hprod_zero :
      Filter.Tendsto
        (fun β : ℝ =>
          (accumulatedError β / Real.log (M.betaC - β)) *
            (Real.log (M.betaC - β) / clock β))
        L (nhds 0) := by
    simpa using hprod
  refine Filter.Tendsto.congr' ?_ hprod_zero
  filter_upwards [hclock_pos, hden_pos] with β hclockβ hdenβ
  have hclock_ne : clock β ≠ 0 := hclockβ.ne'
  have hlog_ne : Real.log (M.betaC - β) ≠ 0 := by
    intro hlog
    rw [hlog] at hdenβ
    norm_num at hdenβ
  field_simp [hclock_ne, hlog_ne]

set_option linter.style.longLine false in


theorem tendsto_error_div_clock_of_log_betaC_sub_of_annulus
    {ι : Type*} (M : CriticalModel ι) (clock accumulatedError : ℝ → ℝ)
    (relevantEigenvalue cLo cHi : ℝ)
    (heigen : 1 < relevantEigenvalue) (hcLo : 0 < cLo)
    (hcHi : 0 < cHi)
    (hannulus :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ∧
          Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ≤ cHi)
    (herror :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / clock β)
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  exact
    tendsto_error_div_clock_of_log_betaC_sub
      M clock accumulatedError heigen
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        M clock relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus)
      herror

set_option linter.style.longLine false in






theorem tendsto_error_div_log_betaC_sub_of_clock_average
    {ι : Type*} (M : CriticalModel ι) (clock accumulatedError : ℝ → ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue)
    (hclock_compare :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
            (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (haverage :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / clock β)
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hclock_ratio :
      Filter.Tendsto
        (fun β : ℝ => clock β / (-Real.log (M.betaC - β)))
        L (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
    simpa [L] using
      (tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock
        M clock heigen hclock_compare)
  have hclock_pos : ∀ᶠ β in L, 0 < clock β := by
    simpa [L] using
      eventually_pos_of_sublinear_criticalDistanceScaleClock
        M clock heigen hclock_compare
  have hprod :
      Filter.Tendsto
        (fun β : ℝ =>
          (accumulatedError β / clock β) *
            (clock β / (-Real.log (M.betaC - β))))
        L (nhds (0 * (Real.log relevantEigenvalue)⁻¹)) := by
    simpa [L] using haverage.mul hclock_ratio
  have hprod_zero :
      Filter.Tendsto
        (fun β : ℝ =>
          (accumulatedError β / clock β) *
            (clock β / (-Real.log (M.betaC - β))))
        L (nhds 0) := by
    simpa using hprod
  have hneglog :
      Filter.Tendsto (fun β : ℝ => -Real.log (M.betaC - β))
        L Filter.atTop := by
    change
      Filter.Tendsto (fun β : ℝ => -(Real.log (M.betaC - β)))
        L Filter.atTop
    exact
      ((Filter.tendsto_neg_atBot_atTop :
        Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop).comp
          (by simpa [L] using tendsto_log_betaC_sub_atBot M))
  have hden_pos : ∀ᶠ β in L, 0 < -Real.log (M.betaC - β) := by
    exact hneglog.eventually_ge_atTop 1 |>.mono (by intro β hβ; linarith)
  have hneg_error_div :
      Filter.Tendsto
        (fun β : ℝ => -(accumulatedError β / Real.log (M.betaC - β)))
        L (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hprod_zero
    filter_upwards [hclock_pos, hden_pos] with β hclockβ hdenβ
    have hclock_ne : clock β ≠ 0 := hclockβ.ne'
    have hden_ne : -Real.log (M.betaC - β) ≠ 0 := hdenβ.ne'
    field_simp [hclock_ne, hden_ne]
  have hneg_neg :
      Filter.Tendsto
        (fun β : ℝ => - (-(accumulatedError β / Real.log (M.betaC - β))))
        L (nhds (-0)) := hneg_error_div.neg
  simpa using hneg_neg

set_option linter.style.longLine false in


theorem tendsto_error_div_log_betaC_sub_of_annulus_clock_average
    {ι : Type*} (M : CriticalModel ι) (clock accumulatedError : ℝ → ℝ)
    (relevantEigenvalue cLo cHi : ℝ)
    (heigen : 1 < relevantEigenvalue) (hcLo : 0 < cLo)
    (hcHi : 0 < cHi)
    (hannulus :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ∧
          Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ≤ cHi)
    (haverage :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / clock β)
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  exact
    tendsto_error_div_log_betaC_sub_of_clock_average
      M clock accumulatedError heigen
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        M clock relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus)
      haverage

set_option linter.style.longLine false in


theorem tendsto_error_div_clock_iff_log_betaC_sub
    {ι : Type*} (M : CriticalModel ι) (clock accumulatedError : ℝ → ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue)
    (hclock_compare :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
            (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
        (fun β : ℝ => accumulatedError β / clock β)
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) ↔
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  constructor
  · exact
      tendsto_error_div_log_betaC_sub_of_clock_average
        M clock accumulatedError heigen hclock_compare
  · exact
      tendsto_error_div_clock_of_log_betaC_sub
        M clock accumulatedError heigen hclock_compare

set_option linter.style.longLine false in


theorem tendsto_error_div_clock_iff_log_betaC_sub_of_annulus
    {ι : Type*} (M : CriticalModel ι) (clock accumulatedError : ℝ → ℝ)
    (relevantEigenvalue cLo cHi : ℝ)
    (heigen : 1 < relevantEigenvalue) (hcLo : 0 < cLo)
    (hcHi : 0 < cHi)
    (hannulus :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ∧
          Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ≤ cHi) :
    Filter.Tendsto
        (fun β : ℝ => accumulatedError β / clock β)
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) ↔
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  exact
    tendsto_error_div_clock_iff_log_betaC_sub
      M clock accumulatedError heigen
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        M clock relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus)

set_option linter.style.longLine false in







theorem tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_clock_average
    {ι : Type*} (M : CriticalModel ι)
    (clock terminalLog accumulatedError : ℝ → ℝ) (terminalBound : ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue)
    (hclock_compare :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
            (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hterminal :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        |terminalLog β| ≤ terminalBound)
    (haverage :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / clock β)
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ =>
        (terminalLog β + accumulatedError β) /
          Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  exact
    tendsto_bounded_terminal_add_error_div_log_betaC_sub
      M terminalLog accumulatedError terminalBound hterminal
      (tendsto_error_div_log_betaC_sub_of_clock_average
        M clock accumulatedError heigen hclock_compare haverage)

set_option linter.style.longLine false in


theorem tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average
    {ι : Type*} (M : CriticalModel ι)
    (clock terminalLog accumulatedError : ℝ → ℝ) (terminalBound : ℝ)
    (relevantEigenvalue cLo cHi : ℝ)
    (heigen : 1 < relevantEigenvalue) (hcLo : 0 < cLo)
    (hcHi : 0 < cHi)
    (hannulus :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ∧
          Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ≤ cHi)
    (hterminal :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        |terminalLog β| ≤ terminalBound)
    (haverage :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / clock β)
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ =>
        (terminalLog β + accumulatedError β) /
          Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  exact
    tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_clock_average
      M clock terminalLog accumulatedError terminalBound heigen
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        M clock relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus)
      hterminal haverage

set_option linter.style.longLine false in


theorem tendsto_terminal_add_error_div_log_betaC_sub_of_clock_average
    {ι : Type*} (M : CriticalModel ι)
    (clock terminalLog accumulatedError : ℝ → ℝ) (terminalLimit : ℝ)
    {relevantEigenvalue : ℝ} (heigen : 1 < relevantEigenvalue)
    (hclock_compare :
      Filter.Tendsto
        (fun β : ℝ =>
          (clock β - criticalDistanceScaleClock M relevantEigenvalue β) /
            (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hterminal :
      Filter.Tendsto terminalLog
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds terminalLimit))
    (haverage :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / clock β)
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ =>
        (terminalLog β + accumulatedError β) /
          Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  exact
    tendsto_terminal_add_error_div_log_betaC_sub
      M terminalLog accumulatedError terminalLimit hterminal
      (tendsto_error_div_log_betaC_sub_of_clock_average
        M clock accumulatedError heigen hclock_compare haverage)

set_option linter.style.longLine false in


theorem tendsto_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average
    {ι : Type*} (M : CriticalModel ι)
    (clock terminalLog accumulatedError : ℝ → ℝ) (terminalLimit : ℝ)
    (relevantEigenvalue cLo cHi : ℝ)
    (heigen : 1 < relevantEigenvalue) (hcLo : 0 < cLo)
    (hcHi : 0 < cHi)
    (hannulus :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ∧
          Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ≤ cHi)
    (hterminal :
      Filter.Tendsto terminalLog
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds terminalLimit))
    (haverage :
      Filter.Tendsto
        (fun β : ℝ => accumulatedError β / clock β)
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
    Filter.Tendsto
      (fun β : ℝ =>
        (terminalLog β + accumulatedError β) /
          Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
  exact
    tendsto_terminal_add_error_div_log_betaC_sub_of_clock_average
      M clock terminalLog accumulatedError terminalLimit heigen
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        M clock relevantEigenvalue cLo cHi heigen hcLo hcHi hannulus)
      hterminal haverage

set_option linter.style.longLine false in





theorem tendsto_log_mass_div_log_betaC_sub_of_scaleClock {ι : Type*}
    (M : CriticalModel ι) (mass clock logError : ℝ → ℝ)
    (scaleBase relevantEigenvalue : ℝ)
    (hclock :
      Filter.Tendsto
        (fun β : ℝ =>
          clock β / (-Real.log (M.betaC - β)))
        (nhdsWithin M.betaC (Set.Iio M.betaC))
        (nhds ((Real.log relevantEigenvalue)⁻¹)))
    (herror :
      Filter.Tendsto
        (fun β : ℝ => logError β / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hlog :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        Real.log (mass β) =
          -(Real.log scaleBase) * clock β + logError β) :
    Filter.Tendsto
      (fun β : ℝ => Real.log (mass β) / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC))
      (nhds (Real.log scaleBase / Real.log relevantEigenvalue)) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  have hlimit :
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log scaleBase *
              (clock β / (-Real.log (M.betaC - β))) +
            logError β / Real.log (M.betaC - β))
        L
        (nhds
          (Real.log scaleBase * (Real.log relevantEigenvalue)⁻¹ + 0)) := by
    simpa [L] using
      ((hclock.const_mul (Real.log scaleBase)).add herror)
  have hlimit' :
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log scaleBase *
              (clock β / (-Real.log (M.betaC - β))) +
            logError β / Real.log (M.betaC - β))
        L
        (nhds (Real.log scaleBase / Real.log relevantEigenvalue)) := by
    simpa [div_eq_mul_inv] using hlimit
  refine Filter.Tendsto.congr' ?_ hlimit'
  filter_upwards [hlog] with β hlogβ
  rw [hlogβ]
  ring

end Exact3D
end StatMech
