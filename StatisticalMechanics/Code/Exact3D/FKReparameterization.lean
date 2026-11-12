/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Reparameterization
import Code.IsingFK.Q2
















namespace StatMech
namespace Exact3D




noncomputable def ParameterModel (c : ℝ) : CriticalModel Unit where
  betaC := c
  twoPoint := fun _ _ _ => 0

namespace FKReparameterization


theorem pOfBeta_strictMono : StrictMono IsingFK.pOfBeta := by
  intro a b hab
  unfold IsingFK.pOfBeta
  have h_exp : Real.exp (-2 * b) < Real.exp (-2 * a) := by
    rw [Real.exp_lt_exp]
    linarith
  linarith


theorem hasDerivAt_pOfBeta (β : ℝ) :
    HasDerivAt IsingFK.pOfBeta (2 * Real.exp (-2 * β)) β := by
  unfold IsingFK.pOfBeta
  have hlin : HasDerivAt (fun x : ℝ => -2 * x) (-2) β := by
    simpa using (hasDerivAt_id β).const_mul (-2)
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-2 * x))
        (Real.exp (-2 * β) * (-2)) β := by
    simpa using hlin.exp
  have hone : HasDerivAt (fun _x : ℝ => (1 : ℝ)) 0 β :=
    hasDerivAt_const β 1
  have hsub := hone.sub hexp
  convert hsub using 1
  ring



noncomputable def pOfBetaDistancePrefactor (βc β : ℝ) : ℝ :=
  (IsingFK.pOfBeta βc - IsingFK.pOfBeta β) / (βc - β)


theorem pOfBetaDistancePrefactor_eq_slope {βc β : ℝ} (hβ : β ≠ βc) :
    pOfBetaDistancePrefactor βc β = slope IsingFK.pOfBeta βc β := by
  unfold pOfBetaDistancePrefactor
  rw [slope_def_field]
  have hden : β - βc ≠ 0 := sub_ne_zero.mpr hβ
  field_simp [hden]
  ring



theorem pOfBetaDistancePrefactor_pos_of_lt {βc β : ℝ} (hβ : β < βc) :
    0 < pOfBetaDistancePrefactor βc β := by
  unfold pOfBetaDistancePrefactor
  exact div_pos (sub_pos.mpr (pOfBeta_strictMono hβ)) (sub_pos.mpr hβ)



theorem pOfBeta_criticalDistance_eq_prefactor_mul
    {βc β : ℝ} (hβ : β ≠ βc) :
    IsingFK.pOfBeta βc - IsingFK.pOfBeta β =
      pOfBetaDistancePrefactor βc β * (βc - β) := by
  unfold pOfBetaDistancePrefactor
  have hden : βc - β ≠ 0 := sub_ne_zero.mpr hβ.symm
  field_simp [hden]



theorem tendsto_pOfBetaDistancePrefactor_left (βc : ℝ) :
    Filter.Tendsto (pOfBetaDistancePrefactor βc)
      (nhdsWithin βc (Set.Iio βc)) (nhds (2 * Real.exp (-2 * βc))) := by
  have hslope :
      Filter.Tendsto (slope IsingFK.pOfBeta βc)
        (nhdsWithin βc (Set.Iio βc)) (nhds (2 * Real.exp (-2 * βc))) := by
    exact (hasDerivAt_pOfBeta βc).tendsto_slope.mono_left
      (nhdsWithin_mono βc (fun β hβ => ne_of_lt hβ))
  refine Filter.Tendsto.congr' ?_ hslope
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact (pOfBetaDistancePrefactor_eq_slope (ne_of_lt hβ)).symm



theorem tendsto_log_pOfBetaDistancePrefactor_div_log_left (βc : ℝ) :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (pOfBetaDistancePrefactor βc β) / Real.log (βc - β))
      (nhdsWithin βc (Set.Iio βc)) (nhds 0) := by
  let a : ℝ := 2 * Real.exp (-2 * βc)
  have ha : 0 < a := by
    positivity
  have hpref :
      Filter.Tendsto (pOfBetaDistancePrefactor βc)
        (nhdsWithin βc (Set.Iio βc)) (nhds a) := by
    simpa [a] using tendsto_pOfBetaDistancePrefactor_left βc
  have hlogpref :
      Filter.Tendsto (fun β : ℝ => Real.log (pOfBetaDistancePrefactor βc β))
        (nhdsWithin βc (Set.Iio βc)) (nhds (Real.log a)) :=
    (Real.continuousAt_log ha.ne').tendsto.comp hpref
  have hlogd :
      Filter.Tendsto (fun β : ℝ => Real.log (βc - β))
        (nhdsWithin βc (Set.Iio βc)) Filter.atBot := by
    simpa [ParameterModel] using
      tendsto_log_betaC_sub_atBot (ParameterModel βc)
  exact hlogpref.div_atBot hlogd

set_option linter.style.longLine false in


theorem eventually_pOfBetaDistancePrefactor_mem_Ioo_left (βc : ℝ) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
      pOfBetaDistancePrefactor βc β ∈
        Set.Ioo (Real.exp (-2 * βc)) (3 * Real.exp (-2 * βc)) := by
  let a : ℝ := 2 * Real.exp (-2 * βc)
  have h_exp_pos : 0 < Real.exp (-2 * βc) := Real.exp_pos _
  have hleft : Real.exp (-2 * βc) < a := by
    dsimp [a]
    linarith
  have hright : a < 3 * Real.exp (-2 * βc) := by
    dsimp [a]
    linarith
  have hmem :
      a ∈ Set.Ioo (Real.exp (-2 * βc)) (3 * Real.exp (-2 * βc)) :=
    ⟨hleft, hright⟩
  have hopen :
      IsOpen (Set.Ioo (Real.exp (-2 * βc)) (3 * Real.exp (-2 * βc))) :=
    isOpen_Ioo
  exact (tendsto_pOfBetaDistancePrefactor_left βc).eventually
    (hopen.mem_nhds hmem)

set_option linter.style.longLine false in



theorem eventually_pOfBeta_criticalDistance_comparable_left (βc : ℝ) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
      Real.exp (-2 * βc) * (βc - β) ≤
          IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧
        IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤
          (3 * Real.exp (-2 * βc)) * (βc - β) := by
  filter_upwards
    [eventually_pOfBetaDistancePrefactor_mem_Ioo_left βc,
      self_mem_nhdsWithin] with β hpref hβ
  have hdist :=
    pOfBeta_criticalDistance_eq_prefactor_mul (βc := βc) (β := β)
      (ne_of_lt hβ)
  have hdiff_nonneg : 0 ≤ βc - β := le_of_lt (sub_pos.mpr hβ)
  constructor
  · rw [hdist]
    exact mul_le_mul_of_nonneg_right (le_of_lt hpref.1) hdiff_nonneg
  · rw [hdist]
    exact mul_le_mul_of_nonneg_right (le_of_lt hpref.2) hdiff_nonneg

set_option linter.style.longLine false in


theorem exists_Ioo_subset_of_eventually_left {βc : ℝ} {P : ℝ → Prop}
    (hP : ∀ᶠ β in nhdsWithin βc (Set.Iio βc), P β) :
    ∃ δ, 0 < δ ∧ ∀ β, β ∈ Set.Ioo (βc - δ) βc → P β := by
  rw [eventually_nhdsWithin_iff] at hP
  rw [Metric.eventually_nhds_iff] at hP
  obtain ⟨ε, hε, hPε⟩ := hP
  refine ⟨ε / 2, by positivity, ?_⟩
  intro β hβ
  have hdist : dist β βc < ε := by
    rw [Real.dist_eq]
    have hle : β - βc ≤ 0 := sub_nonpos.mpr (le_of_lt hβ.2)
    have habs : |β - βc| = βc - β := by
      rw [abs_of_nonpos hle]
      ring
    rw [habs]
    linarith [hβ.1]
  exact hPε hdist hβ.2

set_option linter.style.longLine false in


theorem exists_pOfBeta_criticalDistance_comparable_Ioo_left (βc : ℝ) :
    ∃ δ, 0 < δ ∧
      ∀ β, β ∈ Set.Ioo (βc - δ) βc →
        Real.exp (-2 * βc) * (βc - β) ≤
            IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧
          IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤
            (3 * Real.exp (-2 * βc)) * (βc - β) :=
  exists_Ioo_subset_of_eventually_left
    (eventually_pOfBeta_criticalDistance_comparable_left βc)

set_option linter.style.longLine false in


noncomputable def pOfBetaCriticalDistanceComparableWindow (βc : ℝ) : ℝ :=
  Classical.choose (exists_pOfBeta_criticalDistance_comparable_Ioo_left βc)

theorem pOfBetaCriticalDistanceComparableWindow_pos (βc : ℝ) :
    0 < pOfBetaCriticalDistanceComparableWindow βc := by
  exact (Classical.choose_spec
    (exists_pOfBeta_criticalDistance_comparable_Ioo_left βc)).1

set_option linter.style.longLine false in


theorem pOfBeta_criticalDistance_comparable_of_mem_Ioo_left
    {βc β : ℝ}
    (hβ :
      β ∈ Set.Ioo
        (βc - pOfBetaCriticalDistanceComparableWindow βc) βc) :
    Real.exp (-2 * βc) * (βc - β) ≤
        IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧
      IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤
        (3 * Real.exp (-2 * βc)) * (βc - β) := by
  exact (Classical.choose_spec
    (exists_pOfBeta_criticalDistance_comparable_Ioo_left βc)).2 β hβ

set_option linter.style.longLine false in




theorem exp_log_lower_power_transfer_of_mul_le
    {lo d p k δ : ℝ}
    (hlo : 0 < lo) (hd : 0 < d) (hdlt : d < 1)
    (hk : 0 ≤ k) (hδ : 0 ≤ δ) (hcomp : lo * d ≤ p) :
    Real.exp (k * Real.log lo) *
        Real.exp ((k + δ) * Real.log d) ≤
      Real.exp (k * Real.log p) := by
  rw [← Real.exp_add]
  rw [Real.exp_le_exp]
  have hlogcomp : Real.log (lo * d) ≤ Real.log p :=
    Real.log_le_log (mul_pos hlo hd) hcomp
  have hlogmul : Real.log (lo * d) = Real.log lo + Real.log d := by
    rw [Real.log_mul hlo.ne' hd.ne']
  have hlogcomp' : Real.log lo + Real.log d ≤ Real.log p := by
    simpa [hlogmul] using hlogcomp
  have hmul : k * (Real.log lo + Real.log d) ≤ k * Real.log p :=
    mul_le_mul_of_nonneg_left hlogcomp' hk
  have hlogd_nonpos : Real.log d ≤ 0 :=
    Real.log_nonpos hd.le hdlt.le
  have hdelta : δ * Real.log d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hδ hlogd_nonpos
  calc
    k * Real.log lo + (k + δ) * Real.log d =
        k * (Real.log lo + Real.log d) + δ * Real.log d := by ring
    _ ≤ k * Real.log p + 0 := add_le_add hmul hdelta
    _ = k * Real.log p := by ring

set_option linter.style.longLine false in


theorem exp_log_lower_power_transfer_no_slack_of_mul_le
    {lo d p k : ℝ}
    (hlo : 0 < lo) (hd : 0 < d)
    (hk : 0 ≤ k) (hcomp : lo * d ≤ p) :
    Real.exp (k * Real.log lo) *
        Real.exp (k * Real.log d) ≤
      Real.exp (k * Real.log p) := by
  rw [← Real.exp_add]
  rw [Real.exp_le_exp]
  have hlogcomp : Real.log (lo * d) ≤ Real.log p :=
    Real.log_le_log (mul_pos hlo hd) hcomp
  have hlogmul : Real.log (lo * d) = Real.log lo + Real.log d := by
    rw [Real.log_mul hlo.ne' hd.ne']
  have hlogcomp' : Real.log lo + Real.log d ≤ Real.log p := by
    simpa [hlogmul] using hlogcomp
  calc
    k * Real.log lo + k * Real.log d =
        k * (Real.log lo + Real.log d) := by ring
    _ ≤ k * Real.log p := mul_le_mul_of_nonneg_left hlogcomp' hk

set_option linter.style.longLine false in

theorem exp_log_power_slack_le_of_lt_one
    {d k δ : ℝ} (hd : 0 < d) (hdlt : d < 1) (hδ : 0 ≤ δ) :
    Real.exp ((k + δ) * Real.log d) ≤
      Real.exp (k * Real.log d) := by
  rw [Real.exp_le_exp]
  have hlogd_nonpos : Real.log d ≤ 0 :=
    Real.log_nonpos hd.le hdlt.le
  have hdelta : δ * Real.log d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hδ hlogd_nonpos
  calc
    (k + δ) * Real.log d =
        k * Real.log d + δ * Real.log d := by ring
    _ ≤ k * Real.log d + 0 := add_le_add le_rfl hdelta
    _ = k * Real.log d := by ring

set_option linter.style.longLine false in


noncomputable def expLogUpperComparisonPrefactor
    (lo hi k : ℝ) : ℝ :=
  if 0 ≤ k then
    Real.exp (k * Real.log hi)
  else
    Real.exp (k * Real.log lo)

theorem expLogUpperComparisonPrefactor_pos
    (lo hi k : ℝ) :
    0 < expLogUpperComparisonPrefactor lo hi k := by
  by_cases hk : 0 ≤ k
  · simpa [expLogUpperComparisonPrefactor, hk] using
      Real.exp_pos (k * Real.log hi)
  · simpa [expLogUpperComparisonPrefactor, hk] using
      Real.exp_pos (k * Real.log lo)

set_option linter.style.longLine false in


theorem exp_log_upper_power_transfer_of_comparable
    {lo hi d p k : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) (hd : 0 < d)
    (hlo_comp : lo * d ≤ p) (hhi_comp : p ≤ hi * d) :
    Real.exp (k * Real.log p) ≤
      expLogUpperComparisonPrefactor lo hi k *
        Real.exp (k * Real.log d) := by
  by_cases hk : 0 ≤ k
  · have hp : 0 < p := lt_of_lt_of_le (mul_pos hlo hd) hlo_comp
    have hbase :
        Real.exp (k * Real.log p) ≤
          Real.exp (k * Real.log hi) *
            Real.exp (k * Real.log d) := by
      rw [← Real.exp_add]
      rw [Real.exp_le_exp]
      have hlogcomp : Real.log p ≤ Real.log (hi * d) :=
        Real.log_le_log hp hhi_comp
      have hlogmul : Real.log (hi * d) = Real.log hi + Real.log d := by
        rw [Real.log_mul hhi.ne' hd.ne']
      have hlogcomp' : Real.log p ≤ Real.log hi + Real.log d := by
        simpa [hlogmul] using hlogcomp
      calc
        k * Real.log p ≤ k * (Real.log hi + Real.log d) :=
          mul_le_mul_of_nonneg_left hlogcomp' hk
        _ = k * Real.log hi + k * Real.log d := by ring
    simpa [expLogUpperComparisonPrefactor, hk] using hbase
  · have hk_le : k ≤ 0 := le_of_not_ge hk
    have hbase :
        Real.exp (k * Real.log p) ≤
          Real.exp (k * Real.log lo) *
            Real.exp (k * Real.log d) := by
      rw [← Real.exp_add]
      rw [Real.exp_le_exp]
      have hlogcomp : Real.log (lo * d) ≤ Real.log p :=
        Real.log_le_log (mul_pos hlo hd) hlo_comp
      have hlogmul : Real.log (lo * d) = Real.log lo + Real.log d := by
        rw [Real.log_mul hlo.ne' hd.ne']
      have hlogcomp' : Real.log lo + Real.log d ≤ Real.log p := by
        simpa [hlogmul] using hlogcomp
      calc
        k * Real.log p ≤ k * (Real.log lo + Real.log d) :=
          mul_le_mul_of_nonpos_left hlogcomp' hk_le
        _ = k * Real.log lo + k * Real.log d := by ring
    simpa [expLogUpperComparisonPrefactor, hk] using hbase



theorem pOfBeta_leftCriticalReparam (βc : ℝ) :
    LeftCriticalReparam (ParameterModel βc)
      (ParameterModel (IsingFK.pOfBeta βc)) IsingFK.pOfBeta where
  tendsto_left := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : ContinuousAt IsingFK.pOfBeta βc := by
        unfold IsingFK.pOfBeta
        fun_prop
      simpa [ParameterModel] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      simpa [ParameterModel] using pOfBeta_strictMono hβ
  log_distance_ratio := by
    let L := nhdsWithin βc (Set.Iio βc)
    have hlogpref :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (pOfBetaDistancePrefactor βc β) / Real.log (βc - β))
          L (nhds 0) := by
      simpa [L] using tendsto_log_pOfBetaDistancePrefactor_div_log_left βc
    have hlim :
        Filter.Tendsto
          (fun β : ℝ =>
            1 + Real.log (pOfBetaDistancePrefactor βc β) /
              Real.log (βc - β))
          L (nhds (1 + 0)) :=
      tendsto_const_nhds.add hlogpref
    refine Filter.Tendsto.congr' ?_ (by simpa using hlim)
    filter_upwards
      [self_mem_nhdsWithin,
        Ioo_mem_nhdsLT (show βc - 1 < βc by linarith)] with β hβ hβnear
    have hdiff_pos : 0 < βc - β := sub_pos.mpr hβ
    have hdiff_ne : βc - β ≠ 0 := hdiff_pos.ne'
    have hpref_pos : 0 < pOfBetaDistancePrefactor βc β := by
      unfold pOfBetaDistancePrefactor
      exact div_pos (sub_pos.mpr (pOfBeta_strictMono hβ)) hdiff_pos
    have hpref_ne : pOfBetaDistancePrefactor βc β ≠ 0 := hpref_pos.ne'
    have hdiff_lt_one : βc - β < 1 := by
      linarith [hβnear.1]
    have hlogd_ne : Real.log (βc - β) ≠ 0 :=
      (Real.log_neg hdiff_pos hdiff_lt_one).ne
    have hdist :
        IsingFK.pOfBeta βc - IsingFK.pOfBeta β =
          pOfBetaDistancePrefactor βc β * (βc - β) := by
      unfold pOfBetaDistancePrefactor
      field_simp [hdiff_ne]
    rw [show (ParameterModel (IsingFK.pOfBeta βc)).betaC - IsingFK.pOfBeta β =
        IsingFK.pOfBeta βc - IsingFK.pOfBeta β by rfl]
    rw [show (ParameterModel βc).betaC - β = βc - β by rfl]
    rw [hdist, Real.log_mul hpref_ne hdiff_ne]
    field_simp [hlogd_ne]
    ring

set_option linter.style.longLine false in



theorem eventually_pOfBeta_mem_Ioo_left {βc pδ : ℝ} (hpδ : 0 < pδ) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
      IsingFK.pOfBeta β ∈
        Set.Ioo (IsingFK.pOfBeta βc - pδ) (IsingFK.pOfBeta βc) := by
  have hpIoo :
      Set.Ioo (IsingFK.pOfBeta βc - pδ) (IsingFK.pOfBeta βc) ∈
        nhdsWithin (IsingFK.pOfBeta βc) (Set.Iio (IsingFK.pOfBeta βc)) :=
    Ioo_mem_nhdsLT (show IsingFK.pOfBeta βc - pδ < IsingFK.pOfBeta βc by
      linarith)
  exact (pOfBeta_leftCriticalReparam βc).tendsto_left.eventually hpIoo

set_option linter.style.longLine false in

theorem exists_pOfBeta_mem_Ioo_left {βc pδ : ℝ} (hpδ : 0 < pδ) :
    ∃ δ, 0 < δ ∧
      ∀ β, β ∈ Set.Ioo (βc - δ) βc →
        IsingFK.pOfBeta β ∈
          Set.Ioo (IsingFK.pOfBeta βc - pδ) (IsingFK.pOfBeta βc) :=
  exists_Ioo_subset_of_eventually_left
    (eventually_pOfBeta_mem_Ioo_left (βc := βc) hpδ)

set_option linter.style.longLine false in



noncomputable def pOfBetaLeftPullbackWindow
    (βc : ℝ) (pWindow : ℝ → ℝ)
    (pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then
    Classical.choose
      (exists_pOfBeta_mem_Ioo_left (βc := βc) (pδ := pWindow ε)
        (pWindow_pos ε hε))
  else
    1

set_option linter.style.longLine false in

theorem pOfBetaLeftPullbackWindow_pos
    (βc : ℝ) (pWindow : ℝ → ℝ)
    (pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε)
    {ε : ℝ} (hε : 0 < ε) :
    0 < pOfBetaLeftPullbackWindow βc pWindow pWindow_pos ε := by
  have hspec :=
    Classical.choose_spec
      (exists_pOfBeta_mem_Ioo_left (βc := βc) (pδ := pWindow ε)
        (pWindow_pos ε hε))
  simpa [pOfBetaLeftPullbackWindow, hε] using hspec.1

set_option linter.style.longLine false in

theorem pOfBeta_mem_Ioo_of_mem_leftPullbackWindow
    (βc : ℝ) (pWindow : ℝ → ℝ)
    (pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε)
    {ε β : ℝ} (hε : 0 < ε)
    (hβ :
      β ∈ Set.Ioo
        (βc - pOfBetaLeftPullbackWindow βc pWindow pWindow_pos ε) βc) :
    IsingFK.pOfBeta β ∈
      Set.Ioo (IsingFK.pOfBeta βc - pWindow ε) (IsingFK.pOfBeta βc) := by
  have hspec :=
    Classical.choose_spec
      (exists_pOfBeta_mem_Ioo_left (βc := βc) (pδ := pWindow ε)
        (pWindow_pos ε hε))
  have hmap := hspec.2 β
  have hβ' :
      β ∈ Set.Ioo
        (βc -
          Classical.choose
            (exists_pOfBeta_mem_Ioo_left (βc := βc) (pδ := pWindow ε)
              (pWindow_pos ε hε))) βc := by
    simpa [pOfBetaLeftPullbackWindow, hε] using hβ
  exact hmap hβ'



theorem hasCriticalNu_comp_pOfBeta {correlationLength : ℝ → ℝ} {βc ν : ℝ}
    (hν :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc))
        correlationLength ν) :
    HasCriticalNu (ParameterModel βc)
      (fun β => correlationLength (IsingFK.pOfBeta β)) ν :=
  hν.comp_leftCriticalReparam (pOfBeta_leftCriticalReparam βc)



theorem eventually_comp_pOfBeta_left {βc : ℝ} {P : ℝ → Prop}
    (hP :
      ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta βc)
          (Set.Iio (IsingFK.pOfBeta βc)),
        P p) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc), P (IsingFK.pOfBeta β) := by
  simpa [ParameterModel] using
    (pOfBeta_leftCriticalReparam βc).tendsto_left.eventually hP



theorem eventually_eq_comp_pOfBeta_left {βc : ℝ} {f g : ℝ → ℝ}
    (hEq :
      ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta βc)
          (Set.Iio (IsingFK.pOfBeta βc)),
        f p = g p) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
      f (IsingFK.pOfBeta β) = g (IsingFK.pOfBeta β) :=
  eventually_comp_pOfBeta_left hEq



theorem hasCriticalNu_comp_pOfBeta_congr_eventually
    {βc ν : ℝ} {fkCorrelationLength comparisonLength : ℝ → ℝ}
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc))
        fkCorrelationLength ν)
    (hEq :
      ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
        comparisonLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
    HasCriticalNu (ParameterModel βc) comparisonLength ν :=
  (hasCriticalNu_comp_pOfBeta hfk).congr_eventually hEq

end FKReparameterization

end Exact3D
end StatMech
