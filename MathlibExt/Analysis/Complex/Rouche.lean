/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Rouché's theorem for the disc

Proves `Wanted` entry `rouche_closedBall`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Complex.Rouche

private theorem aux_sphere_ne_zero {c : ℂ} {R : ℝ}
    {f g : ℂ → ℂ}
    (hfg : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) :
    (∀ z ∈ Metric.sphere c R, f z ≠ 0) ∧
    (∀ z ∈ Metric.sphere c R, (fun z => f z + g z) z ≠ 0) := by
  constructor
  · intro z hz hfz
    have h := hfg z hz
    rw [hfz, norm_zero] at h
    have hnn := norm_nonneg (g z)
    linarith
  · intro z hz hFz
    have h := hfg z hz
    simp only at hFz
    have hle : ‖f z‖ ≤ ‖f z + g z‖ + ‖g z‖ := by
      calc ‖f z‖ = ‖(f z + g z) - g z‖ := by ring_nf
        _ ≤ ‖f z + g z‖ + ‖g z‖ := norm_sub_le _ _
    rw [hFz, norm_zero, zero_add] at hle
    linarith

private theorem aux_ordfin {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hf0 : ∀ z ∈ Metric.sphere c R, f z ≠ 0) :
    ∀ w ∈ Metric.ball c R, analyticOrderAt f w ≠ ⊤ := by
  intro w hw htop
  have hwin : w ∈ Metric.closedBall c R :=
    Metric.ball_subset_closedBall hw
  have hev : ∀ᶠ z in nhds w, f z = 0 := analyticOrderAt_eq_top.mp htop
  have hpre : IsPreconnected (Metric.closedBall c R) :=
    Metric.isPreconnected_closedBall
  have hmem : w ∈ closure ({z | f z = 0} \ {w}) := by
    rw [mem_closure_iff_frequently]
    have h1 : ∀ᶠ z in nhdsWithin w ({w}ᶜ : Set ℂ), f z = 0 :=
      hev.filter_mono nhdsWithin_le_nhds
    have hself : ∀ᶠ z in nhdsWithin w ({w}ᶜ : Set ℂ), z ∉ ({w} : Set ℂ) :=
      self_mem_nhdsWithin
    have hfreq : ∃ᶠ z in nhdsWithin w ({w}ᶜ : Set ℂ), f z = 0 ∧ z ∉ ({w} : Set ℂ) :=
      Filter.Frequently.and_eventually h1.frequently hself
    have hfreq2 : ∃ᶠ z in nhds w, f z = 0 ∧ z ∉ ({w} : Set ℂ) :=
      Filter.Frequently.filter_mono hfreq nhdsWithin_le_nhds
    exact hfreq2.mono fun z hz => hz
  have heq : Set.EqOn f 0 (Metric.closedBall c R) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hf hpre hwin hmem
  obtain ⟨z0, hz0⟩ : ∃ z0 : ℂ, z0 ∈ Metric.sphere c R := by
    refine ⟨c + R, Metric.mem_sphere.mpr ?_⟩
    simp [dist_eq_norm, Complex.norm_real, abs_of_pos hR]
  have hfz0 : f z0 = 0 := heq (Metric.sphere_subset_closedBall hz0)
  exact hf0 z0 hz0 hfz0

private theorem aux_local {c : ℂ} {R : ℝ}
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hfin : ∀ w ∈ Metric.ball c R, analyticOrderAt f w ≠ ⊤)
    {a : ℂ} (ha : a ∈ Metric.ball c R)
    (hDa : MeromorphicOn.divisor f (Metric.ball c R) a ≠ 0) :
    ∃ m : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a ≠ 0 ∧
      (∀ z, f z = (z - a) ^ m * g z) ∧
      MeromorphicOn.divisor f (Metric.ball c R) a = (m : ℤ) ∧ 1 ≤ m := by
  have hball : MeromorphicOn f (Metric.ball c R) :=
    (hf.mono Metric.ball_subset_closedBall).meromorphicOn
  have hanal : AnalyticAt ℂ f a := hf a (Metric.ball_subset_closedBall ha)
  have hord : analyticOrderAt f a ≠ ⊤ := hfin a ha
  have hps : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => iteratedDeriv n f a / ↑n.factorial)) a :=
    hanal.hasFPowerSeriesAt
  have hp0 : FormalMultilinearSeries.ofScalars ℂ
        (fun n => iteratedDeriv n f a / ↑n.factorial) ≠ 0 := by
    intro hcon
    apply hord
    rw [analyticOrderAt_eq_top]
    exact (HasFPowerSeriesAt.locally_zero_iff hps).mpr hcon
  set m := (FormalMultilinearSeries.ofScalars ℂ
    (fun n => iteratedDeriv n f a / ↑n.factorial)).order with hm_def
  set g := (Function.swap dslope a)^[m] f with hg_def
  have hfactor : ∀ z, f z = (z - a) ^ m * g z := fun z => by
    have h := HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope hps z
    simpa [hg_def, hm_def, smul_eq_mul] using h
  have hgA : AnalyticAt ℂ g a :=
    HasFPowerSeriesAt.analyticAt
      (HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope m hps)
  have hg0 : g a ≠ 0 :=
    HasFPowerSeriesAt.iterate_dslope_fslope_ne_zero hps hp0
  have hord_eq : analyticOrderAt f a = ↑m := by
    have hmul : AnalyticAt ℂ (fun z => (z - a) ^ m) a := by fun_prop
    have hcongr : analyticOrderAt f a =
        analyticOrderAt ((fun z => (z - a) ^ m) * g) a := by
      apply analyticOrderAt_congr
      filter_upwards with z
      exact hfactor z
    have hpow : (fun z => (z - a) ^ m) = ((fun z : ℂ => z - a) ^ m) := rfl
    rw [hcongr, analyticOrderAt_mul hmul hgA, hpow,
      analyticOrderAt_pow (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - a) a) m,
      analyticOrderAt_id_sub_const_self,
      (hgA.analyticOrderAt_eq_zero.mpr hg0)]
    simp
  refine ⟨m, g, hgA, hg0, hfactor, ?_, ?_⟩
  · rw [hball.divisor_apply ha, hanal.meromorphicOrderAt_eq, hord_eq]
    simp
  · by_contra hle
    push Not at hle
    have hm0 : m = 0 := by omega
    rw [hm0] at hord_eq
    rw [hball.divisor_apply ha, hanal.meromorphicOrderAt_eq, hord_eq] at hDa
    simp at hDa

private theorem aux_bridge {c : ℂ} {R : ℝ}
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hfin : ∀ w ∈ Metric.ball c R, analyticOrderAt f w ≠ ⊤)
    {w : ℂ} (hw : w ∈ Metric.ball c R)
    (hD : MeromorphicOn.divisor f (Metric.ball c R) w = 0) :
    f w ≠ 0 := by
  have hball : MeromorphicOn f (Metric.ball c R) :=
    (hf.mono Metric.ball_subset_closedBall).meromorphicOn
  have hanal : AnalyticAt ℂ f w := hf w (Metric.ball_subset_closedBall hw)
  have hmer : MeromorphicAt f w := hanal.meromorphicAt
  rw [hball.divisor_apply hw] at hD
  rcases WithTop.untop₀_eq_zero.mp hD with h0 | htop
  · obtain ⟨g, hgA, hg0, hfg⟩ :=
      (meromorphicOrderAt_eq_int_iff hmer).mp (by exact_mod_cast h0)
    have hfeq : f =ᶠ[nhdsWithin w ({w}ᶜ : Set ℂ)] g := by
      filter_upwards [hfg] with z hz
      simpa using hz
    have hcont : Filter.Tendsto f (nhdsWithin w ({w}ᶜ : Set ℂ)) (nhds (f w)) :=
      (hanal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hcontg : Filter.Tendsto g (nhdsWithin w ({w}ᶜ : Set ℂ)) (nhds (g w)) :=
      (hgA.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hfw : f w = g w := tendsto_nhds_unique hcont (hcontg.congr' hfeq.symm)
    rw [hfw]
    exact hg0
  · exfalso
    apply hfin w hw
    have hbridge := hanal.meromorphicOrderAt_eq
    have hmap : ENat.map Nat.cast (analyticOrderAt f w) = ⊤ := hbridge ▸ htop
    exact (ENat.map_eq_top_iff).mp hmap

private theorem aux_h_at_mem {Z : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hmemBall : ∀ a ∈ Z, a ∈ Metric.ball c R)
    (h1m : ∀ a ∈ Z, 1 ≤ m a)
    (hgA : ∀ a, AnalyticAt ℂ (g a) a)
    (hg0 : ∀ a ∈ Z, g a a ≠ 0)
    (hfac : ∀ a ∈ Z, ∀ z, f z = (z - a) ^ m a * g a z)
    (h : ℂ → ℂ)
    (hdef : ∀ z, h z = (if z ∈ Z then g z z / ∏ b ∈ Z.erase z, (z - b) ^ m b
      else f z / ∏ a ∈ Z, (z - a) ^ m a))
    {w : ℂ} (hwZ : w ∈ Z) :
    AnalyticAt ℂ h w := by
  have hwBall : w ∈ Metric.ball c R := hmemBall w hwZ
  have hfacW : ∀ z, f z = (z - w) ^ m w * g w z := hfac w hwZ
  have hg0W : g w w ≠ 0 := hg0 w hwZ
  have hgAW : AnalyticAt ℂ (g w) w := hgA w
  have hRW : AnalyticAt ℂ (fun z => ∏ b ∈ Z.erase w, (z - b) ^ m b) w :=
    Finset.analyticAt_fun_prod _ (fun b hb => by fun_prop)
  have hRw0 : (∏ b ∈ Z.erase w, (w - b) ^ m b) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    exact Ne.symm (Finset.ne_of_mem_erase hb)
  have hfq : ∀ᶠ z in nhdsWithin w ({w}ᶜ : Set ℂ), f z ≠ 0 := by
    have hgnear : ∀ᶠ z in nhds w, g w z ≠ 0 :=
      hgAW.continuousAt.eventually_ne hg0W
    have hself : ∀ᶠ z in nhdsWithin w ({w}ᶜ : Set ℂ), z ∉ ({w} : Set ℂ) :=
      self_mem_nhdsWithin
    filter_upwards [hgnear.filter_mono nhdsWithin_le_nhds, hself] with z hgz hne
    have hzw : z ≠ w := by simpa using hne
    rw [hfacW z]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzw)) hgz
  have hnoZ : ∀ᶠ z in nhdsWithin w ({w}ᶜ : Set ℂ), z ∉ Z := by
    have hballmem : ∀ᶠ z in nhdsWithin w ({w}ᶜ : Set ℂ), z ∈ Metric.ball c R :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (IsOpen.mem_nhds Metric.isOpen_ball hwBall)
    filter_upwards [hfq, hballmem] with z hfz hzb
    intro hzZ
    have hfz0 : f z = 0 := by
      have h1 := hfac z hzZ z
      have hmz : m z ≠ 0 := by have := h1m z hzZ; omega
      rw [h1, sub_self, zero_pow hmz, zero_mul]
    exact hfz hfz0
  have hdisj : ∀ᶠ z in nhds w, z = w ∨ z ∉ Z := by
    have hmemS : {z | z ∉ Z} ∈ nhdsWithin w ({w}ᶜ : Set ℂ) := hnoZ
    obtain ⟨U, hU, hUS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hmemS
    apply Filter.mem_of_superset hU
    intro z hz
    by_cases hzw : z = w
    · exact Or.inl hzw
    · exact Or.inr (hUS ⟨hz, by simpa using hzw⟩)
  have heq : ∀ᶠ z in nhds w,
      h z = g w z / ∏ b ∈ Z.erase w, (z - b) ^ m b := by
    filter_upwards [hdisj] with z hz
    rcases hz with hzw | hnz
    · subst z
      rw [hdef w, ite_eq_left hwZ]
    · rw [hdef z, ite_eq_right hnz, hfacW z]
      have hPz : ∏ a ∈ Z, (z - a) ^ m a
          = (z - w) ^ m w * ∏ b ∈ Z.erase w, (z - b) ^ m b :=
        (Finset.mul_prod_erase Z _ hwZ).symm
      rw [hPz]
      have hzw : z ≠ w := fun h => hnz (h ▸ hwZ)
      have hpow : (z - w) ^ m w ≠ 0 :=
        pow_ne_zero _ (sub_ne_zero.mpr hzw)
      exact mul_div_mul_left _ _ hpow
  exact (hgAW.fun_div hRW hRw0).congr (Filter.EventuallyEq.symm heq)

private theorem aux_h_at_notmem
    {Z : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (h1m : ∀ a ∈ Z, 1 ≤ m a)
    (h : ℂ → ℂ)
    (hdef : ∀ z, h z = (if z ∈ Z then g z z / ∏ b ∈ Z.erase z, (z - b) ^ m b
      else f z / ∏ a ∈ Z, (z - a) ^ m a))
    {w : ℂ} (hw : w ∈ Metric.closedBall c R) (hwZ : w ∉ Z) :
    AnalyticAt ℂ h w := by
  have hPzero : ∀ z ∈ Z, ∏ a ∈ Z, (z - a) ^ m a = 0 := by
    intro z hz
    apply Finset.prod_eq_zero hz
    rw [sub_self]
    exact zero_pow (by have := h1m z hz; omega)
  have hPw : ∏ a ∈ Z, (w - a) ^ m a ≠ 0 := by
    intro hcon
    rw [Finset.prod_eq_zero_iff] at hcon
    obtain ⟨b, hbZ, hb0⟩ := hcon
    have hmb : m b ≠ 0 := by have := h1m b hbZ; omega
    have : w = b := sub_eq_zero.mp ((pow_eq_zero_iff hmb).mp hb0)
    exact hwZ (this ▸ hbZ)
  have hPA : AnalyticAt ℂ (fun z => ∏ a ∈ Z, (z - a) ^ m a) w :=
    Finset.analyticAt_fun_prod _ (fun a ha => by fun_prop)
  have heq : ∀ᶠ z in nhds w, h z = f z / ∏ a ∈ Z, (z - a) ^ m a := by
    have hPnear : ∀ᶠ z in nhds w, ∏ a ∈ Z, (z - a) ^ m a ≠ 0 :=
      hPA.continuousAt.eventually_ne hPw
    filter_upwards [hPnear] with z hz
    rw [hdef z, ite_eq_right (fun hzZ => hz (hPzero z hzZ))]
  exact ((hf w hw).fun_div hPA hPw).congr (Filter.EventuallyEq.symm heq)

private theorem aux_factor {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hf0 : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (hfin : ∀ w ∈ Metric.ball c R, analyticOrderAt f w ≠ ⊤) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ Metric.ball c R) ∧
      (∀ a ∈ Z, 1 ≤ m a) ∧
      AnalyticOnNhd ℂ h (Metric.closedBall c R) ∧
      (∀ z ∈ Metric.closedBall c R, h z ≠ 0) ∧
      (∀ z, f z = h z * ∏ a ∈ Z, (z - a) ^ m a) ∧
      (∀ a ∈ Z, MeromorphicOn.divisor f (Metric.ball c R) a = ((m a : ℕ) : ℤ)) ∧
      Function.support (MeromorphicOn.divisor f (Metric.ball c R)) ⊆ ↑Z := by
  have hball : MeromorphicOn f (Metric.ball c R) :=
    (hf.mono Metric.ball_subset_closedBall).meromorphicOn
  have hsupp : (MeromorphicOn.divisor f (Metric.ball c R)).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite hf.meromorphicOn
  obtain ⟨Z, hZ⟩ := Set.Finite.exists_finset_coe hsupp
  have hmemBall : ∀ a ∈ Z, a ∈ Metric.ball c R := by
    intro a ha
    by_contra habs
    have hD0 : MeromorphicOn.divisor f (Metric.ball c R) a = 0 :=
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ habs
    have hmem : a ∈ (MeromorphicOn.divisor f (Metric.ball c R)).support := by
      rw [← hZ]
      exact Finset.mem_coe.mpr ha
    exact (Function.mem_support.mp hmem) hD0
  have hDne : ∀ a ∈ Z, MeromorphicOn.divisor f (Metric.ball c R) a ≠ 0 := by
    intro a ha
    have hmem : a ∈ (MeromorphicOn.divisor f (Metric.ball c R)).support := by
      rw [← hZ]
      exact Finset.mem_coe.mpr ha
    exact Function.mem_support.mp hmem
  have hall : ∀ a, ∃ mm : ℕ, ∃ gg : ℂ → ℂ, AnalyticAt ℂ gg a ∧
      (a ∈ Z → gg a ≠ 0 ∧ (∀ z, f z = (z - a) ^ mm * gg z) ∧
        MeromorphicOn.divisor f (Metric.ball c R) a = ((mm : ℕ) : ℤ) ∧ 1 ≤ mm) := by
    intro a
    by_cases haZ : a ∈ Z
    · obtain ⟨mm, gg, hgA, hg0, hfac, hDm, h1m⟩ :=
        aux_local hf hfin (hmemBall a haZ) (hDne a haZ)
      exact ⟨mm, gg, hgA, fun _ => ⟨hg0, hfac, hDm, h1m⟩⟩
    · exact ⟨0, fun _ => 1, analyticAt_const, fun h => absurd h haZ⟩
  choose m g hmg using hall
  have hgA' : ∀ a, AnalyticAt ℂ (g a) a := fun a => (hmg a).1
  have hDm : ∀ a ∈ Z, MeromorphicOn.divisor f (Metric.ball c R) a = ((m a : ℕ) : ℤ) :=
    fun a ha => ((hmg a).2 ha).2.2.1
  have h1m : ∀ a ∈ Z, 1 ≤ m a := fun a ha => ((hmg a).2 ha).2.2.2
  have hfacPt : ∀ a ∈ Z, ∀ z, f z = (z - a) ^ m a * g a z :=
    fun a ha => ((hmg a).2 ha).2.1
  have hg0Pt : ∀ a ∈ Z, g a a ≠ 0 := fun a ha => ((hmg a).2 ha).1
  have hfac' : ∀ a ∈ Z, ∀ z, f z = (z - a) ^ m a * g a z :=
    fun a ha => ((hmg a).2 ha).2.1
  have hPzero : ∀ z ∈ Z, ∏ a ∈ Z, (z - a) ^ m a = 0 := by
    intro z hz
    apply Finset.prod_eq_zero hz
    rw [sub_self]
    exact zero_pow (by have := h1m z hz; omega)
  have hPne : ∀ z, z ∉ Z → ∏ a ∈ Z, (z - a) ^ m a ≠ 0 := by
    intro z hz
    rw [Finset.prod_ne_zero_iff]
    intro a ha hzero
    apply hz
    have hma : m a ≠ 0 := by have := h1m a ha; omega
    have hza2 : z = a := sub_eq_zero.mp ((pow_eq_zero_iff hma).mp hzero)
    rw [hza2]
    exact ha
  set h : ℂ → ℂ := fun z => if z ∈ Z then g z z / ∏ b ∈ Z.erase z, (z - b) ^ m b
    else f z / ∏ a ∈ Z, (z - a) ^ m a with hhdef
  have hdef : ∀ z, h z = (if z ∈ Z then g z z / ∏ b ∈ Z.erase z, (z - b) ^ m b
      else f z / ∏ a ∈ Z, (z - a) ^ m a) := fun z => rfl
  have hfac_all : ∀ z, f z = h z * ∏ a ∈ Z, (z - a) ^ m a := by
    intro z
    rw [hdef z]
    by_cases hzZ : z ∈ Z
    · rw [ite_eq_left hzZ, hPzero z hzZ, mul_zero]
      have h1 := hfacPt z hzZ z
      have hmz : m z ≠ 0 := by have := h1m z hzZ; omega
      rw [h1, sub_self, zero_pow hmz, zero_mul]
    · rw [ite_eq_right hzZ]
      exact (div_mul_cancel₀ _ (hPne z hzZ)).symm
  have hne : ∀ z ∈ Metric.closedBall c R, h z ≠ 0 := by
    intro w hw hcon
    have hfw : f w = 0 := by rw [hfac_all w, hcon, zero_mul]
    by_cases hwB : w ∈ Metric.ball c R
    · by_cases hwZ : w ∈ Z
      · have hRw0 : (∏ b ∈ Z.erase w, (w - b) ^ m b) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro b hb
          apply pow_ne_zero
          apply sub_ne_zero.mpr
          exact Ne.symm (Finset.ne_of_mem_erase hb)
        rw [hdef w, ite_eq_left hwZ] at hcon
        rcases div_eq_zero_iff.mp hcon with hL | hR
        · exact (hg0Pt w hwZ) hL
        · exact hRw0 hR
      · have hDz : MeromorphicOn.divisor f (Metric.ball c R) w = 0 :=
          Function.notMem_support.mp (by
            intro hmem
            apply hwZ
            rw [← Finset.mem_coe, hZ]
            exact hmem)
        have hfwne := aux_bridge hf hfin hwB hDz
        exact hfwne hfw
    · have hws : w ∈ Metric.sphere c R := by
        have h1 : dist w c ≤ R := Metric.mem_closedBall.mp hw
        have h2 : ¬ dist w c < R := fun hlt => hwB (Metric.mem_ball.mpr hlt)
        rw [Metric.mem_sphere]
        exact le_antisymm h1 (not_lt.mp h2)
      exact (hf0 w hws) hfw
  refine ⟨Z, m, h, hmemBall, h1m, ?_, hne, hfac_all, hDm, ?_⟩
  · intro w hw
    by_cases hwZ : w ∈ Z
    · exact aux_h_at_mem hmemBall h1m hgA' hg0Pt hfac' h hdef hwZ
    · exact aux_h_at_notmem hf h1m h hdef hw hwZ
  · intro z hz
    rw [hZ]
    exact hz

private theorem aux_arg {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hf0 : ∀ z ∈ Metric.sphere c R, f z ≠ 0) :
    ((∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)
    = ∮ z in C(c, R), deriv f z / f z := by
  have hfin := aux_ordfin hR hf hf0
  obtain ⟨Z, m, h, hmemBall, h1m, hAh, hneh, hfac, hDm, hsup⟩ :=
    aux_factor hf hf0 hfin
  have hsum : ∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z
      = ∑ a ∈ Z, ((m a : ℕ) : ℤ) := by
    rw [finsum_eq_sum_of_support_subset _ hsup]
    apply Finset.sum_congr rfl
    intro a ha
    exact hDm a ha
  have hza : ∀ z ∈ Metric.sphere c R, ∀ a ∈ Z, z ≠ a := by
    intro z hz a ha hcon
    have hab := hmemBall a ha
    rw [hcon] at hz
    have h1 := Metric.mem_ball.mp hab
    have h2 := Metric.mem_sphere.mp hz
    linarith
  have hPderiv : ∀ (s : Finset ℂ) (z : ℂ), (∀ a ∈ s, z ≠ a) →
      HasDerivAt (fun w => ∏ a ∈ s, (w - a) ^ m a)
        ((∏ a ∈ s, (z - a) ^ m a) * ∑ a ∈ s, ((m a : ℂ) / (z - a))) z := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro z _
      simpa using hasDerivAt_const z (1 : ℂ)
    · intro a s has ih z hz
      have hza0 : z ≠ a := hz a (Finset.mem_insert_self a s)
      have hzs : ∀ b ∈ s, z ≠ b := fun b hb => hz b (Finset.mem_insert_of_mem hb)
      have hbase : HasDerivAt (fun w : ℂ => w - a) (1 : ℂ) z :=
        (hasDerivAt_id z).sub_const a
      have h1 : HasDerivAt ((fun w : ℂ => w - a) ^ m a)
          ((m a : ℂ) * (z - a) ^ (m a - 1) * 1) z :=
        HasDerivAt.pow hbase (m a)
      have hpow2 : ((fun w : ℂ => w - a) ^ m a) = (fun w => (w - a) ^ m a) := rfl
      have hF : HasDerivAt (fun w => (w - a) ^ m a) ((m a : ℂ) * (z - a) ^ (m a - 1)) z := by
        rw [hpow2] at h1
        simpa using h1
      have hmul := hF.mul (ih z hzs)
      have hX : (z - a) ≠ 0 := sub_ne_zero.mpr hza0
      have hkey : (m a : ℂ) * (z - a) ^ (m a - 1)
          = (m a : ℂ) * (z - a) ^ m a / (z - a) := by
        rcases Nat.eq_zero_or_pos (m a) with hm0 | hpos
        · simp [hm0]
        · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : m a ≠ 0)
          rw [hk, Nat.add_sub_cancel, pow_succ']
          field_simp
      have hval : (m a : ℂ) * (z - a) ^ (m a - 1) * (∏ x ∈ s, (z - x) ^ m x)
          + (z - a) ^ m a * ((∏ x ∈ s, (z - x) ^ m x) * ∑ x ∈ s, ((m x : ℂ) / (z - x)))
          = ((z - a) ^ m a * ∏ x ∈ s, (z - x) ^ m x)
            * ((m a : ℂ) / (z - a) + ∑ x ∈ s, ((m x : ℂ) / (z - x))) := by
        rw [hkey]; ring
      simp only [Finset.prod_insert has, Finset.sum_insert has]
      rw [← hval]
      exact hmul
  have hPne : ∀ z ∈ Metric.sphere c R, ∏ a ∈ Z, (z - a) ^ m a ≠ 0 := by
    intro z hz
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    exact hza z hz a ha
  have hfderiv : ∀ z ∈ Metric.sphere c R, HasDerivAt f
      (deriv h z * (∏ a ∈ Z, (z - a) ^ m a)
        + h z * ((∏ a ∈ Z, (z - a) ^ m a) * ∑ a ∈ Z, ((m a : ℂ) / (z - a)))) z := by
    intro z hz
    have hAhz : AnalyticAt ℂ h z := hAh z (Metric.sphere_subset_closedBall hz)
    have hmul := (hAhz.differentiableAt.hasDerivAt).mul (hPderiv Z z (hza z hz))
    have hfeq : f = h * (fun w => ∏ a ∈ Z, (w - a) ^ m a) := by
      funext w
      exact hfac w
    rw [hfeq]
    exact hmul
  have hdiv : ∀ z ∈ Metric.sphere c R, deriv f z / f z
      = deriv h z / h z + ∑ a ∈ Z, ((m a : ℂ) / (z - a)) := by
    intro z hz
    have hfz : f z ≠ 0 := hf0 z hz
    have hhz : h z ≠ 0 := hneh z (Metric.sphere_subset_closedBall hz)
    have hPz0 := hPne z hz
    rw [(hfderiv z hz).deriv, hfac z]
    field_simp
  -- continuity / integrability on the sphere
  have htermA : ∀ a ∈ Z, ∀ z ∈ Metric.sphere c R,
      AnalyticAt ℂ (fun w => ((m a : ℂ) / (w - a))) z := by
    intro a ha z hz
    apply AnalyticAt.fun_div analyticAt_const (by fun_prop)
    apply sub_ne_zero.mpr
    exact hza z hz a ha
  have hcont_sum : ContinuousOn (fun z => ∑ a ∈ Z, ((m a : ℂ) / (z - a)))
      (Metric.sphere c R) := by
    intro z hz
    have hA : AnalyticAt ℂ (fun w => ∑ a ∈ Z, ((m a : ℂ) / (w - a))) z :=
      Finset.analyticAt_fun_sum _ (fun a ha => htermA a ha z hz)
    exact hA.continuousAt.continuousWithinAt
  have hcont_h : ContinuousOn (fun z => deriv h z / h z) (Metric.sphere c R) := by
    apply ContinuousOn.div
    · intro z hz
      have ha : AnalyticAt ℂ (deriv h) z :=
        (hAh z (Metric.sphere_subset_closedBall hz)).deriv
      exact ha.continuousAt.continuousWithinAt
    · exact (fun z hz =>
        (hAh z (Metric.sphere_subset_closedBall hz)).continuousAt.continuousWithinAt)
    · intro z hz
      exact hneh z (Metric.sphere_subset_closedBall hz)
  have hcont_f : ContinuousOn (fun z => deriv f z / f z) (Metric.sphere c R) := by
    apply ContinuousOn.div
    · intro z hz
      have ha : AnalyticAt ℂ (deriv f) z :=
        (hf z (Metric.sphere_subset_closedBall hz)).deriv
      exact ha.continuousAt.continuousWithinAt
    · exact (hf.mono Metric.sphere_subset_closedBall).continuousOn
    · intro z hz
      exact hf0 z hz
  have hint_h : CircleIntegrable (fun z => deriv h z / h z) c R :=
    ContinuousOn.circleIntegrable hR.le hcont_h
  have hint_sum : CircleIntegrable (fun z => ∑ a ∈ Z, ((m a : ℂ) / (z - a))) c R :=
    ContinuousOn.circleIntegrable hR.le hcont_sum
  have hInt : ∮ z in C(c, R), deriv f z / f z
      = (∮ z in C(c, R), deriv h z / h z)
        + (∮ z in C(c, R), ∑ a ∈ Z, ((m a : ℂ) / (z - a))) := by
    rw [circleIntegral.integral_congr hR.le (fun z hz => hdiv z hz)]
    exact circleIntegral.integral_add hint_h hint_sum
  have hvan : ∮ z in C(c, R), deriv h z / h z = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hR.le Set.countable_empty
    · apply ContinuousOn.div
      · intro z hz
        have ha : AnalyticAt ℂ (deriv h) z := (hAh z hz).deriv
        exact ha.continuousAt.continuousWithinAt
      · exact hAh.continuousOn
      · intro z hz
        exact hneh z hz
    · intro z hz
      rw [Set.sdiff_empty] at hz
      have haH : AnalyticAt ℂ h z := hAh z (Metric.ball_subset_closedBall hz)
      have had : AnalyticAt ℂ (deriv h) z := haH.deriv
      exact had.differentiableAt.div haH.differentiableAt
        (hneh z (Metric.ball_subset_closedBall hz))
  have htermI : ∀ a ∈ Z, CircleIntegrable (fun z => ((m a : ℂ) / (z - a))) c R := by
    intro a ha
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (htermA a ha z hz).continuousAt.continuousWithinAt
  have hSumInt : ∮ z in C(c, R), ∑ a ∈ Z, ((m a : ℂ) / (z - a))
      = ∑ a ∈ Z, (m a : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [circleIntegral.integral_fun_sum (fun a ha => htermI a ha)]
    apply Finset.sum_congr rfl
    intro a ha
    have hcauchy := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (E := ℂ) (R := R) (c := c) (w := a) (f := fun _ => (1 : ℂ)) (s := ∅)
      Set.countable_empty (hmemBall a ha) continuousOn_const
      (fun x _ => differentiableAt_const _)
    have e1 : (∮ z in C(c, R), ((z - a)⁻¹ : ℂ))
        = ∮ z in C(c, R), ((z - a)⁻¹ • (1 : ℂ)) := by
      congr 1
      funext z
      simp
    have e2 : (fun z => ((m a : ℂ) / (z - a)))
        = (fun z => (m a : ℂ) • ((z - a)⁻¹ : ℂ)) := by
      funext z
      simp [smul_eq_mul, div_eq_mul_inv]
    rw [e2, circleIntegral.integral_smul, e1, hcauchy]
    simp [smul_eq_mul]
  rw [hsum]
  simp only [Int.cast_sum, Int.cast_natCast]
  rw [hInt, hvan, zero_add, hSumInt]
  exact Finset.sum_mul Z (fun a => ((m a : ℕ) : ℂ)) (2 * ↑Real.pi * Complex.I)

private theorem aux_step {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hfg : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) :
    ∮ z in C(c, R), deriv (fun z => f z + g z) z / ((fun z => f z + g z) z)
    = ∮ z in C(c, R), deriv f z / f z := by
  obtain ⟨hf0, hF0⟩ := aux_sphere_ne_zero hfg
  have hF : AnalyticOnNhd ℂ (fun z => f z + g z) (Metric.closedBall c R) :=
    hf.add hg
  have hcontF : ContinuousOn
      (fun z => deriv (fun z => f z + g z) z / ((fun z => f z + g z) z))
      (Metric.sphere c R) := by
    apply ContinuousOn.div
    · intro z hz
      have ha : AnalyticAt ℂ (deriv (fun z => f z + g z)) z :=
        (hF z (Metric.sphere_subset_closedBall hz)).deriv
      exact ha.continuousAt.continuousWithinAt
    · exact (hF.mono Metric.sphere_subset_closedBall).continuousOn
    · intro z hz
      exact hF0 z hz
  have hcontf : ContinuousOn (fun z => deriv f z / f z) (Metric.sphere c R) := by
    apply ContinuousOn.div
    · intro z hz
      have ha : AnalyticAt ℂ (deriv f) z :=
        (hf z (Metric.sphere_subset_closedBall hz)).deriv
      exact ha.continuousAt.continuousWithinAt
    · exact (hf.mono Metric.sphere_subset_closedBall).continuousOn
    · intro z hz
      exact hf0 z hz
  have hintF : CircleIntegrable
      (fun z => deriv (fun z => f z + g z) z / ((fun z => f z + g z) z)) c R :=
    ContinuousOn.circleIntegrable hR.le hcontF
  have hintf : CircleIntegrable (fun z => deriv f z / f z) c R :=
    ContinuousOn.circleIntegrable hR.le hcontf
  have hH : ∀ z ∈ Metric.sphere c R,
      HasDerivWithinAt (fun z => Complex.log (1 + g z / f z))
        (deriv (fun z => f z + g z) z / ((fun z => f z + g z) z) - deriv f z / f z)
        (Metric.sphere c R) z := by
    intro z hz
    have hfz : f z ≠ 0 := hf0 z hz
    have hFz : (fun z => f z + g z) z ≠ 0 := hF0 z hz
    have hFz' : f z + g z ≠ 0 := hF0 z hz
    have hfA : AnalyticAt ℂ f z := hf z (Metric.sphere_subset_closedBall hz)
    have hgA : AnalyticAt ℂ g z := hg z (Metric.sphere_subset_closedBall hz)
    have hug : ‖g z / f z‖ < 1 := by
      have hfp : 0 < ‖f z‖ :=
        lt_of_le_of_lt (norm_nonneg _) (hfg z hz)
      rw [norm_div, div_lt_one hfp]
      exact hfg z hz
    have hRe : (0 : ℝ) < ((1 : ℂ) + g z / f z).re := by
      rw [Complex.add_re, Complex.one_re]
      have habs := Complex.abs_re_le_norm (g z / f z)
      rw [abs_le] at habs
      linarith [hug, habs.1]
    have hmem : (1 : ℂ) + g z / f z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff_not_le_zero, Complex.nonpos_iff]
      rintro ⟨hle, -⟩
      linarith
    have h1une : (1 : ℂ) + g z / f z ≠ 0 :=
      Complex.slitPlane_ne_zero hmem
    have hderivu : HasDerivAt (fun z => g z / f z)
        ((deriv g z * f z - g z * deriv f z) / (f z) ^ 2) z :=
      (hgA.differentiableAt.hasDerivAt).div (hfA.differentiableAt.hasDerivAt) hfz
    have hderivu1 : HasDerivAt (fun z => 1 + g z / f z)
        ((deriv g z * f z - g z * deriv f z) / (f z) ^ 2) z :=
      hderivu.const_add 1
    have hlogc : HasDerivAt (Complex.log ∘ (fun z => 1 + g z / f z))
        (((1 : ℂ) + g z / f z)⁻¹
          * ((deriv g z * f z - g z * deriv f z) / (f z) ^ 2)) z :=
      (Complex.hasDerivAt_log hmem).comp z hderivu1
    have hlog : HasDerivAt (fun z => Complex.log (1 + g z / f z))
        (((1 : ℂ) + g z / f z)⁻¹
          * ((deriv g z * f z - g z * deriv f z) / (f z) ^ 2)) z := hlogc
    have hFderiv : HasDerivAt (fun z => f z + g z) (deriv f z + deriv g z) z :=
      (hfA.differentiableAt.hasDerivAt).add (hgA.differentiableAt.hasDerivAt)
    have hderivF : deriv (fun z => f z + g z) z = deriv f z + deriv g z :=
      hFderiv.deriv
    have hval : ((1 : ℂ) + g z / f z)⁻¹
          * ((deriv g z * f z - g z * deriv f z) / (f z) ^ 2)
        = deriv (fun z => f z + g z) z / ((fun z => f z + g z) z)
          - deriv f z / f z := by
      rw [hderivF]
      field_simp
      ring
    rw [hval] at hlog
    exact hlog.hasDerivWithinAt
  have hD0 : ∮ z in C(c, R),
        (deriv (fun z => f z + g z) z / ((fun z => f z + g z) z) - deriv f z / f z)
      = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le (fun z hz => hH z hz)
  have hsub : (∮ z in C(c, R), deriv (fun z => f z + g z) z / ((fun z => f z + g z) z))
      - (∮ z in C(c, R), deriv f z / f z) = 0 := by
    have h1 := circleIntegral.integral_sub hintF hintf
    rw [← h1]
    exact hD0
  exact sub_eq_zero.mp hsub

/--
**Rouché's theorem on a disc.** Let $c \in \mathbb{C}$ and $R > 0$, and let $f$ and $g$ be analytic
at every point of the closed disc $|z - c| \le R$. If $|g(z)| < |f(z)|$ for every $z$ on the circle
$|z - c| = R$, then $f$ and $f + g$ have the same number of zeros in the open disc $|z - c| < R$,
counted with multiplicity: the divisors of $f$ and of $f + g$ on the open disc have equal sums.

Source: E. Rouché, Mémoire sur la série de Lagrange, J. École Polytechnique 22 (1862), 193-224

Proves `Wanted` entry `rouche_closedBall`.
-/
theorem rouche_closedBall
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hfg : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) :
    ∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z =
    ∑ᶠ z, MeromorphicOn.divisor (fun z => f z + g z) (Metric.ball c R) z := by
  obtain ⟨hf0, hF0⟩ := aux_sphere_ne_zero hfg
  have hF : AnalyticOnNhd ℂ (fun z => f z + g z) (Metric.closedBall c R) :=
    hf.add hg
  have hAf := aux_arg hR hf hf0
  have hAF := aux_arg hR hF (fun z hz => hF0 z hz)
  have hEq := aux_step hR hf hg hfg
  have hboth : ((∑ᶠ z, MeromorphicOn.divisor (fun z => f z + g z) (Metric.ball c R) z : ℤ) : ℂ)
      * (2 * ↑Real.pi * Complex.I)
      = ((∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z : ℤ) : ℂ)
      * (2 * ↑Real.pi * Complex.I) := by
    rw [hAF, hEq]
    exact hAf.symm
  have hcast : ((∑ᶠ z, MeromorphicOn.divisor (fun z => f z + g z) (Metric.ball c R) z : ℤ) : ℂ)
      = ((∑ᶠ z, MeromorphicOn.divisor f (Metric.ball c R) z : ℤ) : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero hboth
  exact (Int.cast_injective hcast).symm

end MathlibExt.Analysis.Complex.Rouche
