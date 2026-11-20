/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Mathlib
import Code.Universality.SAW

namespace StatMech.Universality

open Filter Topology
open scoped Topology Real NNReal








noncomputable def hexChiE : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)


noncomputable def hexCl : ℝ := Real.cos (3 * Real.pi / 8)


noncomputable def hexCt : ℝ := Real.cos (Real.pi / 4)


lemma hex_sqrt_pos : 0 < Real.sqrt (2 + Real.sqrt 2) := by
  apply Real.sqrt_pos.mpr; positivity


lemma hexChiE_pos : 0 < hexChiE := by
  unfold hexChiE; exact div_pos one_pos hex_sqrt_pos


lemma one_div_hexChi : 1 / hexChiE = Real.sqrt (2 + Real.sqrt 2) := by
  unfold hexChiE; rw [one_div_one_div]


lemma hexCl_pos : 0 < hexCl := by
  unfold hexCl
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]


lemma hexCt_pos : 0 < hexCt := by
  unfold hexCt; rw [Real.cos_pi_div_four]; positivity












theorem hex_recip_induction (u : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hpos : ∀ v, 1 ≤ v → 0 < u v)
    (hmono : ∀ v, 1 ≤ v → u (v + 1) ≤ u v)
    (hrec : ∀ v, 1 ≤ v → u v - u (v + 1) ≤ C * (u (v + 1)) ^ 2) :
    ∀ v, 1 ≤ v → 1 / u v ≤ v / min (u 1) (1 / C) := by
  set m := min (u 1) (1 / C) with hm
  have hm1 : 0 < m := by rw [hm]; exact lt_min (hpos 1 le_rfl) (by positivity)
  have hmle1 : m ≤ u 1 := min_le_left _ _
  have hmleC : m ≤ 1 / C := min_le_right _ _
  intro v hv
  induction v with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge 1 (k + 1) with hk | hk
    · have hk1 : 1 ≤ k := by omega
      have ihk := ih hk1
      have hpk := hpos k hk1
      have hpk1 := hpos (k + 1) (by omega)
      have hmonok := hmono k hk1
      have hreck := hrec k hk1
      have step : 1 / u (k + 1) ≤ 1 / u k + C := by
        rw [div_add' _ _ _ (ne_of_gt hpk), div_le_div_iff₀ hpk1 hpk]
        nlinarith [hpk1, hmonok, hC, hreck]
      calc 1 / u (k + 1) ≤ 1 / u k + C := step
        _ ≤ (k : ℝ) / m + C := by linarith [ihk]
        _ ≤ (k : ℝ) / m + 1 / m := by
              have hCm : C ≤ 1 / m := by
                rw [le_div_iff₀ hm1]
                calc C * m ≤ C * (1 / C) := by nlinarith [hmleC, hC]
                  _ = 1 := by field_simp
              linarith
        _ = ((k + 1 : ℕ) : ℝ) / m := by push_cast; rw [add_div]
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [show ((0 + 1 : ℕ) : ℝ) = 1 by norm_num, div_le_div_iff₀ (hpos 1 le_rfl) hm1]
      nlinarith [hmle1, hpos 1 le_rfl]





theorem hex_div_of_lower_bound (u : ℕ → ℝ) (m : ℝ) (hm : 0 < m)
    (hu0 : ∀ n, 0 ≤ u n) (hge : ∀ v, 1 ≤ v → m / v ≤ u v) :
    ¬ Summable u := by
  intro hsum
  have hcomp : Summable (fun n : ℕ => m / n) := by
    refine hsum.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · subst h0; simpa using hu0 0
    · exact hge n hp
  have hs : Summable (fun n : ℕ => (1 : ℝ) / n) := by
    refine (hcomp.mul_left m⁻¹).congr (fun n => ?_); field_simp
  exact Real.not_summable_one_div_natCast hs




theorem hex_pow_rootid (c x : ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : 0 < c) :
    (c ^ ((n : ℝ)⁻¹) * x) ^ n = c * x ^ n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_pow]; congr 1
  rw [← Real.rpow_natCast (c ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul (le_of_lt hc),
    inv_mul_cancel₀ (ne_of_gt hnpos), Real.rpow_one]





theorem hex_root_summable (c : ℕ → ℝ) (x kappa : ℝ) (hx : 0 ≤ x)
    (hge : ∀ n, 1 ≤ c n)
    (hroot : Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa))
    (hlt : kappa * x < 1) :
    Summable (fun n => c n * x ^ n) := by
  have hk1 : 1 ≤ kappa := by
    refine ge_of_tendsto hroot ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.one_le_rpow (hge n) (by positivity)
  obtain ⟨r, hkr, hr1⟩ := exists_between hlt
  have hrnn : 0 ≤ r := le_trans (by positivity) (le_of_lt hkr)
  have hprod : Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹) * x) atTop (𝓝 (kappa * x)) :=
    hroot.mul_const x
  have hev : ∀ᶠ n in atTop, (c n) ^ ((n : ℝ)⁻¹) * x < r := hprod.eventually_lt_const hkr
  refine Summable.of_norm_bounded_eventually (g := fun n => r ^ n)
    (summable_geometric_of_lt_one hrnn hr1) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one (hge n)
  have hbase : 0 ≤ (c n) ^ ((n : ℝ)⁻¹) * x := by positivity
  calc ‖c n * x ^ n‖ = c n * x ^ n := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = ((c n) ^ ((n : ℝ)⁻¹) * x) ^ n := (hex_pow_rootid (c n) x n hn1 hcpos).symm
    _ ≤ r ^ n := pow_le_pow_left₀ hbase (le_of_lt hn) n





theorem hex_root_not_summable (c : ℕ → ℝ) (x kappa : ℝ)
    (hge : ∀ n, 1 ≤ c n)
    (hroot : Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa))
    (hgt : 1 < kappa * x) :
    ¬ Summable (fun n => c n * x ^ n) := by
  intro hsum
  have hto0 : Tendsto (fun n => c n * x ^ n) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hprod : Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹) * x) atTop (𝓝 (kappa * x)) :=
    hroot.mul_const x
  have hev : ∀ᶠ n in atTop, 1 < (c n) ^ ((n : ℝ)⁻¹) * x := hprod.eventually_const_lt hgt
  have hge1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ c n * x ^ n := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hcpos : 0 < c n := lt_of_lt_of_le zero_lt_one (hge n)
    rw [← hex_pow_rootid (c n) x n hn1 hcpos]
    calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
      _ ≤ ((c n) ^ ((n : ℝ)⁻¹) * x) ^ n := pow_le_pow_left₀ zero_le_one (le_of_lt hn) n
  have hlt1 : ∀ᶠ n in atTop, c n * x ^ n < 1 := by
    have := hto0.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this] with n hn; simpa using hn
  obtain ⟨n, hn1, hn2⟩ := (hge1.and hlt1).exists
  linarith


























theorem hexZ_chi_div (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE * (ups (v + 1)) ^ 2)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable (fun n => c n * hexChiE ^ n))
    (hυemb : Summable (fun n => c n * hexChiE ^ n) → Summable ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  by_cases hτ : ∃ v, 1 ≤ v ∧ 0 < tau v
  · 
    exact hτcol hτ
  · 
    push Not at hτ
    have hτ0 : ∀ v, 1 ≤ v → tau v = 0 := fun v hv =>
      le_antisymm (hτ v hv) (hτnn v)
    
    have hbd2 : ∀ v, 1 ≤ v → hexCl * lam v + ups v = 1 := by
      intro v hv
      have h := hbdry v hv
      rw [hτ0 v hv, mul_zero, add_zero] at h
      exact h
    
    have hdefect : ∀ v, 1 ≤ v → ups v - ups (v + 1) ≤ (hexCl * hexChiE) * (ups (v + 1)) ^ 2 := by
      intro v hv
      
      have e1 := hbd2 v hv
      have e2 := hbd2 (v + 1) (by omega)
      have hr := hrec v hv
      
      have hmul : hexCl * (lam (v + 1) - lam v) ≤ hexCl * (hexChiE * (ups (v + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_left hr (le_of_lt hexCl_pos)
      nlinarith [hmul, e1, e2]
    
    have hυmono : ∀ v, 1 ≤ v → ups (v + 1) ≤ ups v := by
      intro v hv
      have e1 := hbd2 v hv
      have e2 := hbd2 (v + 1) (by omega)
      have hmono := hlamMono v hv
      
      nlinarith [mul_le_mul_of_nonneg_left hmono (le_of_lt hexCl_pos)]
    
    set C := hexCl * hexChiE with hCdef
    have hCpos : 0 < C := mul_pos hexCl_pos hexChiE_pos
    have hrecip := hex_recip_induction ups C hCpos hυpos hυmono hdefect
    set m := min (ups 1) (1 / C) with hmdef
    have hmpos : 0 < m := lt_min (hυpos 1 le_rfl) (by positivity)
    
    have hlower : ∀ v, 1 ≤ v → m / v ≤ ups v := by
      intro v hv
      have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
      have huv := hυpos v hv
      
      have h := hrecip v hv
      rw [div_le_div_iff₀ huv hmpos] at h
      
      rw [div_le_iff₀ hvpos]
      nlinarith [h]
    
    have hυdiv : ¬ Summable ups :=
      hex_div_of_lower_bound ups m hmpos hυnn hlower
    
    intro hZ
    exact hυdiv (hυemb hZ)












theorem hex_ups_summable (upsx : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hlt : x < hexChiE)
    (hυnn : ∀ T, 0 ≤ upsx T) (hυle : ∀ T, upsx T ≤ (x / hexChiE) ^ T) :
    Summable upsx := by
  have hgeom : Summable (fun T : ℕ => (x / hexChiE) ^ T) := by
    apply summable_geometric_of_lt_one (div_nonneg hx (le_of_lt hexChiE_pos))
    rw [div_lt_one hexChiE_pos]; exact hlt
  exact hgeom.of_nonneg_of_le hυnn hυle




theorem hex_bridge_multipliable (upsx : ℕ → ℝ) (hsum : Summable upsx) :
    Multipliable (fun T => 1 + upsx T) :=
  Real.multipliable_one_add_of_summable hsum
















theorem hexZ_conv (c upsx : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hlt : x < hexChiE)
    (hc : ∀ n, 0 ≤ c n)
    (hυnn : ∀ T, 0 ≤ upsx T) (hυle : ∀ T, upsx T ≤ (x / hexChiE) ^ T)
    (hbridge : ∀ N, ∑ n ∈ Finset.range N, c n * x ^ n
        ≤ 2 * (∏' T, (1 + upsx T)) ^ 2) :
    Summable (fun n => c n * x ^ n) := by
  
  
  
  have hsum : Summable upsx := hex_ups_summable upsx x hx hlt hυnn hυle
  have _hmul : Multipliable (fun T => 1 + upsx T) := hex_bridge_multipliable upsx hsum
  
  refine summable_of_sum_range_le
    (f := fun n => c n * x ^ n) (c := 2 * (∏' T, (1 + upsx T)) ^ 2) ?_ ?_
  · intro n; exact mul_nonneg (hc n) (pow_nonneg hx n)
  · intro N; exact hbridge N
















theorem hex_kappa_eq (c : ℕ → ℝ) (kappa : ℝ)
    (hge : ∀ n, 1 ≤ c n)
    (hroot : Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa))
    (hdiv : ¬ Summable (fun n => c n * hexChiE ^ n))
    (hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n)) :
    kappa = 1 / hexChiE := by
  have hk1 : 1 ≤ kappa := by
    refine ge_of_tendsto hroot ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.one_le_rpow (hge n) (by positivity)
  have hkpos : 0 < kappa := lt_of_lt_of_le zero_lt_one hk1
  have hχpos := hexChiE_pos
  
  have hge1 : 1 ≤ kappa * hexChiE := by
    by_contra hlt
    push Not at hlt
    exact hdiv (hex_root_summable c hexChiE kappa (le_of_lt hχpos) hge hroot hlt)
  
  have hle1 : kappa * hexChiE ≤ 1 := by
    by_contra hgt
    push Not at hgt
    
    have hinvlt : 1 / kappa < hexChiE := by
      rw [div_lt_iff₀ hkpos, mul_comm]; exact hgt
    obtain ⟨x, hx1, hx2⟩ := exists_between hinvlt
    have hinvnn : (0 : ℝ) ≤ 1 / kappa := by positivity
    have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt hinvnn hx1)
    
    have hkx : 1 < kappa * x := by
      rw [div_lt_iff₀ hkpos] at hx1; linarith [hx1]
    exact hex_root_not_summable c x kappa hge hroot hkx (hconv x hx0 hx2)
  
  have heq : kappa * hexChiE = 1 := le_antisymm hle1 hge1
  field_simp
  linarith [heq]













theorem hex_connective_constant (c : ℕ → ℝ)
    (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    (hdiv : ¬ Summable (fun n => c n * hexChiE ^ n))
    (hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n)) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) := by
  obtain ⟨kappa, hkpos, hroot⟩ := connectiveConstant_tendsto hge hsub
  refine ⟨kappa, hkpos, hroot, ?_⟩
  rw [hex_kappa_eq c kappa hge hroot hdiv hconv, one_div_hexChi]

end StatMech.Universality
