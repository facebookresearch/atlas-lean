/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Foundations.Kingman
import Code.Foundations.BirkhoffPointwise

open MeasureTheory Filter Topology

namespace StatMech

namespace KingmanAE

open Kingman BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}




theorem ae_all_subadditive (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, ∀ m n, X (m + n) x ≤ X m x + X n (T^[m] x) := by
  rw [ae_all_iff]
  intro m
  rw [ae_all_iff]
  intro n
  exact h.subadditive m n











theorem ae_le_block_birkhoffSum (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, ∀ k q, 1 ≤ q → X (q * k) x ≤ birkhoffSum (T^[k]) (X k) q x := by
  filter_upwards [ae_all_subadditive h] with x hx
  intro k q
  induction q with
  | zero => intro h0; exact absurd h0 (by norm_num)
  | succ q ih =>
    intro _
    have hstep : X ((q + 1) * k) x ≤ X (q * k) x + X k (T^[q * k] x) := by
      have := hx (q * k) k
      rwa [show q * k + k = (q + 1) * k by ring] at this
    have hiter : (T^[k])^[q] x = T^[q * k] x := by
      rw [← Function.iterate_mul, Nat.mul_comm]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp only [Nat.zero_add, Nat.one_mul, birkhoffSum_one, le_refl]
    · calc X ((q + 1) * k) x ≤ X (q * k) x + X k (T^[q * k] x) := hstep
        _ ≤ birkhoffSum (T^[k]) (X k) q x + X k (T^[q * k] x) := by gcongr; exact ih hq
        _ = birkhoffSum (T^[k]) (X k) q x + X k ((T^[k])^[q] x) := by rw [hiter]
        _ = birkhoffSum (T^[k]) (X k) (q + 1) x := (birkhoffSum_succ (T^[k]) (X k) q x).symm



variable [IsFiniteMeasure μ]








theorem tendsto_comp_div_atTop (hT : MeasurePreserving T μ μ) {g : α → ℝ}
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun m : ℕ => g (T^[m] x) / m) atTop (𝓝 0) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT hg] with x hx
  set L : ℝ := birkhoffLimit T g x with hL
  
  have hkey : ∀ᶠ m : ℕ in atTop, g (T^[m] x) / m
      = (((m : ℝ) + 1) / m) * birkhoffAverage ℝ T g (m + 1) x - birkhoffAverage ℝ T g m x := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hsucc : birkhoffSum T g (m + 1) x = birkhoffSum T g m x + g (T^[m] x) :=
      birkhoffSum_succ T g m x
    simp only [birkhoffAverage, smul_eq_mul]
    rw [hsucc]
    push_cast
    field_simp
    ring
  rw [tendsto_congr' hkey]
  
  have hr : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / m) atTop (𝓝 1) := by
    have key : ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 1) / m = 1 + 1 / (m : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with m hm
      have : (m : ℝ) ≠ 0 := by positivity
      field_simp
    rw [tendsto_congr' key]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
  have hA1 : Tendsto (fun m : ℕ => birkhoffAverage ℝ T g (m + 1) x) atTop (𝓝 L) :=
    hx.comp (tendsto_add_atTop_nat 1)
  have hprod : Tendsto (fun m : ℕ => (((m : ℝ) + 1) / m) * birkhoffAverage ℝ T g (m + 1) x)
      atTop (𝓝 (1 * L)) := hr.mul hA1
  rw [one_mul] at hprod
  have := hprod.sub hx
  rwa [sub_self] at this



omit [IsFiniteMeasure μ] in

theorem tendsto_natDiv_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => n / k) atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro b
  refine ⟨b * k, fun n hn => ?_⟩
  calc b = b * k / k := by rw [Nat.mul_div_cancel _ hk]
    _ ≤ n / k := Nat.div_le_div_right hn

omit [IsFiniteMeasure μ] in

theorem tendsto_natDiv_div_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (k : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hupper : ∀ n : ℕ, ((n / k : ℕ) : ℝ) * k / n ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast hn)]
      have hle : (n / k) * k ≤ n := Nat.div_mul_le_self n k
      calc ((n / k : ℕ) : ℝ) * k = (((n / k) * k : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (n : ℝ) := by exact_mod_cast hle
  have hlower : ∀ n : ℕ, 1 ≤ n → 1 - (k : ℝ) / n ≤ ((n / k : ℕ) : ℝ) * k / n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlt : n < (n / k) * k + k := Nat.lt_div_mul_add hk
    have h2 : (n : ℝ) ≤ ((n / k : ℕ) : ℝ) * k + k := by
      calc (n : ℝ) ≤ (((n / k) * k + k : ℕ) : ℝ) := by exact_mod_cast hlt.le
        _ = ((n / k : ℕ) : ℝ) * k + k := by push_cast; ring
    rw [sub_le_iff_le_add,
      show ((n / k : ℕ) : ℝ) * k / n + (k : ℝ) / n = (((n / k : ℕ) : ℝ) * k + k) / n by ring,
      le_div_iff₀ hn0, one_mul]
    exact h2
  have hmid : Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) * k / n) atTop (𝓝 1) := by
    have hL : Tendsto (fun n : ℕ => 1 - (k : ℝ) / n) atTop (𝓝 1) := by
      have hkz : Tendsto (fun n : ℕ => (k : ℝ) / n) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (k : ℝ))).div_atTop tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hkz
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with n hn using hlower n hn
    · filter_upwards with n using hupper n
  have hfin : Tendsto (fun n : ℕ => (((n / k : ℕ) : ℝ) * k / n) / k) atTop (𝓝 (1 / k)) :=
    hmid.div_const k
  refine hfin.congr (fun n => ?_)
  by_cases hn : n = 0
  · simp [hn]
  · field_simp






noncomputable def remDom (X : ℕ → α → ℝ) (k : ℕ) (y : α) : ℝ :=
  ∑ r ∈ Finset.range k, (X r y)⁺

omit [IsFiniteMeasure μ] in

theorem remDom_integrable (h : SubadditiveCocycle T μ X) (k : ℕ) : Integrable (remDom X k) μ := by
  unfold remDom; exact integrable_finsetSum _ (fun r _ => (h.integrable r).pos_part)

omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem remDom_nonneg (X : ℕ → α → ℝ) (k : ℕ) (y : α) : 0 ≤ remDom X k y := by
  unfold remDom; positivity

omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem le_remDom (X : ℕ → α → ℝ) {k r : ℕ} (hr : r < k) (y : α) : X r y ≤ remDom X k y := by
  unfold remDom
  calc X r y ≤ (X r y)⁺ := le_max_left _ _
    _ ≤ ∑ s ∈ Finset.range k, (X s y)⁺ :=
        Finset.single_le_sum (f := fun s => (X s y)⁺) (fun i _ => by positivity)
          (Finset.mem_range.mpr hr)











theorem gStar_le (h : SubadditiveCocycle T μ X) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ x ∂μ, limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop
      ≤ ((birkhoffLimit (T^[k]) (X k) x / k : ℝ) : EReal) := by
  have hTk : MeasurePreserving (T^[k]) μ μ := h.measurePreserving.iterate k
  filter_upwards [ae_all_subadditive h, ae_le_block_birkhoffSum h,
    tendsto_birkhoffAverage_ae hTk (h.integrable k),
    tendsto_comp_div_atTop h.measurePreserving (remDom_integrable h k)] with x hsub hblk hbirk hrem
  set Λ : ℝ := birkhoffLimit (T^[k]) (X k) x with hΛ
  set q : ℕ → ℕ := fun n => n / k with hq
  set R : ℕ → ℝ := fun n =>
    ((q n : ℝ) / n) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x
      + remDom X k (T^[q n * k] x) / (q n * k) with hR
  
  have hle : ∀ᶠ n in atTop, X n x / n ≤ R n := by
    filter_upwards [eventually_ge_atTop k] with n hn
    have hkpos : 0 < k := hk
    have hnpos : 0 < n := lt_of_lt_of_le hkpos hn
    have hqpos : 1 ≤ q n := by rw [hq]; exact (Nat.one_le_div_iff hkpos).mpr hn
    have hqk_pos : 0 < q n * k := Nat.mul_pos hqpos hkpos
    have hqk_le : q n * k ≤ n := by rw [hq]; exact Nat.div_mul_le_self n k
    have hr : n % k < k := Nat.mod_lt n hkpos
    have hdecomp : q n * k + n % k = n := by rw [hq]; exact Nat.div_add_mod' n k
    have hcoc : X n x ≤ X (q n * k) x + X (n % k) (T^[q n * k] x) := by
      have := hsub (q n * k) (n % k); rwa [hdecomp] at this
    have hblock : X (q n * k) x ≤ birkhoffSum (T^[k]) (X k) (q n) x := hblk k (q n) hqpos
    have hremb : X (n % k) (T^[q n * k] x) ≤ remDom X k (T^[q n * k] x) :=
      le_remDom X hr (T^[q n * k] x)
    have hXn : X n x ≤ birkhoffSum (T^[k]) (X k) (q n) x + remDom X k (T^[q n * k] x) :=
      calc X n x ≤ X (q n * k) x + X (n % k) (T^[q n * k] x) := hcoc
        _ ≤ birkhoffSum (T^[k]) (X k) (q n) x + remDom X k (T^[q n * k] x) := by gcongr
    have hbs : birkhoffSum (T^[k]) (X k) (q n) x
        = (q n : ℝ) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x := by
      rw [birkhoffAverage, smul_eq_mul, ← mul_assoc]
      rcases Nat.eq_zero_or_pos (q n) with h0 | h0
      · simp [h0, birkhoffSum_zero]
      · rw [mul_inv_cancel₀ (by exact_mod_cast h0.ne'), one_mul]
    have hremdiv : remDom X k (T^[q n * k] x)
        ≤ remDom X k (T^[q n * k] x) / (q n * k) * n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hqk_pos)]
      have hnn : 0 ≤ remDom X k (T^[q n * k] x) := remDom_nonneg X k _
      have hqkn : (q n * k : ℝ) ≤ n := by exact_mod_cast hqk_le
      nlinarith [hnn, hqkn]
    rw [div_le_iff₀ (by exact_mod_cast hnpos)]
    calc X n x ≤ birkhoffSum (T^[k]) (X k) (q n) x + remDom X k (T^[q n * k] x) := hXn
      _ = (q n : ℝ) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x
            + remDom X k (T^[q n * k] x) := by rw [hbs]
      _ ≤ (q n : ℝ) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x
            + remDom X k (T^[q n * k] x) / (q n * k) * n := by linarith [hremdiv]
      _ = R n * n := by rw [hR]; field_simp
  
  have hRtend : Tendsto R atTop (𝓝 (Λ / k)) := by
    have hqinf : Tendsto q atTop atTop := tendsto_natDiv_atTop hk
    have hratio : Tendsto (fun n : ℕ => ((q n : ℝ)) / (n : ℝ)) atTop (𝓝 (1 / (k : ℝ))) :=
      tendsto_natDiv_div_atTop hk
    have hAcomp : Tendsto (fun n : ℕ => birkhoffAverage ℝ (T^[k]) (X k) (q n) x) atTop (𝓝 Λ) :=
      hbirk.comp hqinf
    have hterm1 : Tendsto
        (fun n : ℕ => ((q n : ℝ) / n) * birkhoffAverage ℝ (T^[k]) (X k) (q n) x) atTop
        (𝓝 (1 / (k : ℝ) * Λ)) := hratio.mul hAcomp
    have hqkinf : Tendsto (fun n : ℕ => q n * k) atTop atTop := by
      have hmk : Tendsto (fun m : ℕ => m * k) atTop atTop := by
        apply tendsto_atTop_atTop.2; intro b; refine ⟨b, fun m hm => ?_⟩
        exact le_trans hm (Nat.le_mul_of_pos_right m hk)
      exact hmk.comp hqinf
    have hterm2 : Tendsto (fun n : ℕ => remDom X k (T^[q n * k] x) / (q n * k)) atTop (𝓝 0) := by
      have hc := hrem.comp hqkinf
      refine hc.congr (fun n => ?_)
      simp only [Function.comp_apply, Nat.cast_mul]
    have hsum := hterm1.add hterm2
    rw [add_zero] at hsum
    have : 1 / (k : ℝ) * Λ = Λ / k := by rw [div_mul_eq_mul_div, one_mul]
    rwa [this] at hsum
  
  have h1 : limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop
      ≤ limsup (fun n => ((R n : ℝ) : EReal)) atTop := by
    refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [hle] with n hn; exact_mod_cast hn
  have h2 : Tendsto (fun n => ((R n : ℝ) : EReal)) atTop (𝓝 ((Λ / k : ℝ) : EReal)) := by
    rw [EReal.tendsto_coe]; exact hRtend
  rw [h2.limsup_eq] at h1
  exact h1






@[nolint unusedArguments]
noncomputable def gStar (_T : α → α) (X : ℕ → α → ℝ) (x : α) : EReal :=
  limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop


@[nolint unusedArguments]
noncomputable def gStarLow (_T : α → α) (X : ℕ → α → ℝ) (x : α) : EReal :=
  liminf (fun n => ((X n x / n : ℝ) : EReal)) atTop

omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem gStarLow_le_gStar (x : α) : gStarLow T X x ≤ gStar T X x := liminf_le_limsup

omit [IsFiniteMeasure μ] in






theorem gStar_le_comp (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, gStar T X x ≤ gStar T X (T x) := by
  have hsub : ∀ᵐ x ∂μ, ∀ n, X (n + 1) x ≤ X 1 x + X n (T x) := by
    rw [ae_all_iff]; intro n
    filter_upwards [h.subadditive 1 n] with x hx
    rw [show 1 + n = n + 1 by ring] at hx; simpa using hx
  filter_upwards [hsub] with x hx
  unfold gStar
  set L : EReal := limsup (fun n => ((X n (T x) / n : ℝ) : EReal)) atTop with hL
  rw [limsup_le_iff']
  intro y hyL
  obtain ⟨z, hLz, hzy⟩ := EReal.lt_iff_exists_real_btwn.mp hyL
  have h0 : ∀ᶠ n in atTop, ((X n (T x) / n : ℝ) : EReal) < (z : EReal) :=
    eventually_lt_of_limsup_lt (hL ▸ hLz)
  have hev : ∀ᶠ n in atTop, X n (T x) / n < z := by
    filter_upwards [h0] with n hn; exact_mod_cast hn
  have hr : Tendsto (fun n : ℕ => X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * z) atTop (𝓝 z) := by
    have h1 : Tendsto (fun n : ℕ => X 1 x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := X 1 x)).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (n + 1) = 1 - 1 / ((n : ℝ) + 1) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp; ring
      rw [tendsto_congr' key]
      have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
    simpa using h1.add (h2.mul tendsto_const_nhds)
  have hbound : ∀ᶠ n in atTop,
      X (n + 1) x / (n + 1) < X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * z := by
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hpos
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hXle : X (n + 1) x ≤ X 1 x + X n (T x) := hx n
    have hXn : X n (T x) < n * z := by rw [div_lt_iff₀ hnn] at hn; linarith [hn]
    have hrw : X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * z = (X 1 x + n * z) / (n + 1) := by
      field_simp
    rw [hrw, div_lt_div_iff_of_pos_right hn1]; linarith
  rcases eq_top_or_lt_top y with hytop | hytop
  · filter_upwards with n; rw [hytop]; exact le_top
  · have hybot : y ≠ ⊥ := fun hh => by rw [hh] at hzy; exact not_lt_bot hzy
    have hyr : y = (y.toReal : EReal) := (EReal.coe_toReal hytop.ne hybot).symm
    have hzyr : z < y.toReal := by rw [hyr] at hzy; exact_mod_cast hzy
    have hrlt : ∀ᶠ n : ℕ in atTop, X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * z < y.toReal :=
      hr.eventually (eventually_lt_nhds hzyr)
    have hsucc : ∀ᶠ n in atTop, ((X (n + 1) x / ((n : ℝ) + 1) : ℝ) : EReal) ≤ y := by
      filter_upwards [hbound, hrlt] with n hn1 hn2
      have hlt : X (n + 1) x / (n + 1) < y.toReal := lt_trans hn1 hn2
      rw [hyr]; exact_mod_cast hlt.le
    rw [eventually_atTop] at hsucc ⊢
    obtain ⟨N, hN⟩ := hsucc
    refine ⟨N + 1, fun m hm => ?_⟩
    have hmm : (m - 1) + 1 = m := by omega
    have key := hN (m - 1) (by omega)
    rw [hmm] at key
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by rw [← hmm]; push_cast; ring
    rw [hcast] at key
    exact key


theorem gStar_le_birkhoffLimit (h : SubadditiveCocycle T μ X) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ x ∂μ, gStar T X x ≤ ((birkhoffLimit (T^[k]) (X k) x / k : ℝ) : EReal) :=
  gStar_le h hk



theorem gStar_lt_top_ae (h : SubadditiveCocycle T μ X) : ∀ᵐ x ∂μ, gStar T X x < ⊤ := by
  filter_upwards [gStar_le h (k := 1) le_rfl] with x hx
  exact lt_of_le_of_lt hx (EReal.coe_lt_top _)


theorem gStar_le_birkhoffLimit_one (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, gStar T X x ≤ ((birkhoffLimit T (X 1) x : ℝ) : EReal) := by
  filter_upwards [gStar_le h (k := 1) le_rfl] with x hx
  simpa using hx





noncomputable def kingmanLimit (T : α → α) (X : ℕ → α → ℝ) (x : α) : ℝ := (gStar T X x).toReal












theorem tendsto_div_kingmanLimit_ae (h : SubadditiveCocycle T μ X)
    (heq : ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x)
    (hbot : ∀ᵐ x ∂μ, ⊥ < gStar T X x) :
    ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
  filter_upwards [heq, hbot, gStar_lt_top_ae h] with x hxeq hxbot hxtop
  set ℓ : EReal := gStar T X x with hℓ
  have hlow_le : gStarLow T X x ≤ ℓ := gStarLow_le_gStar x
  have hloweq : liminf (fun n => ((X n x / n : ℝ) : EReal)) atTop = ℓ :=
    le_antisymm hlow_le hxeq
  have hsupeq : limsup (fun n => ((X n x / n : ℝ) : EReal)) atTop = ℓ := rfl
  have htend : Tendsto (fun n => ((X n x / n : ℝ) : EReal)) atTop (𝓝 ℓ) :=
    tendsto_of_liminf_eq_limsup hloweq hsupeq
  have hℓr : ℓ = ((ℓ.toReal : ℝ) : EReal) := (EReal.coe_toReal hxtop.ne hxbot.ne').symm
  rw [hℓr, EReal.tendsto_coe] at htend
  exact htend

omit [IsFiniteMeasure μ] in








theorem limit_le_comp_of_tendsto (h : SubadditiveCocycle T μ X) {ℓ : α → ℝ}
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (ℓ x))) :
    ∀ᵐ x ∂μ, ℓ x ≤ ℓ (T x) := by
  have hconvT : ∀ᵐ x ∂μ, Tendsto (fun n => X n (T x) / n) atTop (𝓝 (ℓ (T x))) :=
    h.measurePreserving.quasiMeasurePreserving.ae hconv
  have hsub : ∀ᵐ x ∂μ, ∀ n, X (n + 1) x ≤ X 1 x + X n (T x) := by
    rw [ae_all_iff]; intro n
    filter_upwards [h.subadditive 1 n] with x hx
    rw [show 1 + n = n + 1 by ring] at hx; simpa using hx
  filter_upwards [hconv, hconvT, hsub] with x hx hxT hxsub
  have hL : Tendsto (fun n => X (n + 1) x / ((n : ℝ) + 1)) atTop (𝓝 (ℓ x)) := by
    have hc := hx.comp (tendsto_add_atTop_nat 1)
    refine hc.congr (fun n => ?_); simp [Function.comp_apply]
  have hR : Tendsto (fun n : ℕ => X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * (X n (T x) / n)) atTop
      (𝓝 (ℓ (T x))) := by
    have h1 : Tendsto (fun n : ℕ => X 1 x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := X 1 x)).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (n + 1) = 1 - 1 / ((n : ℝ) + 1) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp; ring
      rw [tendsto_congr' key]
      have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
    have hsum := h1.add (h2.mul hxT)
    simpa using hsum
  have hle : (fun n => X (n + 1) x / ((n : ℝ) + 1)) ≤ᶠ[atTop]
      (fun n : ℕ => X 1 x / (n + 1) + ((n : ℝ) / (n + 1)) * (X n (T x) / n)) := by
    filter_upwards [eventually_gt_atTop 0] with n hpos
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    have hXle : X (n + 1) x ≤ X 1 x + X n (T x) := hxsub n
    rw [show ((n : ℝ) / (n + 1)) * (X n (T x) / n) = X n (T x) / (n + 1) by field_simp,
        ← add_div, div_le_div_iff_of_pos_right hn1]
    linarith
  exact le_of_tendsto_of_tendsto hL hR hle








theorem kingmanLimit_comp_ae (h : SubadditiveCocycle T μ X)
    (heq : ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x)
    (hbot : ∀ᵐ x ∂μ, ⊥ < gStar T X x)
    (hint : Integrable (kingmanLimit T X) μ) :
    ∀ᵐ x ∂μ, kingmanLimit T X (T x) = kingmanLimit T X x := by
  have hconv := tendsto_div_kingmanLimit_ae h heq hbot
  have hsub : ∀ᵐ x ∂μ, kingmanLimit T X x ≤ kingmanLimit T X (T x) :=
    limit_le_comp_of_tendsto h hconv
  
  set ℓ := kingmanLimit T X with hℓ
  have hintT : Integrable (fun x => ℓ (T x)) μ :=
    h.measurePreserving.integrable_comp_of_integrable hint
  have hge : 0 ≤ᵐ[μ] (fun x => ℓ (T x) - ℓ x) := by
    filter_upwards [hsub] with x hx; simp only [Pi.zero_apply]; linarith
  have heqint : ∫ x, ℓ (T x) ∂μ = ∫ x, ℓ x ∂μ :=
    Kingman.integral_comp_measurePreserving T h.measurePreserving ℓ hint.aestronglyMeasurable
  have hz : ∫ x, (ℓ (T x) - ℓ x) ∂μ = 0 := by
    rw [integral_sub hintT hint, heqint, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hge (hintT.sub hint)).mp hz
  filter_upwards [hae] with x hx
  simp only [Pi.zero_apply] at hx
  linarith



omit [IsFiniteMeasure μ] in

theorem aemeasurable_gStar (h : SubadditiveCocycle T μ X) : AEMeasurable (gStar T X) μ := by
  have hA : ∀ n, AEMeasurable (fun x => ((X n x / n : ℝ) : EReal)) μ := fun n =>
    measurable_coe_real_ereal.comp_aemeasurable
      ((h.integrable n).aestronglyMeasurable.aemeasurable.div_const _)
  refine ⟨fun x => limsup (fun n => (hA n).mk _ x) atTop,
    Measurable.limsup (fun n => (hA n).measurable_mk), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, ((X n x / n : ℝ) : EReal) = (hA n).mk _ x := by
    rw [ae_all_iff]; exact fun n => (hA n).ae_eq_mk
  filter_upwards [hall] with x hx
  unfold gStar
  exact limsup_congr (Eventually.of_forall fun n => hx n)

omit [IsFiniteMeasure μ] in

theorem aemeasurable_kingmanLimit (h : SubadditiveCocycle T μ X) :
    AEMeasurable (kingmanLimit T X) μ :=
  (aemeasurable_gStar h).ereal_toReal

omit [IsFiniteMeasure μ] in

theorem gStar_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] X n) : ∀ᵐ x ∂μ, (0 : EReal) ≤ gStar T X x := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ X n x := by rw [ae_all_iff]; exact hnn
  filter_upwards [hall] with x hx
  unfold gStar
  refine le_limsup_of_frequently_le (Frequently.of_forall (fun n => ?_)) (by isBoundedDefault)
  have hnn' : (0 : ℝ) ≤ X n x / n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · exact div_nonneg (hx n) (by positivity)
  exact_mod_cast hnn'

omit [IsFiniteMeasure μ] in

theorem kingmanLimit_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, 0 ≤ kingmanLimit T X x := by
  filter_upwards [gStar_nonneg_ae (T := T) hnn] with x hx
  exact EReal.toReal_nonneg hx


theorem kingmanLimit_le_birkhoffLimit_ae (h : SubadditiveCocycle T μ X)
    (hnn : ∀ n, 0 ≤ᵐ[μ] X n) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ x ∂μ, kingmanLimit T X x ≤ birkhoffLimit (T^[k]) (X k) x / k := by
  filter_upwards [gStar_le h hk, gStar_nonneg_ae (T := T) hnn] with x hx hg0
  have hbot : gStar T X x ≠ ⊥ := (lt_of_lt_of_le EReal.bot_lt_zero hg0).ne'
  have htop : ((birkhoffLimit (T^[k]) (X k) x / k : ℝ) : EReal) ≠ ⊤ := by simp
  have hmono := EReal.toReal_le_toReal hx hbot htop
  simpa [kingmanLimit] using hmono



theorem integrable_kingmanLimit (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    Integrable (kingmanLimit T X) μ := by
  have hTk : MeasurePreserving (T^[1]) μ μ := h.measurePreserving.iterate 1
  have hB : Integrable (fun x => birkhoffLimit (T^[1]) (X 1) x / 1) μ :=
    (integrable_birkhoffLimit hTk (h.integrable 1)).div_const (1 : ℝ)
  refine Integrable.mono' hB (aemeasurable_kingmanLimit h).aestronglyMeasurable ?_
  filter_upwards [kingmanLimit_nonneg_ae (T := T) hnn,
    kingmanLimit_le_birkhoffLimit_ae h hnn (k := 1) le_rfl] with x hpos hub
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  simpa using hub



theorem integral_birkhoffLimit_block (h : SubadditiveCocycle T μ X) (k : ℕ) :
    ∫ x, birkhoffLimit (T^[k]) (X k) x ∂μ = ∫ x, X k x ∂μ := by
  have hTk : MeasurePreserving (T^[k]) μ μ := h.measurePreserving.iterate k
  have hinv : IsInvariantSet (T^[k]) Set.univ := fun x => by simp
  simpa using (setIntegral_birkhoffLimit hTk (h.integrable k) MeasurableSet.univ hinv).symm






theorem integral_kingmanLimit_le_div (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
    {k : ℕ} (hk : 1 ≤ k) :
    (∫ x, kingmanLimit T X x ∂μ) ≤ (∫ x, X k x ∂μ) / k := by
  have hTk : MeasurePreserving (T^[k]) μ μ := h.measurePreserving.iterate k
  have hBint : Integrable (fun x => birkhoffLimit (T^[k]) (X k) x) μ :=
    integrable_birkhoffLimit hTk (h.integrable k)
  calc (∫ x, kingmanLimit T X x ∂μ)
      ≤ ∫ x, birkhoffLimit (T^[k]) (X k) x / k ∂μ :=
        integral_mono_ae (integrable_kingmanLimit h hnn) (hBint.div_const k)
          (kingmanLimit_le_birkhoffLimit_ae h hnn hk)
    _ = (∫ x, birkhoffLimit (T^[k]) (X k) x ∂μ) / k := integral_div _ _
    _ = (∫ x, X k x ∂μ) / k := by rw [integral_birkhoffLimit_block h k]








theorem integral_kingmanLimit_le_gamma (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    (∫ x, kingmanLimit T X x ∂μ) ≤ SubadditiveCocycle.gamma h := by
  unfold SubadditiveCocycle.gamma Subadditive.lim
  refine le_csInf ⟨SubadditiveCocycle.expSeq X μ 1 / 1, ⟨1, by simp⟩⟩ ?_
  rintro b ⟨n, hn, rfl⟩
  exact integral_kingmanLimit_le_div h hnn hn

end KingmanAE

end StatMech
