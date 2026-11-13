/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























import Mathlib
import Code.Foundations.Kingman
import Code.Foundations.BirkhoffPointwise
import Code.Foundations.KingmanAE

open MeasureTheory Filter Topology

namespace StatMech

namespace KingmanFilling

open Kingman BirkhoffAE KingmanAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {X : ℕ → α → ℝ}




noncomputable def gLow (T : α → α) (X : ℕ → α → ℝ) (x : α) : ℝ := (gStarLow T X x).toReal


theorem aemeasurable_gStarLow (h : SubadditiveCocycle T μ X) : AEMeasurable (gStarLow T X) μ := by
  have hA : ∀ n, AEMeasurable (fun x => ((X n x / n : ℝ) : EReal)) μ := fun n =>
    measurable_coe_real_ereal.comp_aemeasurable
      ((h.integrable n).aestronglyMeasurable.aemeasurable.div_const _)
  refine ⟨fun x => liminf (fun n => (hA n).mk _ x) atTop,
    Measurable.liminf (fun n => (hA n).measurable_mk), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, ((X n x / n : ℝ) : EReal) = (hA n).mk _ x := by
    rw [ae_all_iff]; exact fun n => (hA n).ae_eq_mk
  filter_upwards [hall] with x hx
  unfold gStarLow
  exact liminf_congr (Eventually.of_forall fun n => hx n)


theorem aemeasurable_gLow (h : SubadditiveCocycle T μ X) :
    AEMeasurable (gLow T X) μ :=
  (aemeasurable_gStarLow h).ereal_toReal


theorem gStarLow_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, (0 : EReal) ≤ gStarLow T X x := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ X n x := by rw [ae_all_iff]; exact hnn
  filter_upwards [hall] with x hx
  unfold gStarLow
  refine le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (fun n => ?_))
  have hnn' : (0 : ℝ) ≤ X n x / n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · exact div_nonneg (hx n) (by positivity)
  exact_mod_cast hnn'


theorem gLow_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, 0 ≤ gLow T X x := by
  filter_upwards [gStarLow_nonneg_ae (T := T) hnn] with x hx
  exact EReal.toReal_nonneg hx



theorem eq_of_le_toReal_eq {x y : EReal} (hle : x ≤ y) (hxbot : x ≠ ⊥) (hytop : y ≠ ⊤)
    (heq : x.toReal = y.toReal) : x = y := by
  have hxtop : x ≠ ⊤ := fun hh => hytop (top_le_iff.mp (hh ▸ hle))
  have hybot : y ≠ ⊥ := fun hh => hxbot (le_bot_iff.mp (hh ▸ hle))
  rw [← EReal.coe_toReal hxtop hxbot, ← EReal.coe_toReal hytop hybot, heq]










theorem gStarLow_le_comp (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, gStarLow T X x ≤ gStarLow T X (T x) := by
  have hsub : ∀ᵐ x ∂μ, ∀ n, X (n + 1) x ≤ X 1 x + X n (T x) := by
    rw [ae_all_iff]; intro n
    filter_upwards [h.subadditive 1 n] with x hx
    rw [show 1 + n = n + 1 by ring] at hx; simpa using hx
  filter_upwards [hsub] with x hx
  rw [show gStarLow T X (T x) = liminf (fun n => ((X n (T x) / n : ℝ) : EReal)) atTop from rfl,
     le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)]
  intro y hyL
  obtain ⟨z, hyz, hzL⟩ := EReal.lt_iff_exists_real_btwn.mp hyL
  have hzL' : (z : EReal) < liminf (fun n => ((X n x / n : ℝ) : EReal)) atTop := hzL
  have h0 : ∀ᶠ n in atTop, (z : EReal) < ((X n x / n : ℝ) : EReal) :=
    eventually_lt_of_lt_liminf hzL'
  have hev : ∀ᶠ n in atTop, z < X n x / n := by
    filter_upwards [h0] with n hn; exact_mod_cast hn
  have hev1 : ∀ᶠ n in atTop, z < X (n+1) x / ((n:ℝ)+1) := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hev] with n hn
    rwa [Nat.cast_add_one] at hn
  have hr : Tendsto (fun n : ℕ => (((n:ℝ)+1)/n) * z - X 1 x / n) atTop (𝓝 z) := by
    have h1 : Tendsto (fun n : ℕ => ((n:ℝ)+1)/n) atTop (𝓝 1) := by
      have key : ∀ᶠ n : ℕ in atTop, ((n:ℝ)+1)/n = 1 + 1/(n:ℝ) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have : (n:ℝ) ≠ 0 := by positivity
        field_simp
      rw [tendsto_congr' key]
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => X 1 x / (n:ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := X 1 x)).div_atTop tendsto_natCast_atTop_atTop
    simpa using (h1.mul tendsto_const_nhds).sub h2
  rcases eq_or_ne y ⊥ with hyb | hyb
  · subst hyb
    filter_upwards with n
    exact bot_lt_iff_ne_bot.mpr (by simp)
  · have hytop : y ≠ ⊤ := fun hh => by rw [hh] at hyz; exact (not_top_lt hyz)
    have hyeq : (y.toReal : EReal) = y := EReal.coe_toReal hytop hyb
    have hyr : y.toReal < z := by rw [← hyeq] at hyz; exact_mod_cast hyz
    have hrlt : ∀ᶠ n : ℕ in atTop, y.toReal < (((n:ℝ)+1)/n)*z - X 1 x / n :=
      hr.eventually (eventually_gt_nhds hyr)
    filter_upwards [hev1, hrlt, eventually_gt_atTop 0] with n hn1 hn2 hpos
    have hnn : (0:ℝ) < n := by exact_mod_cast hpos
    have hXle : X (n+1) x ≤ X 1 x + X n (T x) := hx n
    have hXn1 : ((n:ℝ)+1) * z < X (n+1) x := by
      rw [lt_div_iff₀ (by positivity)] at hn1; linarith [hn1]
    have hXnT : ((n:ℝ)+1)*z - X 1 x < X n (T x) := by linarith [hXle, hXn1]
    have hgoal : y.toReal < X n (T x) / n := by
      rw [lt_div_iff₀ hnn]
      have hmul : y.toReal * n < ((((n:ℝ)+1)/n)*z - X 1 x/n) * n :=
        mul_lt_mul_of_pos_right hn2 hnn
      have hrhs : ((((n:ℝ)+1)/n)*z - X 1 x/n) * n = ((n:ℝ)+1)*z - X 1 x := by
        field_simp
      rw [hrhs] at hmul; linarith [hXnT, hmul]
    rw [← hyeq]; exact_mod_cast hgoal









def badSet (T : α → α) (X : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) : Set α :=
  {x | ∀ m, 1 ≤ m → m ≤ N → (gLow T X x + ε) * m < X m x}





noncomputable def dep (T : α → α) (X : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) (y : α) : ℝ :=
  gLow T X y + ε + (badSet T X ε N).indicator (fun z => X 1 z) y



noncomputable def badCost (T : α → α) (X : ℕ → α → ℝ) (ε : ℝ) (N : ℕ) (x : α) : ℝ :=
  (badSet T X ε N).indicator (fun z => X 1 z) x

omit [MeasurableSpace α] in

theorem dep_nonneg {ε : ℝ} {N : ℕ} {y : α} (hg : 0 ≤ gLow T X y) (hε : 0 ≤ ε)
    (hx1 : 0 ≤ X 1 y) : 0 ≤ dep T X ε N y := by
  unfold dep
  have : 0 ≤ (badSet T X ε N).indicator (fun z => X 1 z) y := by
    rcases em (y ∈ badSet T X ε N) with hy | hy
    · rw [Set.indicator_of_mem hy]; exact hx1
    · rw [Set.indicator_of_notMem hy]
  linarith



omit [MeasurableSpace α] in










theorem greedy (ε : ℝ) (N : ℕ) (hN : 1 ≤ N) (x : α)
    (hsub : ∀ s a b, X (a + b) (T^[s] x) ≤ X a (T^[s] x) + X b (T^[a + s] x))
    (hmono : ∀ i j, i ≤ j → gLow T X (T^[i] x) ≤ gLow T X (T^[j] x))
    (hgnn : ∀ i, 0 ≤ gLow T X (T^[i] x))
    (hx1nn : ∀ i, 0 ≤ X 1 (T^[i] x))
    (hεnn : 0 ≤ ε)
    (hrem : ∀ i n, n < N → X n (T^[i] x) ≤ remDom X N (T^[i] x)) :
    ∀ n s, ∃ m, m ≤ n ∧ n ≤ m + N ∧
      X n (T^[s] x) ≤ (∑ j ∈ Finset.range n, dep T X ε N (T^[s + j] x))
        + remDom X N (T^[s + m] x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine ⟨0, le_refl _, by omega, ?_⟩
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.add_zero]
      exact hrem s 0 hN
    by_cases hbad : T^[s] x ∈ badSet T X ε N
    · 
      have h1 : X n (T^[s] x) ≤ X 1 (T^[s] x) + X (n-1) (T^[1 + s] x) := by
        have := hsub s 1 (n-1)
        rwa [show 1 + (n-1) = n by omega] at this
      obtain ⟨m', hm'1, hm'2, hbound⟩ := ih (n-1) (by omega) (s+1)
      refine ⟨1 + m', by omega, by omega, ?_⟩
      have hsplit : (∑ j ∈ Finset.range n, dep T X ε N (T^[s + j] x))
          = dep T X ε N (T^[s] x) + ∑ j ∈ Finset.range (n-1), dep T X ε N (T^[(s+1) + j] x) := by
        have hr := Finset.sum_range_add (fun j => dep T X ε N (T^[s + j] x)) 1 (n-1)
        rw [show (1 + (n-1)) = n by omega] at hr
        rw [hr]; congr 1
        · simp
        · apply Finset.sum_congr rfl; intro j _; congr 2; omega
      rw [hsplit]
      have hdep0 : X 1 (T^[s] x) ≤ dep T X ε N (T^[s] x) := by
        unfold dep
        rw [Set.indicator_of_mem hbad]
        have : 0 ≤ gLow T X (T^[s] x) + ε := by have := hgnn s; linarith
        linarith
      have hremeq : remDom X N (T^[(s+1) + m'] x) = remDom X N (T^[s + (1 + m')] x) := by
        congr 2; omega
      have hxeq : X (n-1) (T^[1+s] x) = X (n-1) (T^[s+1] x) := by congr 2; omega
      rw [hxeq] at h1
      calc X n (T^[s] x) ≤ X 1 (T^[s] x) + X (n-1) (T^[s+1] x) := h1
        _ ≤ dep T X ε N (T^[s] x) +
            ((∑ j ∈ Finset.range (n-1), dep T X ε N (T^[(s+1)+j] x))
              + remDom X N (T^[(s+1)+m'] x)) := by gcongr
        _ = (dep T X ε N (T^[s] x) + ∑ j ∈ Finset.range (n-1), dep T X ε N (T^[(s+1)+j] x))
            + remDom X N (T^[s+(1+m')] x) := by rw [hremeq]; ring
    · 
      simp only [badSet, Set.mem_setOf_eq, not_forall, not_lt] at hbad
      obtain ⟨len, hlen1, hlen2, hgood⟩ := hbad
      by_cases hfit : len ≤ n
      · have h1 : X n (T^[s] x) ≤ X len (T^[s] x) + X (n-len) (T^[len + s] x) := by
          have := hsub s len (n-len)
          rwa [show len + (n-len) = n by omega] at this
        obtain ⟨m', hm'1, hm'2, hbound⟩ := ih (n-len) (by omega) (s+len)
        refine ⟨len + m', by omega, by omega, ?_⟩
        have hspread : X len (T^[s] x) ≤ ∑ j ∈ Finset.range len, dep T X ε N (T^[s + j] x) := by
          calc X len (T^[s] x) ≤ (gLow T X (T^[s] x) + ε) * len := hgood
            _ = ∑ _j ∈ Finset.range len, (gLow T X (T^[s] x) + ε) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
            _ ≤ ∑ j ∈ Finset.range len, (gLow T X (T^[s+j] x) + ε) := by
                  apply Finset.sum_le_sum; intro j hj
                  have : gLow T X (T^[s] x) ≤ gLow T X (T^[s+j] x) := hmono s (s+j) (by omega)
                  linarith
            _ ≤ ∑ j ∈ Finset.range len, dep T X ε N (T^[s+j] x) := by
                  apply Finset.sum_le_sum; intro j hj
                  unfold dep
                  have : 0 ≤ (badSet T X ε N).indicator (fun z => X 1 z) (T^[s+j] x) := by
                    rcases em (T^[s+j] x ∈ badSet T X ε N) with hy | hy
                    · rw [Set.indicator_of_mem hy]; exact hx1nn (s+j)
                    · rw [Set.indicator_of_notMem hy]
                  linarith
        have hsplit : (∑ j ∈ Finset.range n, dep T X ε N (T^[s + j] x))
            = (∑ j ∈ Finset.range len, dep T X ε N (T^[s+j] x))
              + ∑ j ∈ Finset.range (n-len), dep T X ε N (T^[(s+len) + j] x) := by
          have hr := Finset.sum_range_add (fun j => dep T X ε N (T^[s + j] x)) len (n-len)
          rw [show (len + (n-len)) = n by omega] at hr
          rw [hr]; congr 1
          apply Finset.sum_congr rfl; intro j _; congr 2; omega
        rw [hsplit]
        have hremeq : remDom X N (T^[(s+len) + m'] x) = remDom X N (T^[s + (len + m')] x) := by
          congr 2; omega
        have hxeq : X (n-len) (T^[len+s] x) = X (n-len) (T^[s+len] x) := by congr 2; omega
        rw [hxeq] at h1
        calc X n (T^[s] x) ≤ X len (T^[s] x) + X (n-len) (T^[s+len] x) := h1
          _ ≤ (∑ j ∈ Finset.range len, dep T X ε N (T^[s+j] x)) +
              ((∑ j ∈ Finset.range (n-len), dep T X ε N (T^[(s+len)+j] x))
                + remDom X N (T^[(s+len)+m'] x)) := by gcongr
          _ = ((∑ j ∈ Finset.range len, dep T X ε N (T^[s+j] x))
                + ∑ j ∈ Finset.range (n-len), dep T X ε N (T^[(s+len)+j] x))
              + remDom X N (T^[s+(len+m')] x) := by rw [hremeq]; ring
      · 
        refine ⟨0, Nat.zero_le _, by omega, ?_⟩
        have hnN : n < N := by omega
        have hsum0 : (0:ℝ) ≤ ∑ j ∈ Finset.range n, dep T X ε N (T^[s+j] x) := by
          apply Finset.sum_nonneg; intro j _
          exact dep_nonneg (hgnn (s+j)) hεnn (hx1nn (s+j))
        simp only [Nat.add_zero]
        calc X n (T^[s] x) ≤ remDom X N (T^[s] x) := hrem s n hnN
          _ ≤ (∑ j ∈ Finset.range n, dep T X ε N (T^[s+j] x)) + remDom X N (T^[s] x) := by linarith

omit [MeasurableSpace α] in





theorem greedy_windowed (ε : ℝ) (N : ℕ) (hN : 1 ≤ N) (x : α)
    (hsub : ∀ s a b, X (a + b) (T^[s] x) ≤ X a (T^[s] x) + X b (T^[a + s] x))
    (hmono : ∀ i j, i ≤ j → gLow T X (T^[i] x) ≤ gLow T X (T^[j] x))
    (hgnn : ∀ i, 0 ≤ gLow T X (T^[i] x))
    (hx1nn : ∀ i, 0 ≤ X 1 (T^[i] x))
    (hεnn : 0 ≤ ε)
    (hremnn : ∀ t, 0 ≤ remDom X N (T^[t] x)) (n : ℕ) :
    X n x ≤ (∑ j ∈ Finset.range n, dep T X ε N (T^[j] x))
      + ∑ t ∈ Finset.Icc (n-N) n, remDom X N (T^[t] x) := by
  have hrem : ∀ i n, n < N → X n (T^[i] x) ≤ remDom X N (T^[i] x) :=
    fun i n hn => le_remDom X hn (T^[i] x)
  obtain ⟨m, hm1, hm2, hbound⟩ := greedy ε N hN x hsub hmono hgnn hx1nn hεnn hrem n 0
  simp only [Nat.zero_add] at hbound
  refine le_trans hbound ?_
  gcongr
  apply Finset.single_le_sum (f := fun t => remDom X N (T^[t] x)) (fun t _ => hremnn t)
  rw [Finset.mem_Icc]; omega

variable [IsFiniteMeasure μ]



theorem gLow_le_kingmanLimit_ae (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, gLow T X x ≤ kingmanLimit T X x := by
  filter_upwards [gStarLow_nonneg_ae (T := T) hnn, gStar_lt_top_ae h] with x hg0 htop
  have hlow_le : gStarLow T X x ≤ gStar T X x := gStarLow_le_gStar x
  have hlowbot : gStarLow T X x ≠ ⊥ := (lt_of_lt_of_le EReal.bot_lt_zero hg0).ne'
  exact EReal.toReal_le_toReal hlow_le hlowbot htop.ne



theorem integrable_gLow (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    Integrable (gLow T X) μ := by
  refine Integrable.mono' (integrable_kingmanLimit h hnn)
    (aemeasurable_gLow h).aestronglyMeasurable ?_
  filter_upwards [gLow_nonneg_ae (T := T) hnn, gLow_le_kingmanLimit_ae h hnn,
    kingmanLimit_nonneg_ae (T := T) hnn] with x hpos hub hkpos
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  exact hub







theorem gLow_orbit_mono (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, ∀ i j, i ≤ j → gLow T X (T^[i] x) ≤ gLow T X (T^[j] x) := by
  have hstep : ∀ᵐ x ∂μ, ∀ i, gStarLow T X (T^[i] x) ≤ gStarLow T X (T^[i+1] x) := by
    rw [ae_all_iff]; intro i
    have := (h.measurePreserving.iterate i).quasiMeasurePreserving.ae (gStarLow_le_comp h)
    filter_upwards [this] with x hx
    rw [show T^[i+1] x = T (T^[i] x) by rw [Function.iterate_succ_apply']]
    exact hx
  have hnn' : ∀ᵐ x ∂μ, ∀ i, (0 : EReal) ≤ gStarLow T X (T^[i] x) := by
    rw [ae_all_iff]; intro i
    exact (h.measurePreserving.iterate i).quasiMeasurePreserving.ae
      (gStarLow_nonneg_ae (T := T) (μ := μ) hnn)
  have htop' : ∀ᵐ x ∂μ, ∀ i, gStarLow T X (T^[i] x) < ⊤ := by
    rw [ae_all_iff]; intro i
    have := (h.measurePreserving.iterate i).quasiMeasurePreserving.ae (gStar_lt_top_ae h)
    filter_upwards [this] with x hx
    exact lt_of_le_of_lt (gStarLow_le_gStar _) hx
  filter_upwards [hstep, hnn', htop'] with x hstepx hnnx htopx
  have hchain : ∀ i j, i ≤ j → gStarLow T X (T^[i] x) ≤ gStarLow T X (T^[j] x) := by
    have key : ∀ i d, gStarLow T X (T^[i] x) ≤ gStarLow T X (T^[i + d] x) := by
      intro i d
      induction d with
      | zero => simp
      | succ k ih =>
        calc gStarLow T X (T^[i] x) ≤ gStarLow T X (T^[i + k] x) := ih
          _ ≤ gStarLow T X (T^[(i + k) + 1] x) := hstepx (i + k)
          _ = gStarLow T X (T^[i + (k+1)] x) := by ring_nf
    intro i j hij
    obtain ⟨d, rfl⟩ := Nat.le.dest hij
    exact key i d
  intro i j hij
  exact EReal.toReal_le_toReal (hchain i j hij)
    (lt_of_lt_of_le EReal.bot_lt_zero (hnnx i)).ne' (htopx j).ne



omit [IsFiniteMeasure μ] in


theorem nullMeasurableSet_badSet (h : SubadditiveCocycle T μ X) (ε : ℝ) (N : ℕ) :
    NullMeasurableSet (badSet T X ε N) μ := by
  have hset : badSet T X ε N
      = ⋂ m ∈ Finset.Icc 1 N, {x | (gLow T X x + ε) * (m:ℝ) < X m x} := by
    ext x
    simp only [badSet, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_Icc]
    exact ⟨fun hx m hm => hx m hm.1 hm.2, fun hx m hm1 hm2 => hx m ⟨hm1, hm2⟩⟩
  rw [hset]
  refine MeasureTheory.NullMeasurableSet.biInter (Set.to_countable _) (fun m _ => ?_)
  exact nullMeasurableSet_lt (((aemeasurable_gLow h).add_const ε).mul_const _)
    (h.integrable m).aestronglyMeasurable.aemeasurable


theorem integrable_dep (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) (ε : ℝ) (N : ℕ) :
    Integrable (dep T X ε N) μ := by
  unfold dep
  exact ((integrable_gLow h hnn).add (integrable_const ε)).add
    ((h.integrable 1).indicator₀ (nullMeasurableSet_badSet h ε N))

omit [IsFiniteMeasure μ] in

theorem integrable_badCost (h : SubadditiveCocycle T μ X) (ε : ℝ) (N : ℕ) :
    Integrable (badCost T X ε N) μ :=
  (h.integrable 1).indicator₀ (nullMeasurableSet_badSet h ε N)





theorem gStarLow_finite_ae (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, gStarLow T X x ≠ ⊥ ∧ gStarLow T X x ≠ ⊤ := by
  filter_upwards [gStarLow_nonneg_ae (T := T) hnn, gStar_lt_top_ae h] with x hg0 htop
  exact ⟨(lt_of_lt_of_le EReal.bot_lt_zero hg0).ne',
    (lt_of_le_of_lt (gStarLow_le_gStar x) htop).ne⟩






theorem exists_good (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∃ m, 1 ≤ m ∧ X m x ≤ (gLow T X x + ε) * m := by
  filter_upwards [gStarLow_finite_ae h hnn] with x ⟨hbot, htop⟩
  have hreal : gStarLow T X x = ((gLow T X x : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
  have hlt : (gStarLow T X x) < ((gLow T X x + ε : ℝ) : EReal) := by
    rw [hreal]; exact_mod_cast (by linarith : gLow T X x < gLow T X x + ε)
  have hfreq : ∃ᶠ m in atTop, ((X m x / m : ℝ) : EReal) < ((gLow T X x + ε : ℝ) : EReal) :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  have hfreq' : ∃ᶠ m in atTop, 1 ≤ m ∧ X m x / m < gLow T X x + ε := by
    refine hfreq.mp ?_
    filter_upwards [eventually_ge_atTop 1] with m hm hlt'
    exact ⟨hm, by exact_mod_cast hlt'⟩
  obtain ⟨m, hm1, hmlt⟩ := hfreq'.exists
  refine ⟨m, hm1, ?_⟩
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm1
  rw [div_lt_iff₀ hm0] at hmlt
  linarith [hmlt]





theorem tendsto_integral_badCost (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => ∫ x, badCost T X ε N x ∂μ) atTop (𝓝 0) := by
  have hptw : ∀ᵐ x ∂μ, Tendsto (fun N => badCost T X ε N x) atTop (𝓝 0) := by
    filter_upwards [exists_good h hnn hε] with x ⟨m0, hm01, hgood⟩
    apply tendsto_atTop_of_eventually_const (i₀ := m0)
    intro N hN
    have hxnotbad : x ∉ badSet T X ε N := by
      simp only [badSet, Set.mem_setOf_eq, not_forall, not_lt]
      exact ⟨m0, hm01, hN, hgood⟩
    unfold badCost; rw [Set.indicator_of_notMem hxnotbad]
  have hmeas : ∀ N, AEStronglyMeasurable (fun x => badCost T X ε N x) μ :=
    fun N => (integrable_badCost h ε N).aestronglyMeasurable
  have hdom : ∀ N, ∀ᵐ x ∂μ, ‖badCost T X ε N x‖ ≤ |X 1 x| := by
    intro N
    filter_upwards with x
    unfold badCost
    rcases em (x ∈ badSet T X ε N) with hx | hx
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
    · rw [Set.indicator_of_notMem hx]; simp
  simpa using tendsto_integral_of_dominated_convergence (fun x => |X 1 x|) hmeas
    (h.integrable 1).abs hdom hptw



omit [IsFiniteMeasure μ] in


theorem ae_all_subadditive_orbit (h : SubadditiveCocycle T μ X) :
    ∀ᵐ x ∂μ, ∀ s a b, X (a + b) (T^[s] x) ≤ X a (T^[s] x) + X b (T^[a + s] x) := by
  have horb : ∀ᵐ x ∂μ, ∀ s, ∀ a b, X (a+b) (T^[s] x) ≤ X a (T^[s] x) + X b (T^[a] (T^[s] x)) := by
    rw [ae_all_iff]; intro s
    exact (h.measurePreserving.iterate s).quasiMeasurePreserving.ae (ae_all_subadditive h)
  filter_upwards [horb] with x hx
  intro s a b
  have := hx s a b
  rwa [← Function.iterate_add_apply] at this

omit [IsFiniteMeasure μ] in

theorem ae_orbit_nonneg (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, (∀ i, 0 ≤ gLow T X (T^[i] x)) ∧ (∀ i, 0 ≤ X 1 (T^[i] x)) := by
  have hg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ gLow T X (T^[i] x) := by
    rw [ae_all_iff]; intro i
    exact (h.measurePreserving.iterate i).quasiMeasurePreserving.ae (gLow_nonneg_ae (T := T) hnn)
  have h1 : ∀ᵐ x ∂μ, ∀ i, 0 ≤ X 1 (T^[i] x) := by
    rw [ae_all_iff]; intro i
    exact (h.measurePreserving.iterate i).quasiMeasurePreserving.ae (hnn 1)
  filter_upwards [hg, h1] with x hgx h1x using ⟨hgx, h1x⟩








theorem per_n_integral (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
    {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    SubadditiveCocycle.expSeq X μ n
      ≤ n * (∫ x, dep T X ε N x ∂μ) + (N + 1) * ∫ x, remDom X N x ∂μ := by
  have hdepsum_int : Integrable (fun x => ∑ j ∈ Finset.range n, dep T X ε N (T^[j] x)) μ := by
    apply integrable_finsetSum
    intro j _
    exact (h.measurePreserving.iterate j).integrable_comp_of_integrable (integrable_dep h hnn ε N)
  have hwin_int : Integrable (fun x => ∑ t ∈ Finset.Icc (n-N) n, remDom X N (T^[t] x)) μ := by
    apply integrable_finsetSum
    intro t _
    exact (h.measurePreserving.iterate t).integrable_comp_of_integrable (remDom_integrable h N)
  
  have hmono : SubadditiveCocycle.expSeq X μ n
      ≤ ∫ x, ((∑ j ∈ Finset.range n, dep T X ε N (T^[j] x))
          + ∑ t ∈ Finset.Icc (n-N) n, remDom X N (T^[t] x)) ∂μ := by
    refine integral_mono_ae (h.integrable n) (hdepsum_int.add hwin_int) ?_
    filter_upwards [ae_all_subadditive_orbit h, gLow_orbit_mono h hnn, ae_orbit_nonneg h hnn]
      with x hsub hmonoo ⟨hgnn, hx1nn⟩
    exact greedy_windowed ε N hN x hsub hmonoo hgnn hx1nn hε
      (fun t => remDom_nonneg X N (T^[t] x)) n
  rw [integral_add hdepsum_int hwin_int] at hmono
  
  have hdsum : ∫ x, (∑ j ∈ Finset.range n, dep T X ε N (T^[j] x)) ∂μ
      = n * ∫ x, dep T X ε N x ∂μ := by
    rw [integral_finsetSum]
    · rw [Finset.sum_congr rfl (fun j _ => Kingman.integral_comp_iterate T h.measurePreserving
        (dep T X ε N) (integrable_dep h hnn ε N).aestronglyMeasurable j)]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro j _
      exact (h.measurePreserving.iterate j).integrable_comp_of_integrable
        (integrable_dep h hnn ε N)
  
  have hwin : ∫ x, (∑ t ∈ Finset.Icc (n-N) n, remDom X N (T^[t] x)) ∂μ
      = (Finset.Icc (n-N) n).card * ∫ x, remDom X N x ∂μ := by
    rw [integral_finsetSum]
    · rw [Finset.sum_congr rfl (fun t _ => Kingman.integral_comp_iterate T h.measurePreserving
        (remDom X N) (remDom_integrable h N).aestronglyMeasurable t)]
      rw [Finset.sum_const, nsmul_eq_mul]
    · intro t _
      exact (h.measurePreserving.iterate t).integrable_comp_of_integrable (remDom_integrable h N)
  rw [hdsum, hwin] at hmono
  have hcardN : (Finset.Icc (n-N) n).card ≤ N + 1 := by rw [Nat.card_Icc]; omega
  have hcard : ((Finset.Icc (n-N) n).card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hcardN
  have hremnn : 0 ≤ ∫ x, remDom X N x ∂μ := integral_nonneg (fun x => remDom_nonneg X N x)
  calc SubadditiveCocycle.expSeq X μ n
      ≤ ↑n * (∫ x, dep T X ε N x ∂μ)
        + ↑(Finset.Icc (n-N) n).card * ∫ x, remDom X N x ∂μ := hmono
    _ ≤ ↑n * (∫ x, dep T X ε N x ∂μ) + (N + 1) * ∫ x, remDom X N x ∂μ := by gcongr


theorem integral_dep_eq (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) (ε : ℝ) (N : ℕ) :
    ∫ x, dep T X ε N x ∂μ
      = (∫ x, gLow T X x ∂μ) + ε * (μ Set.univ).toReal + ∫ x, badCost T X ε N x ∂μ := by
  have he1 : Integrable (fun x => gLow T X x + ε) μ :=
    (integrable_gLow h hnn).add (integrable_const ε)
  have he2 : Integrable (fun x => (badSet T X ε N).indicator (fun z => X 1 z) x) μ :=
    (h.integrable 1).indicator₀ (nullMeasurableSet_badSet h ε N)
  have hsplit : ∫ x, dep T X ε N x ∂μ
      = (∫ x, (gLow T X x + ε) ∂μ) + ∫ x, (badSet T X ε N).indicator (fun z => X 1 z) x ∂μ := by
    rw [← integral_add he1 he2]; rfl
  rw [hsplit, integral_add (integrable_gLow h hnn) (integrable_const ε), integral_const]
  simp only [smul_eq_mul, Measure.real, badCost]
  ring





theorem gamma_le_integral_dep (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
    {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 1 ≤ N) :
    h.gamma ≤ ∫ x, dep T X ε N x ∂μ := by
  have hbdd : BddBelow (Set.range fun n => SubadditiveCocycle.expSeq X μ n / n) :=
    h.bddBelow_of_nonneg hnn
  have hconv : Tendsto (fun n => SubadditiveCocycle.expSeq X μ n / n) atTop (𝓝 h.gamma) :=
    h.tendsto_expSeq_div hbdd
  set D := ∫ x, dep T X ε N x ∂μ with hD
  set R := ∫ x, remDom X N x ∂μ with hR
  have hub : Tendsto (fun n : ℕ => D + (N+1)*R/n) atTop (𝓝 D) := by
    have : Tendsto (fun n : ℕ => (N+1)*R/(n:ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (N+1)*R)).div_atTop tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := D)).add this
  refine le_of_tendsto_of_tendsto hconv hub ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hpn := per_n_integral h hnn hε hN n
  rw [div_le_iff₀ hnn0]
  have hrw : (D + (N+1)*R/n)*n = n*D + (N+1)*R := by field_simp
  rw [hrw]; exact hpn


theorem gamma_le_integral_gLow_add_eps (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
    {ε : ℝ} (hε : 0 < ε) :
    h.gamma ≤ (∫ x, gLow T X x ∂μ) + ε * (μ Set.univ).toReal := by
  set G := ∫ x, gLow T X x ∂μ with hG
  set c := ε * (μ Set.univ).toReal with hc
  have hN : ∀ N : ℕ, 1 ≤ N → h.gamma ≤ G + c + ∫ x, badCost T X ε N x ∂μ := by
    intro N hN1
    have := gamma_le_integral_dep h hnn hε.le hN1
    rwa [integral_dep_eq h hnn ε N] at this
  have hlim : Tendsto (fun N : ℕ => G + c + ∫ x, badCost T X ε (N+1) x ∂μ) atTop (𝓝 (G + c)) := by
    have hbc := (tendsto_integral_badCost h hnn hε).comp (tendsto_add_atTop_nat 1)
    simpa using (tendsto_const_nhds (x := G + c)).add hbc
  refine ge_of_tendsto hlim ?_
  filter_upwards with N
  exact hN (N+1) (by omega)





theorem gamma_le_integral_gLow (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    h.gamma ≤ ∫ x, gLow T X x ∂μ := by
  set G := ∫ x, gLow T X x ∂μ with hG
  have hev : ∀ ε : ℝ, 0 < ε → h.gamma ≤ G + ε * (μ Set.univ).toReal :=
    fun ε hε => gamma_le_integral_gLow_add_eps h hnn hε
  have hlim : Tendsto (fun n : ℕ => G + (1/(n+1:ℝ)) * (μ Set.univ).toReal) atTop (𝓝 G) := by
    have h1 : Tendsto (fun n : ℕ => (1/(n+1:ℝ)) * (μ Set.univ).toReal) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1:ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using this.mul_const ((μ Set.univ).toReal)
    simpa using (tendsto_const_nhds (x := G)).add h1
  refine ge_of_tendsto hlim ?_
  filter_upwards with n
  exact hev (1/(n+1:ℝ)) (by positivity)











theorem gStar_le_gStarLow_ae_of_gamma_le_integral (h : SubadditiveCocycle T μ X)
    (hnn : ∀ n, 0 ≤ᵐ[μ] X n) (hgamma : h.gamma ≤ ∫ x, gLow T X x ∂μ) :
    ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x := by
  have hgLow_int : Integrable (gLow T X) μ := integrable_gLow h hnn
  have hkL_int : Integrable (kingmanLimit T X) μ := integrable_kingmanLimit h hnn
  
  have hle_int : (∫ x, gLow T X x ∂μ) ≤ ∫ x, kingmanLimit T X x ∂μ :=
    integral_mono_ae hgLow_int hkL_int (gLow_le_kingmanLimit_ae h hnn)
  
  have hkL_le_gamma : (∫ x, kingmanLimit T X x ∂μ) ≤ h.gamma :=
    integral_kingmanLimit_le_gamma h hnn
  have heq_int : (∫ x, gLow T X x ∂μ) = ∫ x, kingmanLimit T X x ∂μ :=
    le_antisymm hle_int (le_trans hkL_le_gamma hgamma)
  
  have hz : ∫ x, (kingmanLimit T X x - gLow T X x) ∂μ = 0 := by
    rw [integral_sub hkL_int hgLow_int, ← heq_int, sub_self]
  have hge : 0 ≤ᵐ[μ] (fun x => kingmanLimit T X x - gLow T X x) := by
    filter_upwards [gLow_le_kingmanLimit_ae h hnn] with x hx
    simp only [Pi.zero_apply]; linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hge (hkL_int.sub hgLow_int)).mp hz
  
  filter_upwards [hae, gStar_lt_top_ae h, gStarLow_nonneg_ae (T := T) hnn] with x hx htop hg0
  simp only [Pi.zero_apply] at hx
  have htoReal_eq : (gStar T X x).toReal = (gStarLow T X x).toReal := by
    simp only [kingmanLimit, gLow] at hx; linarith
  have hlow_le : gStarLow T X x ≤ gStar T X x := gStarLow_le_gStar x
  have hlowbot : gStarLow T X x ≠ ⊥ := (lt_of_lt_of_le EReal.bot_lt_zero hg0).ne'
  exact ge_of_eq (eq_of_le_toReal_eq hlow_le hlowbot htop.ne htoReal_eq.symm)










theorem gStar_le_gStarLow_ae (h : SubadditiveCocycle T μ X) (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x :=
  gStar_le_gStarLow_ae_of_gamma_le_integral h hnn (gamma_le_integral_gLow h hnn)












theorem tendsto_div_kingmanLimit_ae_of_nonneg (h : SubadditiveCocycle T μ X)
    (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
  have hbot : ∀ᵐ x ∂μ, ⊥ < gStar T X x := by
    filter_upwards [gStar_nonneg_ae (T := T) hnn] with x hx
    exact lt_of_lt_of_le EReal.bot_lt_zero hx
  exact tendsto_div_kingmanLimit_ae h (gStar_le_gStarLow_ae h hnn) hbot

end KingmanFilling

end StatMech

