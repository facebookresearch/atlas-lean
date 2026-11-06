/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.DickmanDeBruijn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Existence and uniqueness of the Dickman–de Bruijn function
-/

section
namespace Real

/-- Method-of-steps approximants for the Dickman–de Bruijn function. -/
private noncomputable def dickStep (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 - ∫ t in (1 : ℝ)..(max x 1), f (t - 1) / max t 1

private noncomputable def dickApprox : ℕ → (ℝ → ℝ)
  | 0 => fun _ => 1
  | n + 1 => dickStep (dickApprox n)

private lemma dickIntegrand_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun t : ℝ => f (t - 1) / max t 1) := by
  apply Continuous.div
  · exact hf.comp (continuous_id.sub continuous_const)
  · exact continuous_id.max continuous_const
  · intro t
    have h1 : (1 : ℝ) ≤ max t 1 := le_max_right _ _
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)

private lemma dickApprox_continuous (n : ℕ) : Continuous (dickApprox n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (dickStep _)
    unfold dickStep
    apply Continuous.sub continuous_const
    have hcont : Continuous (fun t : ℝ => dickApprox n (t - 1) / max t 1) :=
      dickIntegrand_continuous _ ih
    have hprim : Continuous (fun u : ℝ => ∫ t in (1 : ℝ)..u, dickApprox n (t - 1) / max t 1) := by
      rw [continuous_iff_continuousAt]
      intro u
      have hderiv : HasDerivAt
          (fun u => ∫ t in (1 : ℝ)..u, dickApprox n (t - 1) / max t 1)
          (dickApprox n (u - 1) / max u 1) u := by
        apply intervalIntegral.integral_hasDerivAt_right
        · exact (hcont.continuousOn).intervalIntegrable
        · exact hcont.stronglyMeasurableAtFilter _ _
        · exact hcont.continuousAt
      exact hderiv.continuousAt
    exact hprim.comp (continuous_id.max continuous_const)

private lemma dickApprox_eq_one_of_le_one : ∀ (n : ℕ) (x : ℝ), x ≤ 1 → dickApprox n x = 1
  | 0, x, _ => rfl
  | n + 1, x, hx => by
    simp only [dickApprox, dickStep]
    have hmax : max x 1 = 1 := max_eq_right hx
    rw [hmax]
    simp

private lemma dickApprox_agree_succ : ∀ (n : ℕ) (x : ℝ), x ≤ (n : ℝ) + 1 →
    dickApprox (n + 1) x = dickApprox n x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have hx1 : x ≤ 1 := by simpa using hx
    have h1 : dickApprox 1 x = 1 := by
      change dickStep (dickApprox 0) x = 1
      unfold dickStep
      have hmax : max x 1 = 1 := max_eq_right hx1
      rw [hmax]
      simp
    rw [h1]
    rfl
  | succ n ih =>
    intro x hx
    have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    have hx2 : x ≤ (n : ℝ) + 2 := by
      have : x ≤ ((n + 1 : ℕ) : ℝ) + 1 := hx
      rwa [hcast] at this
    change dickStep (dickApprox (n + 1)) x = dickStep (dickApprox n) x
    unfold dickStep
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have h1le : (1 : ℝ) ≤ max x 1 := le_max_right _ _
    have htmem : t ∈ Set.Icc (1 : ℝ) (max x 1) := by
      have : Set.uIcc (1 : ℝ) (max x 1) = Set.Icc 1 (max x 1) := Set.uIcc_of_le h1le
      rwa [this] at ht
    have ht_le : t ≤ max x 1 := htmem.2
    have hmax_le : max x 1 ≤ (n : ℝ) + 2 := by
      apply max_le hx2
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have hsub : t - 1 ≤ (n : ℝ) + 1 := by linarith [le_trans ht_le hmax_le]
    have heq := ih (t - 1) hsub
    change dickApprox (n + 1) (t - 1) / max t 1 = dickApprox n (t - 1) / max t 1
    rw [heq]

private lemma dickApprox_agree_le {n m : ℕ} (hnm : n ≤ m) (x : ℝ) (hx : x ≤ (n : ℝ) + 1) :
    dickApprox m x = dickApprox n x := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ k hkn ih =>
    have hx' : x ≤ (k : ℝ) + 1 := by
      have hnk : (n : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkn
      linarith
    rw [dickApprox_agree_succ k x hx']
    exact ih

private lemma dickApprox_hasDerivAt {N : ℕ} {u : ℝ} (hu : 1 < u) :
    HasDerivAt (dickApprox (N + 1)) (-(dickApprox N (u - 1) / u)) u := by
  have hcont : Continuous (fun t : ℝ => dickApprox N (t - 1) / max t 1) :=
    dickIntegrand_continuous _ (dickApprox_continuous N)
  have hprim : HasDerivAt
      (fun x => ∫ t in (1 : ℝ)..x, dickApprox N (t - 1) / max t 1)
      (dickApprox N (u - 1) / max u 1) u := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hcont.continuousOn).intervalIntegrable
    · exact hcont.stronglyMeasurableAtFilter _ _
    · exact hcont.continuousAt
  have hmax_eq : max u 1 = u := max_eq_left (le_of_lt hu)
  have hev : (fun x => ∫ t in (1 : ℝ)..(max x 1), dickApprox N (t - 1) / max t 1)
      =ᶠ[nhds u] (fun x => ∫ t in (1 : ℝ)..x, dickApprox N (t - 1) / max t 1) := by
    have hmem : Set.Ioi (1 : ℝ) ∈ nhds u := Ioi_mem_nhds hu
    filter_upwards [hmem] with y hy
    simp only [Set.mem_Ioi] at hy
    rw [max_eq_left (le_of_lt hy)]
  have hcomp : HasDerivAt
      (fun x => ∫ t in (1 : ℝ)..(max x 1), dickApprox N (t - 1) / max t 1)
      (dickApprox N (u - 1) / max u 1) u :=
    hprim.congr_of_eventuallyEq hev
  rw [hmax_eq] at hcomp
  have hsub : HasDerivAt
      (fun x => 1 - ∫ t in (1 : ℝ)..(max x 1), dickApprox N (t - 1) / max t 1)
      (0 - dickApprox N (u - 1) / u) u :=
    (hasDerivAt_const u (1 : ℝ)).sub hcomp
  have hzero : (0 : ℝ) - dickApprox N (u - 1) / u = -(dickApprox N (u - 1) / u) := by ring
  rw [hzero] at hsub
  have hstep : dickApprox (N + 1) =
      (fun x => 1 - ∫ t in (1 : ℝ)..(max x 1), dickApprox N (t - 1) / max t 1) := by
    funext x
    simp [dickApprox, dickStep]
  rw [hstep]
  exact hsub

private noncomputable def dickRho (x : ℝ) : ℝ :=
  if x < 0 then 0 else dickApprox ⌈x⌉₊ x

private lemma dickRho_of_neg {x : ℝ} (hx : x < 0) : dickRho x = 0 := by
  unfold dickRho
  simp [hx]

private lemma dickRho_of_nonneg_le {x : ℝ} {n : ℕ} (hx0 : 0 ≤ x) (hxn : x ≤ (n : ℝ)) :
    dickRho x = dickApprox n x := by
  have hneg : ¬ x < 0 := by linarith
  have hceil : ⌈x⌉₊ ≤ n := (Nat.ceil_le).mpr hxn
  have hnn : (0 : ℝ) ≤ (⌈x⌉₊ : ℝ) := Nat.cast_nonneg _
  have hx1 : x ≤ (⌈x⌉₊ : ℝ) + 1 := le_trans (Nat.le_ceil x) (by linarith)
  have hagree := dickApprox_agree_le hceil x hx1
  unfold dickRho
  simp only [hneg, ite_false]
  exact hagree.symm

private lemma dickRho_eq_one_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    dickRho x = 1 := by
  obtain ⟨h0, h1⟩ := hx
  have h : dickRho x = dickApprox 1 x := dickRho_of_nonneg_le h0 (by simpa using h1)
  rw [h]
  exact dickApprox_eq_one_of_le_one 1 x h1

private lemma dickRho_continuousOn : ContinuousOn dickRho (Set.Ici (0 : ℝ)) := by
  intro x hx
  simp only [Set.mem_Ici] at hx
  obtain ⟨N, hN⟩ := exists_nat_ge x
  have hnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hNle : (N : ℝ) < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hxN1 : x < ((N + 1 : ℕ) : ℝ) := lt_of_le_of_lt hN hNle
  have hN' : x ≤ ((N + 1 : ℕ) : ℝ) := le_of_lt hxN1
  have hcont : ContinuousWithinAt (dickApprox (N + 1)) (Set.Ici 0) x :=
    (dickApprox_continuous _).continuousWithinAt
  have heq_at : dickRho x = dickApprox (N + 1) x := dickRho_of_nonneg_le hx hN'
  have hev : dickRho =ᶠ[nhdsWithin x (Set.Ici 0)] dickApprox (N + 1) := by
    have hmem : Set.Iio ((N + 1 : ℕ) : ℝ) ∈ nhds x := Iio_mem_nhds hxN1
    have hmemW : Set.Iio ((N + 1 : ℕ) : ℝ) ∈ nhdsWithin x (Set.Ici 0) :=
      mem_nhdsWithin_of_mem_nhds hmem
    filter_upwards [hmemW, self_mem_nhdsWithin] with y hy1 hy2
    simp only [Set.mem_Iio] at hy1
    simp only [Set.mem_Ici] at hy2
    have hyle : y ≤ ((N + 1 : ℕ) : ℝ) := le_of_lt hy1
    have : dickRho y = dickApprox (N + 1) y := dickRho_of_nonneg_le hy2 hyle
    rw [this]
  exact hcont.congr_of_eventuallyEq hev heq_at

private lemma dickRho_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt dickRho (-(dickRho (u - 1) / u)) u := by
  obtain ⟨N, hN⟩ := exists_nat_ge u
  have hnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hsub0 : (0 : ℝ) ≤ u - 1 := by linarith
  have hsubN : u - 1 ≤ (N : ℝ) := by linarith
  have hRho_sub : dickRho (u - 1) = dickApprox N (u - 1) :=
    dickRho_of_nonneg_le hsub0 hsubN
  have hNM : (N : ℝ) < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
  have huM : u < ((N + 1 : ℕ) : ℝ) := lt_of_le_of_lt hN hNM
  have happrox : HasDerivAt (dickApprox (N + 1)) (-(dickApprox N (u - 1) / u)) u :=
    dickApprox_hasDerivAt hu
  have hev : dickRho =ᶠ[nhds u] dickApprox (N + 1) := by
    have h1 : Set.Iio ((N + 1 : ℕ) : ℝ) ∈ nhds u := Iio_mem_nhds huM
    have h2 : Set.Ioi (0 : ℝ) ∈ nhds u := Ioi_mem_nhds (by linarith)
    filter_upwards [h1, h2] with y hy1 hy2
    simp only [Set.mem_Iio] at hy1
    simp only [Set.mem_Ioi] at hy2
    have hyle : y ≤ ((N + 1 : ℕ) : ℝ) := le_of_lt hy1
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy2
    have : dickRho y = dickApprox (N + 1) y := dickRho_of_nonneg_le hy0 hyle
    rw [this]
  have htrans := happrox.congr_of_eventuallyEq hev
  rw [← hRho_sub] at htrans
  exact htrans

private lemma IsDickmanDeBruijn.hasDerivAt_of_one_lt {σ : ℝ → ℝ}
    (hσ : IsDickmanDeBruijn σ) {u : ℝ} (hu : 1 < u) :
    HasDerivAt σ (-(σ (u - 1) / u)) u := by
  obtain ⟨hdiff, heq⟩ := hσ.2.2.2.2 u hu
  have hu0 : u ≠ 0 := by linarith
  have hderiv : deriv σ u = -(σ (u - 1) / u) := by
    have : u * deriv σ u = -(σ (u - 1)) := by linarith [heq]
    field_simp at this ⊢
    linarith [this]
  rw [← hderiv]
  exact hdiff.hasDerivAt

private lemma dick_unique_aux (σ ρ : ℝ → ℝ)
    (hσ : IsDickmanDeBruijn σ) (hρ : IsDickmanDeBruijn ρ) :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ (n : ℝ) + 1 → σ x = ρ x := by
  intro n
  induction n with
  | zero =>
    intro x h0 hx
    have hx1 : x ≤ 1 := by simpa using hx
    have hσ1 := hσ.2.2.2.1 x ⟨h0, hx1⟩
    have hρ1 := hρ.2.2.2.1 x ⟨h0, hx1⟩
    rw [hσ1, hρ1]
  | succ n ih =>
    intro x h0 hx
    by_cases hxle : x ≤ (n : ℝ) + 1
    · exact ih x h0 hxle
    · have hab : (n : ℝ) + 1 < x := lt_of_not_ge hxle
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
      have hx2 : x ≤ (n : ℝ) + 2 := by
        have : x ≤ ((n + 1 : ℕ) : ℝ) + 1 := hx
        rwa [hcast] at this
      have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
      have hsub_set : Set.Icc ((n : ℝ) + 1) x ⊆ Set.Ici (0 : ℝ) := by
        intro y hy
        simp only [Set.mem_Icc] at hy
        simp only [Set.mem_Ici]
        linarith [hy.1, hn1]
      have hcont : ContinuousOn (fun y => σ y - ρ y) (Set.Icc ((n : ℝ) + 1) x) := by
        apply ContinuousOn.sub
        · exact hσ.2.2.1.mono hsub_set
        · exact hρ.2.2.1.mono hsub_set
      have hdiff : DifferentiableOn ℝ (fun y => σ y - ρ y) (Set.Ioo ((n : ℝ) + 1) x) := by
        intro y hy
        simp only [Set.mem_Ioo] at hy
        have hy1 : (1 : ℝ) < y := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
          linarith [hy.1]
        have hσd := (hσ.2.2.2.2 y hy1).1
        have hρd := (hρ.2.2.2.2 y hy1).1
        exact (hσd.sub hρd).differentiableWithinAt
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope _ hab hcont hdiff
      simp only [Set.mem_Ioo] at hc_mem
      have hc1 : (1 : ℝ) < c := by
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith [hc_mem.1]
      have hc_sub_mem : c - 1 ≤ (n : ℝ) + 1 := by linarith [hc_mem.2, hx2]
      have hc_sub_nonneg : (0 : ℝ) ≤ c - 1 := by
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith [hc_mem.1]
      have heq_sub : σ (c - 1) = ρ (c - 1) := ih (c - 1) hc_sub_nonneg hc_sub_mem
      have hσh := hσ.hasDerivAt_of_one_lt hc1
      have hρh := hρ.hasDerivAt_of_one_lt hc1
      have hsub : HasDerivAt (fun y => σ y - ρ y) 0 c := by
        have h := hσh.sub hρh
        have hval : -(σ (c - 1) / c) - (-(ρ (c - 1) / c)) = 0 := by rw [heq_sub]; ring
        rwa [hval] at h
      have hderiv_eq : deriv (fun y => σ y - ρ y) c = 0 := hsub.deriv
      have hbase : σ ((n : ℝ) + 1) = ρ ((n : ℝ) + 1) := ih _ hn1 (by linarith)
      have hslope : (σ x - ρ x - (σ ((n : ℝ) + 1) - ρ ((n : ℝ) + 1))) / (x - ((n : ℝ) + 1)) =
          0 := by
        rw [← hc_eq, hderiv_eq]
      have hne : x - ((n : ℝ) + 1) ≠ 0 := by linarith [hab]
      have hnum : σ x - ρ x - (σ ((n : ℝ) + 1) - ρ ((n : ℝ) + 1)) = 0 := by
        have := (div_eq_zero_iff).mp hslope
        rcases this with h | h
        · exact h
        · exact absurd h hne
      rw [hbase] at hnum
      linarith [hnum]

private lemma dick_unique (σ ρ : ℝ → ℝ)
    (hσ : IsDickmanDeBruijn σ) (hρ : IsDickmanDeBruijn ρ) : σ = ρ := by
  funext x
  by_cases hxneg : x < 0
  · rw [hσ.1 x hxneg, hρ.1 x hxneg]
  · have hx0 : (0 : ℝ) ≤ x := le_of_not_gt hxneg
    obtain ⟨n, hn⟩ := exists_nat_ge x
    have hle : x ≤ (n : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith [hn]
    exact dick_unique_aux σ ρ hσ hρ n x hx0 hle

private lemma dickRho_contAt_of_pos {w : ℝ} (hw : 0 < w) : ContinuousAt dickRho w := by
  apply dickRho_continuousOn.continuousAt
  apply Filter.mem_of_superset (Ioi_mem_nhds hw)
  intro y hy
  simp only [Set.mem_Ioi] at hy
  simp only [Set.mem_Ici]
  linarith

private lemma dickRho_contOn_Ioi : ContinuousOn dickRho (Set.Ioi 0) := by
  apply dickRho_continuousOn.mono
  intro y hy
  simp only [Set.mem_Ioi] at hy
  simp only [Set.mem_Ici]
  linarith

private lemma dickRho_meas_at_pos {w : ℝ} (hw : 0 < w) :
    StronglyMeasurableAtFilter dickRho (nhds w) MeasureTheory.volume :=
  ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi dickRho_contOn_Ioi w
    (Set.mem_Ioi.mpr hw)

private lemma dickRho_intble {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable dickRho MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply dickRho_continuousOn.mono
  intro y hy
  simp only [Set.mem_Ici]
  rw [Set.mem_uIcc] at hy
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

private lemma dickPrim_hasDerivAt {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, dickRho t) (dickRho w) w := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact dickRho_intble le_rfl (le_of_lt hw)
  · exact dickRho_meas_at_pos hw
  · exact dickRho_contAt_of_pos hw

private lemma dickPrim_eq_id {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..w, dickRho t) = w := by
  obtain ⟨hw0, hw1⟩ := hw
  have hcongr : (∫ t in (0 : ℝ)..w, dickRho t) = ∫ _ in (0 : ℝ)..w, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.mem_uIcc] at ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    exact dickRho_eq_one_of_mem_Icc ht01
  rw [hcongr, intervalIntegral.integral_const]
  simp

private lemma dickPrim_hasDerivWithinAt_right_zero :
    HasDerivWithinAt (fun u => ∫ t in (0 : ℝ)..u, dickRho t) (dickRho 0)
      (Set.Ici 0) 0 := by
  have heq : (fun u => ∫ t in (0 : ℝ)..u, dickRho t)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] id := by
    have hmem : Set.Icc (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) := by
      have h1 : Set.Iic (1 : ℝ) ∈ nhds (0 : ℝ) := by
        apply Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
        intro y hy
        simp only [Set.mem_Iio] at hy
        simp only [Set.mem_Iic]
        linarith
      have h2 := mem_nhdsWithin_of_mem_nhds h1 (t := Set.Ici (0 : ℝ))
      have h3 := Filter.inter_mem self_mem_nhdsWithin h2
      rwa [Set.Ici_inter_Iic] at h3
    filter_upwards [hmem] with y hy
    simp only [id_eq]
    exact dickPrim_eq_id hy
  have hval : (∫ t in (0 : ℝ)..(0 : ℝ), dickRho t) = id (0 : ℝ) := by
    simp [intervalIntegral.integral_same]
  have h := (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq heq hval
  have hρ0 : dickRho 0 = 1 := dickRho_eq_one_of_mem_Icc ⟨le_rfl, zero_le_one⟩
  rw [hρ0]
  exact h

private lemma dickPrim_contWithin_at_zero :
    ContinuousWithinAt (fun u => ∫ t in (0 : ℝ)..u, dickRho t) (Set.Ici 0) 0 :=
  dickPrim_hasDerivWithinAt_right_zero.continuousWithinAt

private lemma dickPrim_contOn_Ici :
    ContinuousOn (fun u => ∫ t in (0 : ℝ)..u, dickRho t) (Set.Ici 0) := by
  intro w hw
  simp only [Set.mem_Ici] at hw
  rcases eq_or_lt_of_le hw with rfl | hpos
  · exact dickPrim_contWithin_at_zero
  · exact (dickPrim_hasDerivAt hpos).continuousAt.continuousWithinAt

private lemma dickApprox1_hasDerivWithinAt_right :
    HasDerivWithinAt (dickApprox 1) (-(dickApprox 0 ((1 : ℝ) - 1) / max (1 : ℝ) 1))
      (Set.Ici 1) 1 := by
  have hcont : Continuous (fun t : ℝ => dickApprox 0 (t - 1) / max t 1) :=
    dickIntegrand_continuous _ (dickApprox_continuous 0)
  have hprim : HasDerivAt
      (fun y => ∫ t in (1 : ℝ)..y, dickApprox 0 (t - 1) / max t 1)
      (dickApprox 0 ((1 : ℝ) - 1) / max (1 : ℝ) 1) 1 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hcont.continuousOn).intervalIntegrable
    · exact hcont.stronglyMeasurableAtFilter _ _
    · exact hcont.continuousAt
  have hev : (fun y => ∫ t in (1 : ℝ)..(max y 1), dickApprox 0 (t - 1) / max t 1)
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ici 1)]
        (fun y => ∫ t in (1 : ℝ)..y, dickApprox 0 (t - 1) / max t 1) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_Ici] at hy
    rw [max_eq_left hy]
  have hval_at : (fun y => ∫ t in (1 : ℝ)..(max y 1), dickApprox 0 (t - 1) / max t 1) 1
      = (fun y => ∫ t in (1 : ℝ)..y, dickApprox 0 (t - 1) / max t 1) 1 := by simp
  have hcomp : HasDerivWithinAt
      (fun y => ∫ t in (1 : ℝ)..(max y 1), dickApprox 0 (t - 1) / max t 1)
      (dickApprox 0 ((1 : ℝ) - 1) / max (1 : ℝ) 1) (Set.Ici 1) 1 :=
    hprim.hasDerivWithinAt.congr_of_eventuallyEq hev hval_at
  have hc : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0 (Set.Ici (1 : ℝ)) 1 :=
    (hasDerivAt_const 1 (1 : ℝ)).hasDerivWithinAt
  have h := hc.sub hcomp
  have hstep : dickApprox 1
      = fun y => 1 - ∫ t in (1 : ℝ)..(max y 1), dickApprox 0 (t - 1) / max t 1 := by
    funext y
    simp [dickApprox, dickStep]
  rw [hstep]
  simpa [Pi.sub_def] using h

private lemma dickRho_approx1_on_Icc12 (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    dickRho y = dickApprox 1 y := by
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have h2 : y ≤ ((2 : ℕ) : ℝ) := by exact_mod_cast hy2
  have e1 : dickRho y = dickApprox 2 y := dickRho_of_nonneg_le hy0 h2
  have e2 : dickApprox 2 y = dickApprox 1 y := by
    have hle : y ≤ ((1 : ℕ) : ℝ) + 1 := by
      have h1c : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      rw [h1c]
      linarith
    exact dickApprox_agree_succ 1 y hle
  rw [e1]
  exact e2

private lemma dickRho_hasDerivWithinAt_right_one :
    HasDerivWithinAt dickRho (-(dickRho ((1 : ℝ) - 1) / 1)) (Set.Ici 1) 1 := by
  have hmem : Set.Icc (1 : ℝ) 2 ∈ nhdsWithin (1 : ℝ) (Set.Ici 1) := by
    have h1 : Set.Iic (2 : ℝ) ∈ nhds (1 : ℝ) := by
      apply Filter.mem_of_superset (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))
      intro y hy
      simp only [Set.mem_Iio] at hy
      simp only [Set.mem_Iic]
      linarith
    have h2 := mem_nhdsWithin_of_mem_nhds h1 (t := Set.Ici (1 : ℝ))
    have h3 := Filter.inter_mem self_mem_nhdsWithin h2
    rwa [Set.Ici_inter_Iic] at h3
  have hev : dickRho =ᶠ[nhdsWithin (1 : ℝ) (Set.Ici 1)] dickApprox 1 := by
    filter_upwards [hmem] with y hy
    exact dickRho_approx1_on_Icc12 y hy
  have hval_at : dickRho 1 = dickApprox 1 1 :=
    dickRho_approx1_on_Icc12 1 ⟨le_rfl, by norm_num⟩
  have hval : (-(dickApprox 0 ((1 : ℝ) - 1) / max (1 : ℝ) 1))
      = (-(dickRho ((1 : ℝ) - 1) / 1)) := by
    have h1 : dickApprox 0 ((1 : ℝ) - 1) = 1 := rfl
    have h2 : dickRho ((1 : ℝ) - 1) = 1 := by
      have h10 : ((1 : ℝ) - 1) = 0 := sub_self 1
      rw [h10]
      exact dickRho_eq_one_of_mem_Icc ⟨le_rfl, zero_le_one⟩
    rw [h1, h2, max_self]
  have h := dickApprox1_hasDerivWithinAt_right.congr_of_eventuallyEq hev hval_at
  rwa [hval] at h

private lemma dickRho_avg {x : ℝ} (hx : 1 ≤ x) :
    x * dickRho x = ∫ t in (x - 1)..x, dickRho t := by
  have hJ1 : ContinuousOn (fun u => ∫ t in (0 : ℝ)..u, dickRho t) (Set.Icc 1 x) :=
    dickPrim_contOn_Ici.mono (by
      intro y hy
      simp only [Set.mem_Icc] at hy
      simp only [Set.mem_Ici]
      linarith [hy.1])
  have hJ0 : ContinuousOn (fun w => ∫ t in (0 : ℝ)..w, dickRho t) (Set.Icc 0 x) :=
    dickPrim_contOn_Ici.mono (by
      intro y hy
      simp only [Set.mem_Icc] at hy
      simp only [Set.mem_Ici]
      linarith [hy.1])
  have hsubC : ContinuousOn (fun u : ℝ => u - 1) (Set.Icc 1 x) :=
    (continuous_id.sub continuous_const).continuousOn
  have hmapsC : Set.MapsTo (fun u : ℝ => u - 1) (Set.Icc 1 x) (Set.Icc 0 x) := by
    intro u hu
    simp only [Set.mem_Icc] at hu ⊢
    constructor <;> linarith [hx, hu.1, hu.2]
  have hH : ContinuousOn ((fun w => ∫ t in (0 : ℝ)..w, dickRho t) ∘ (fun u => u - 1))
      (Set.Icc 1 x) :=
    hJ0.comp hsubC hmapsC
  have hGcont : ContinuousOn ((fun u => ∫ t in (0 : ℝ)..u, dickRho t)
      - ((fun w => ∫ t in (0 : ℝ)..w, dickRho t) ∘ (fun u => u - 1))) (Set.Icc 1 x) :=
    hJ1.sub hH
  have hFcont : ContinuousOn ((id : ℝ → ℝ) * dickRho) (Set.Icc 1 x) := by
    have h1 : ContinuousOn id (Set.Icc (1 : ℝ) x) := continuous_id.continuousOn
    have h2 : ContinuousOn dickRho (Set.Icc (1 : ℝ) x) :=
      dickRho_continuousOn.mono (by
        intro y hy
        simp only [Set.mem_Icc] at hy
        simp only [Set.mem_Ici]
        linarith [hy.1])
    exact h1.mul h2
  have hρ1 : dickRho 1 = 1 := dickRho_eq_one_of_mem_Icc ⟨zero_le_one, le_rfl⟩
  have hJJ1 : (∫ t in (0 : ℝ)..(1 : ℝ), dickRho t) = 1 :=
    dickPrim_eq_id ⟨zero_le_one, le_rfl⟩
  have hJJ0' : (∫ t in (0 : ℝ)..((1 : ℝ) - 1), dickRho t) = 0 := by
    rw [sub_self]
    exact intervalIntegral.integral_same
  have hbase : ((id : ℝ → ℝ) * dickRho) 1
      = ((fun u => ∫ t in (0 : ℝ)..u, dickRho t)
        - ((fun w => ∫ t in (0 : ℝ)..w, dickRho t) ∘ (fun u => u - 1))) 1 := by
    have h : id 1 * dickRho 1
        = (∫ t in (0 : ℝ)..(1 : ℝ), dickRho t)
          - (∫ t in (0 : ℝ)..((1 : ℝ) - 1), dickRho t) := by
      rw [id_eq, hρ1, hJJ1, hJJ0']
      ring
    exact h
  have hFderiv : ∀ u ∈ Set.Ico (1 : ℝ) x,
      HasDerivWithinAt ((id : ℝ → ℝ) * dickRho) (dickRho u - dickRho (u - 1))
        (Set.Ici u) u := by
    intro u hu
    rw [Set.mem_Ico] at hu
    rcases eq_or_lt_of_le hu.1 with rfl | hu1
    · have hid : HasDerivWithinAt id (1 : ℝ) (Set.Ici (1 : ℝ)) 1 :=
        (hasDerivAt_id 1).hasDerivWithinAt
      have hmul := hid.mul dickRho_hasDerivWithinAt_right_one
      have hval : (1 : ℝ) * dickRho 1 + id 1 * (-(dickRho ((1 : ℝ) - 1) / 1))
          = dickRho 1 - dickRho ((1 : ℝ) - 1) := by
        rw [id_eq]
        ring
      rwa [hval] at hmul
    · have hρ := dickRho_hasDerivAt hu1
      have hmul := (hasDerivAt_id u).mul hρ
      have hu0 : u ≠ 0 := by linarith
      have hval : (1 : ℝ) * dickRho u + id u * (-(dickRho (u - 1) / u))
          = dickRho u - dickRho (u - 1) := by
        rw [id_eq]
        field_simp
        ring
      rw [hval] at hmul
      exact hmul.hasDerivWithinAt
  have hGderiv : ∀ u ∈ Set.Ico (1 : ℝ) x,
      HasDerivWithinAt ((fun u => ∫ t in (0 : ℝ)..u, dickRho t)
        - ((fun w => ∫ t in (0 : ℝ)..w, dickRho t) ∘ (fun u => u - 1)))
        (dickRho u - dickRho (u - 1)) (Set.Ici u) u := by
    intro u hu
    rw [Set.mem_Ico] at hu
    have hu0' : (0 : ℝ) < u := by linarith [hu.1]
    have hJ1u : HasDerivWithinAt (fun w => ∫ t in (0 : ℝ)..w, dickRho t)
        (dickRho u) (Set.Ici u) u :=
      (dickPrim_hasDerivAt hu0').hasDerivWithinAt
    rcases eq_or_lt_of_le hu.1 with rfl | hu1
    · have h10 : ((1 : ℝ) - 1) = (0 : ℝ) := sub_self 1
      rw [h10]
      have hsubw : HasDerivWithinAt (fun v : ℝ => v - 1) 1 (Set.Ici (1 : ℝ)) 1 :=
        (HasDerivAt.sub_const (1 : ℝ) (hasDerivAt_id 1)).hasDerivWithinAt
      have hmaps : Set.MapsTo (fun v : ℝ => v - 1) (Set.Ici (1 : ℝ)) (Set.Ici (0 : ℝ)) := by
        intro v hv
        simp only [Set.mem_Ici] at hv ⊢
        linarith
      have hJ0 : HasDerivWithinAt (fun w => ∫ t in (0 : ℝ)..w, dickRho t) (dickRho 0)
          (Set.Ici 0) ((fun v : ℝ => v - 1) 1) := by
        have e : ((fun v : ℝ => v - 1) 1) = (0 : ℝ) := by simp
        rw [e]
        exact dickPrim_hasDerivWithinAt_right_zero
      have hcomp : HasDerivWithinAt
          ((fun w => ∫ t in (0 : ℝ)..w, dickRho t) ∘ (fun v => v - 1))
          (dickRho 0 * 1) (Set.Ici 1) 1 :=
        HasDerivWithinAt.comp 1 hJ0 hsubw hmaps
      have h := hJ1u.sub hcomp
      rw [mul_one] at h
      exact h
    · have hsubpos : (0 : ℝ) < u - 1 := by linarith
      have hJ2 := dickPrim_hasDerivAt hsubpos
      have hg : HasDerivAt (fun v : ℝ => v - 1) 1 u :=
        HasDerivAt.sub_const (1 : ℝ) (hasDerivAt_id u)
      have hcomp : HasDerivWithinAt
          ((fun w => ∫ t in (0 : ℝ)..w, dickRho t) ∘ (fun v => v - 1))
          (dickRho (u - 1) * 1) (Set.Ici u) u :=
        (HasDerivAt.comp u hJ2 hg).hasDerivWithinAt
      have h := hJ1u.sub hcomp
      rw [mul_one] at h
      exact h
  have heq := eq_of_has_deriv_right_eq hFderiv hGderiv hFcont hGcont hbase
  have hxmem : x ∈ Set.Icc (1 : ℝ) x := ⟨hx, le_rfl⟩
  have hxx := heq x hxmem
  have hxx' : x * dickRho x
      = (∫ t in (0 : ℝ)..x, dickRho t) - (∫ t in (0 : ℝ)..(x - 1), dickRho t) := hxx
  have hx10 : (0 : ℝ) ≤ x - 1 := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hint01 := dickRho_intble le_rfl hx10
  have hint1x := dickRho_intble hx10 hx0
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint01 hint1x
  have hfin : (∫ t in (0 : ℝ)..x, dickRho t) - (∫ t in (0 : ℝ)..(x - 1), dickRho t)
      = ∫ t in (x - 1)..x, dickRho t := by linarith [hadd]
  rw [hfin] at hxx'
  exact hxx'

private lemma dickRho_antitoneOn {n : ℕ}
    (hneg : ∀ x : ℝ, 0 ≤ x → x ≤ (n : ℝ) + 1 → 0 ≤ dickRho x) :
    AntitoneOn dickRho (Set.Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · apply dickRho_continuousOn.mono
    intro y hy
    simp only [Set.mem_Icc] at hy
    simp only [Set.mem_Ici]
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith [hy.1]
  · intro y hy
    rw [interior_Icc] at hy
    simp only [Set.mem_Ioo] at hy
    have hy1 : (1 : ℝ) < y := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith [hy.1]
    exact (dickRho_hasDerivAt hy1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    simp only [Set.mem_Ioo] at hy
    have hy1 : (1 : ℝ) < y := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith [hy.1]
    have hderiv : deriv dickRho y = -(dickRho (y - 1) / y) :=
      (dickRho_hasDerivAt hy1).deriv
    rw [hderiv]
    have hsub0 : (0 : ℝ) ≤ y - 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith [hy.1]
    have hsub1 : y - 1 ≤ (n : ℝ) + 1 := by linarith [hy.2]
    have hnn_val := hneg (y - 1) hsub0 hsub1
    have hypos : (0 : ℝ) < y := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith [hy.1]
    have hle : (0 : ℝ) ≤ dickRho (y - 1) / y := div_nonneg hnn_val (le_of_lt hypos)
    linarith

private lemma dickRho_range_aux : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ (n : ℝ) + 1 →
    0 ≤ dickRho x ∧ dickRho x ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro x h0 hx
    have hx1 : x ≤ 1 := by simpa using hx
    have heq := dickRho_eq_one_of_mem_Icc ⟨h0, hx1⟩
    rw [heq]
    exact ⟨zero_le_one, le_rfl⟩
  | succ n ih =>
    intro x h0 hx
    have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hx
    by_cases hxle : x ≤ (n : ℝ) + 1
    · exact ih x h0 hxle
    · have hlt : (n : ℝ) + 1 < x := lt_of_not_ge hxle
      have hanti := dickRho_antitoneOn (fun z hz0 hz1 => (ih z hz0 hz1).1)
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have hmemL : ((n : ℝ) + 1) ∈ Set.Icc ((n : ℝ) + 1) ((n : ℝ) + 2) :=
        ⟨le_rfl, by linarith⟩
      have hmemX : x ∈ Set.Icc ((n : ℝ) + 1) ((n : ℝ) + 2) := ⟨le_of_lt hlt, hx⟩
      have hle_anti : dickRho x ≤ dickRho ((n : ℝ) + 1) := hanti hmemL hmemX hlt.le
      have hbase := ih ((n : ℝ) + 1) (by linarith) (by linarith)
      have hupper : dickRho x ≤ 1 := le_trans hle_anti hbase.2
      have hlower : 0 ≤ dickRho x := by
        by_contra hcon
        have hneg : dickRho x < 0 := lt_of_not_ge hcon
        have hx1 : (1 : ℝ) ≤ x := by linarith [hlt]
        have havg := dickRho_avg hx1
        have hxsub0 : (0 : ℝ) ≤ x - 1 := by linarith [hx1]
        have hx0' : (0 : ℝ) ≤ x := by linarith [hx1]
        have hpoint : ∀ t ∈ Set.Icc (x - 1) x, dickRho x ≤ dickRho t := by
          intro t ht
          simp only [Set.mem_Icc] at ht
          by_cases ht1 : t ≤ (n : ℝ) + 1
          · have ht0 : (0 : ℝ) ≤ t := by linarith [ht.1, hxsub0]
            have hnn_t := (ih t ht0 ht1).1
            linarith [hneg]
          · have hgt : (n : ℝ) + 1 < t := lt_of_not_ge ht1
            have hmemT : t ∈ Set.Icc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
              constructor
              · exact hgt.le
              · linarith [ht.2, hx]
            exact hanti hmemT hmemX (by linarith [ht.2] : t ≤ x)
        have hint1 := dickRho_intble hxsub0 hx0'
        have hconst : IntervalIntegrable (fun _ => dickRho x) MeasureTheory.volume
            (x - 1) x :=
          continuous_const.continuousOn.intervalIntegrable
        have hmono := intervalIntegral.integral_mono_on (by linarith : x - 1 ≤ x)
          hconst hint1 (fun t ht => hpoint t ht)
        have hconstval : (∫ _ in (x - 1)..x, dickRho x) = dickRho x := by
          rw [intervalIntegral.integral_const]
          have hsimp : x - (x - 1) = (1 : ℝ) := by ring
          rw [hsimp, one_smul]
        rw [hconstval] at hmono
        rw [← havg] at hmono
        have hsubpos : (0 : ℝ) < x - 1 := by linarith [hlt]
        have hmul : (x - 1) * dickRho x < 0 := mul_neg_of_pos_of_neg hsubpos hneg
        have hlt2 : x * dickRho x < dickRho x := by linarith [hmul]
        linarith [hmono, hlt2]
      exact ⟨hlower, hupper⟩

/--
**Existence and uniqueness of the Dickman–de Bruijn function.** There is exactly one function
$\rho : \mathbb{R} \to \mathbb{R}$ that is a Dickman–de Bruijn function, that is, such that
$\rho(u) = 0$ for $u < 0$, $0 \le \rho(u) \le 1$ for $u \ge 0$, $\rho$ is continuous on
$[0, \infty)$, $\rho(u) = 1$ for $0 \le u \le 1$, and for every $u > 1$ the function $\rho$ is
differentiable at $u$ with $u \rho'(u) + \rho(u - 1) = 0$.

Source: [O. Gorodetsky, *Rigidity of Averages over the Two Largest Prime
Factors*](https://arxiv.org/abs/2608.05191), which characterizes the unique continuous function on
the nonnegative reals and specifies its zero extension to negative inputs; Lean packages those
clauses in `Real.IsDickmanDeBruijn`.

Proves `Wanted` entry `existsUnique_isDickmanDeBruijn`.
-/
theorem existsUnique_isDickmanDeBruijn :
    ∃! ρ : ℝ → ℝ, IsDickmanDeBruijn ρ := by
  have hRho_maps : Set.MapsTo dickRho (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Set.mem_Ici] at hx
    simp only [Set.mem_Icc]
    obtain ⟨n, hn⟩ := exists_nat_ge x
    have hle : x ≤ (n : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith [hn]
    exact dickRho_range_aux n x hx hle
  have hRho : IsDickmanDeBruijn dickRho := by
    refine ⟨?_, hRho_maps, dickRho_continuousOn, ?_, ?_⟩
    · intro u hu
      exact dickRho_of_neg hu
    · intro u hu
      exact dickRho_eq_one_of_mem_Icc hu
    · intro u hu
      have hderiv := dickRho_hasDerivAt hu
      refine ⟨hderiv.differentiableAt, ?_⟩
      have hval : deriv dickRho u = -(dickRho (u - 1) / u) := hderiv.deriv
      have hu0 : u ≠ 0 := by linarith
      rw [hval]
      field_simp
      ring
  exact ⟨dickRho, hRho, fun σ hσ => dick_unique σ dickRho hσ hRho⟩

end Real
end
