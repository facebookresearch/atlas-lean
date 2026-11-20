/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.RiemannPeriodic

open scoped Real
open MeasureTheory

namespace StatMech.Onsager



theorem continuous_intervalIntegral_right (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) (a b : ℝ) :
    Continuous (fun x => ∫ y in a..b, f x y) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  by_cases hab : a = b
  · subst b
    refine ⟨1, zero_lt_one, fun x _ => ?_⟩
    simpa using hε
  · let ℓ := |b - a|
    have hℓ : 0 < ℓ := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hab))
    let η := ε / (2 * ℓ)
    have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hℓ)
    let K : Set (ℝ × ℝ) := Set.Icc (x₀ - 1) (x₀ + 1) ×ˢ Set.uIcc a b
    have hK : IsCompact K := isCompact_Icc.prod isCompact_uIcc
    have hu : UniformContinuousOn (Function.uncurry f) K :=
      hK.uniformContinuousOn_of_continuous hf.continuousOn
    obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hu) η hη
    refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
    intro x hx
    have hxδ : dist x x₀ < δ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx1 : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_right _ _)
    have hxm : x ∈ Set.Icc (x₀ - 1) (x₀ + 1) := by
      rw [Real.dist_eq, abs_lt] at hx1
      constructor <;> linarith
    have hx₀m : x₀ ∈ Set.Icc (x₀ - 1) (x₀ + 1) := by constructor <;> linarith
    have hslice (z : ℝ) : Continuous (fun y => f z y) := by
      exact hf.comp (continuous_const.prodMk continuous_id)
    have hdiff :
        (∫ y in a..b, f x y) - ∫ y in a..b, f x₀ y =
          ∫ y in a..b, (f x y - f x₀ y) := by
      rw [intervalIntegral.integral_sub
        ((hslice x).intervalIntegrable a b) ((hslice x₀).intervalIntegrable a b)]
    have hbound : ‖∫ y in a..b, (f x y - f x₀ y)‖ ≤ η * ℓ := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hxy : (x, y) ∈ K := ⟨hxm, Set.uIoc_subset_uIcc hy⟩
      have hx₀y : (x₀, y) ∈ K := ⟨hx₀m, Set.uIoc_subset_uIcc hy⟩
      have hpdist : dist (x, y) (x₀, y) < δ := by
        simpa [Prod.dist_eq] using hxδ
      have hout := hmod (x, y) hxy (x₀, y) hx₀y hpdist
      rw [Real.norm_eq_abs, ← Real.dist_eq]
      exact le_of_lt hout
    rw [Real.dist_eq, hdiff, ← Real.norm_eq_abs]
    calc
      ‖∫ y in a..b, (f x y - f x₀ y)‖ ≤ η * ℓ := hbound
      _ = ε / 2 := by simp [η, ℓ]; field_simp
      _ < ε := by linarith



theorem ons_riemann_periodic_two (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f))
    (hper : ∀ y, Function.Periodic (fun x => f x y) (2 * Real.pi)) :
    Filter.Tendsto
      (fun n : ℕ => (2 * Real.pi / n) ^ 2 *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          f (2 * Real.pi * i / n) (2 * Real.pi * j / n))
      Filter.atTop
      (nhds (∫ x in (0)..(2 * Real.pi), ∫ y in (0)..(2 * Real.pi), f x y)) := by
  set T : ℝ := 2 * Real.pi with hT
  have hTpos : (0 : ℝ) < T := by rw [hT]; linarith [Real.pi_pos]
  let g : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..T, f x y
  have hg : Continuous g := continuous_intervalIntegral_right f hf 0 T
  have hperg : Function.Periodic g T := by
    intro x
    apply intervalIntegral.integral_congr
    intro y _
    exact hper y x
  have houter := ons_riemann_periodic g hg hperg
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hεhalf : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp houter) (ε / 2) hεhalf
  let η : ℝ := ε / (4 * T ^ 2)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sq_pos_of_pos hTpos))
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) T
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hu : UniformContinuousOn (Function.uncurry f) K :=
    hK.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hu) η hη
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (T / δ)
  refine ⟨max (max N₀ N₁) 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hnN₁ : N₁ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn0R : (n : ℝ) ≠ 0 := ne_of_gt hnR
  let Δ : ℝ := T / n
  let a : ℕ → ℝ := fun k => T * (k : ℝ) / (n : ℝ)
  have hΔ : 0 < Δ := div_pos hTpos hnR
  have hΔδ : Δ < δ := by
    dsimp [Δ]
    rw [div_lt_iff₀ hnR]
    have hlt : T / δ < (n : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast hnN₀)
    rw [div_lt_iff₀ hδ] at hlt
    linarith
  have hdiff : ∀ k, a (k + 1) - a k = Δ := by
    intro k
    dsimp [a, Δ]
    push_cast
    field_simp
    ring
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = T := by
    dsimp [a]
    rw [mul_div_assoc, div_self hn0R, mul_one]
  have hamem {k : ℕ} (hk : k < n) : a k ∈ Set.Icc (0 : ℝ) T := by
    constructor
    · dsimp [a]
      positivity
    · dsimp [a]
      rw [div_le_iff₀ hnR]
      have hkc : (k : ℝ) ≤ n := by exact_mod_cast hk.le
      nlinarith
  have ha1mem {k : ℕ} (hk : k < n) : a (k + 1) ∈ Set.Icc (0 : ℝ) T := by
    constructor
    · dsimp [a]
      positivity
    · dsimp [a]
      rw [div_le_iff₀ hnR]
      have hkc : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
      nlinarith
  have hslice (x : ℝ) : Continuous (fun y => f x y) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hinner : ∀ i ∈ Finset.range n,
      |g (a i) - Δ * ∑ j ∈ Finset.range n, f (a i) (a j)| ≤ η * T := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hsplit : g (a i) =
        ∑ j ∈ Finset.range n, ∫ y in a j..a (j + 1), f (a i) y := by
      have hs := intervalIntegral.sum_integral_adjacent_intervals
        (f := fun y => f (a i) y) (n := n) (a := a) (μ := volume)
        (fun j _ => (hslice (a i)).intervalIntegrable (a j) (a (j + 1)))
      rw [ha0, han] at hs
      exact hs.symm
    have hdiffeq : g (a i) - Δ * ∑ j ∈ Finset.range n, f (a i) (a j) =
        ∑ j ∈ Finset.range n,
          ∫ y in a j..a (j + 1), (f (a i) y - f (a i) (a j)) := by
      rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_sub
        ((hslice (a i)).intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, hdiff j, smul_eq_mul]
    have hcell : ∀ j ∈ Finset.range n,
        |∫ y in a j..a (j + 1), (f (a i) y - f (a i) (a j))| ≤ η * Δ := by
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hle : a j ≤ a (j + 1) := by linarith [hdiff j, hΔ]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := η) (f := fun y => f (a i) y - f (a i) (a j)) (by
          intro y hy
          rw [Set.uIoc_of_le hle] at hy
          have hyK : y ∈ Set.Icc (0 : ℝ) T :=
            ⟨le_trans (hamem hjn).1 (le_of_lt hy.1), le_trans hy.2 (ha1mem hjn).2⟩
          have hp : (a i, y) ∈ K := ⟨hamem hin, hyK⟩
          have hq : (a i, a j) ∈ K := ⟨hamem hin, hamem hjn⟩
          have hydist : dist (a i, y) (a i, a j) < δ := by
            rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq,
              abs_of_pos (sub_pos.mpr hy.1)]
            calc
              y - a j ≤ a (j + 1) - a j := sub_le_sub_right hy.2 _
              _ = Δ := hdiff j
              _ < δ := hΔδ
          have hout := hmod _ hp _ hq hydist
          rw [Real.norm_eq_abs, ← Real.dist_eq]
          exact le_of_lt hout)
      rw [Real.norm_eq_abs, hdiff j, abs_of_pos hΔ] at hb
      exact hb
    rw [hdiffeq]
    calc
      |∑ j ∈ Finset.range n,
          ∫ y in a j..a (j + 1), (f (a i) y - f (a i) (a j))|
          ≤ ∑ j ∈ Finset.range n,
            |∫ y in a j..a (j + 1), (f (a i) y - f (a i) (a j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range n, η * Δ := Finset.sum_le_sum hcell
      _ = η * T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp [Δ]
        field_simp
  let A : ℝ := Δ ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f (a i) (a j)
  let B : ℝ := Δ * ∑ i ∈ Finset.range n, g (a i)
  have hABeq : A - B =
      Δ * ∑ i ∈ Finset.range n,
        (Δ * ∑ j ∈ Finset.range n, f (a i) (a j) - g (a i)) := by
    dsimp [A, B]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hsum :
        ∑ j ∈ Finset.range n, Δ ^ 2 * f (a i) (a j) =
          Δ * ∑ j ∈ Finset.range n, Δ * f (a i) (a j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    ring
  have hAB : |A - B| ≤ η * T ^ 2 := by
    rw [hABeq, abs_mul, abs_of_pos hΔ]
    calc
      Δ * |∑ i ∈ Finset.range n,
          (Δ * ∑ j ∈ Finset.range n, f (a i) (a j) - g (a i))|
          ≤ Δ * ∑ i ∈ Finset.range n,
            |Δ * ∑ j ∈ Finset.range n, f (a i) (a j) - g (a i)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ Δ * ∑ _i ∈ Finset.range n, η * T := by
        gcongr with i hi
        rw [abs_sub_comm]
        exact hinner i hi
      _ = η * T ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp [Δ]
        field_simp
  have hABsmall : |A - B| < ε / 2 := by
    calc
      |A - B| ≤ η * T ^ 2 := hAB
      _ = ε / 4 := by dsimp [η]; field_simp [ne_of_gt hTpos]
      _ < ε / 2 := by linarith
  have hBout := hN₁ n hnN₁
  change dist ((T / (n : ℝ)) * ∑ k ∈ Finset.range n, g (T * k / n))
    (∫ x in (0 : ℝ)..T, g x) < ε / 2 at hBout
  have hB : dist B (∫ x in (0 : ℝ)..T, g x) < ε / 2 := by
    simpa [B, Δ, a] using hBout
  change dist A (∫ x in (0 : ℝ)..T, g x) < ε
  calc
    dist A (∫ x in (0 : ℝ)..T, g x) ≤ dist A B + dist B (∫ x in (0 : ℝ)..T, g x) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      rw [Real.dist_eq]
      exact add_lt_add hABsmall hB
    _ = ε := by ring


theorem ons_riemann_periodic_two_shift (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f))
    (hper : ∀ y, Function.Periodic (fun x => f x y) (2 * Real.pi))
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun n : ℕ => (2 * Real.pi / n) ^ 2 *
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          f (2 * Real.pi * (i + s) / n) (2 * Real.pi * (j + t) / n))
      Filter.atTop
      (nhds (∫ x in (0)..(2 * Real.pi), ∫ y in (0)..(2 * Real.pi), f x y)) := by
  set T : ℝ := 2 * Real.pi with hT
  have hTpos : (0 : ℝ) < T := by rw [hT]; linarith [Real.pi_pos]
  have hbase := ons_riemann_periodic_two f hf hper
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hεhalf : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hbase) (ε / 2) hεhalf
  let η : ℝ := ε / (4 * T ^ 2)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sq_pos_of_pos hTpos))
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) T
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hu : UniformContinuousOn (Function.uncurry f) K :=
    hK.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hu) η hη
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (T / δ)
  refine ⟨max (max N₀ N₁) 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hnN₁ : N₁ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  let Δ : ℝ := T / n
  have hΔ : 0 < Δ := div_pos hTpos hnR
  have hΔδ : Δ < δ := by
    dsimp [Δ]
    rw [div_lt_iff₀ hnR]
    have hlt : T / δ < (n : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast hnN₀)
    rw [div_lt_iff₀ hδ] at hlt
    linarith
  let a : ℕ → ℝ := fun i => T * i / n
  let as : ℕ → ℝ := fun i => T * (i + s) / n
  let bt : ℕ → ℝ := fun i => T * (i + t) / n
  have hamem {i : ℕ} (hi : i < n) : a i ∈ Set.Icc (0 : ℝ) T := by
    dsimp [a]
    constructor
    · positivity
    · rw [div_le_iff₀ hnR]
      have hic : (i : ℝ) ≤ n := by exact_mod_cast hi.le
      nlinarith
  have hasmem {i : ℕ} (hi : i < n) : as i ∈ Set.Icc (0 : ℝ) T := by
    dsimp [as]
    constructor
    · exact div_nonneg (mul_nonneg hTpos.le (add_nonneg (Nat.cast_nonneg i) hs.1)) hnR.le
    · rw [div_le_iff₀ hnR]
      have hic : (i : ℝ) + s ≤ n := by
        have hi' : (i : ℝ) ≤ n - 1 := by exact_mod_cast (Nat.le_pred_of_lt hi)
        linarith [hs.2]
      nlinarith
  have hbtmem {i : ℕ} (hi : i < n) : bt i ∈ Set.Icc (0 : ℝ) T := by
    dsimp [bt]
    constructor
    · exact div_nonneg (mul_nonneg hTpos.le (add_nonneg (Nat.cast_nonneg i) ht.1)) hnR.le
    · rw [div_le_iff₀ hnR]
      have hic : (i : ℝ) + t ≤ n := by
        have hi' : (i : ℝ) ≤ n - 1 := by exact_mod_cast (Nat.le_pred_of_lt hi)
        linarith [ht.2]
      nlinarith
  have hpoint : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      |f (as i) (bt j) - f (a i) (a j)| ≤ η := by
    intro i hi j hj
    have hin := Finset.mem_range.mp hi
    have hjn := Finset.mem_range.mp hj
    have hp : (as i, bt j) ∈ K := ⟨hasmem hin, hbtmem hjn⟩
    have hq : (a i, a j) ∈ K := ⟨hamem hin, hamem hjn⟩
    have hxs : dist (as i) (a i) ≤ Δ := by
      rw [Real.dist_eq]
      dsimp [as, a, Δ]
      rw [abs_of_nonneg]
      · have hs1 := hs.2
        field_simp
        nlinarith
      · rw [sub_nonneg]
        apply div_le_div_of_nonneg_right _ hnR.le
        nlinarith [hs.1, hTpos]
    have hyt : dist (bt j) (a j) ≤ Δ := by
      rw [Real.dist_eq]
      dsimp [bt, a, Δ]
      rw [abs_of_nonneg]
      · have ht1 := ht.2
        field_simp
        nlinarith
      · rw [sub_nonneg]
        apply div_le_div_of_nonneg_right _ hnR.le
        nlinarith [ht.1, hTpos]
    have hpdist : dist (as i, bt j) (a i, a j) < δ := by
      rw [Prod.dist_eq]
      exact (max_le hxs hyt).trans_lt hΔδ
    have hout := hmod _ hp _ hq hpdist
    rw [Real.dist_eq] at hout
    exact le_of_lt hout
  let S : ℝ := ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f (as i) (bt j)
  let B : ℝ := ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f (a i) (a j)
  have hSB : |S - B| ≤ (n : ℝ) ^ 2 * η := by
    have heq : S - B = ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range n, (f (as i) (bt j) - f (a i) (a j)) := by
      dsimp [S, B]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range n, (f (as i) (bt j) - f (a i) (a j))| ≤
          ∑ i ∈ Finset.range n,
            |∑ j ∈ Finset.range n, (f (as i) (bt j) - f (a i) (a j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range n, |f (as i) (bt j) - f (a i) (a j)| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, ∑ _j ∈ Finset.range n, η := by
        gcongr with i hi j hj
        exact hpoint i hi j hj
      _ = (n : ℝ) ^ 2 * η := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hscaled : |Δ ^ 2 * S - Δ ^ 2 * B| < ε / 2 := by
    rw [← mul_sub, abs_mul, abs_of_pos (sq_pos_of_pos hΔ)]
    calc
      Δ ^ 2 * |S - B| ≤ Δ ^ 2 * ((n : ℝ) ^ 2 * η) := by gcongr
      _ = ε / 4 := by
        dsimp [Δ, η]
        field_simp [hn0, ne_of_gt hTpos]
      _ < ε / 2 := by linarith
  have hBout := hN₁ n hnN₁
  change dist ((T / (n : ℝ)) ^ 2 *
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f (T * i / n) (T * j / n))
    (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f x y) < ε / 2 at hBout
  change dist (Δ ^ 2 * S)
    (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f x y) < ε
  have hB : dist (Δ ^ 2 * B)
      (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f x y) < ε / 2 := by
    simpa [Δ, B, a] using hBout
  calc
    dist (Δ ^ 2 * S) (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f x y) ≤
        dist (Δ ^ 2 * S) (Δ ^ 2 * B) +
          dist (Δ ^ 2 * B) (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f x y) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      rw [Real.dist_eq]
      exact add_lt_add hscaled hB
    _ = ε := by ring

end StatMech.Onsager
