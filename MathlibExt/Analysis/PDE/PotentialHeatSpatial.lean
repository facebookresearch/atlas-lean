/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.PotentialHeatRegularity
public import MathlibExt.Analysis.PDE.HeatIteratedDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import MathlibExt.Analysis.PDE.HeatKernelUniqueness

/-!
# Positive-time spatial regularity of potential-heat evolution

Restarting at an earlier positive time permits finite-order spatial smoothing
without differentiating the initial datum. The proof transfers available
spatial derivatives to the forcing and uses one further Gaussian derivative.
The conclusions concern actual iterated spatial derivatives; joint smoothness
in time and space is a separate result.

The analytic starting points are Gaussian differentiation and Duhamel's formula
in James Nolen, *Partial Differential Equations and Diffusion Processes*,
§§2.3–2.4, https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf.
The finite-order exponential-growth bootstrap here is derived from the proved
weighted heat and Duhamel estimates, with no potential time derivative assumed.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ContDiff
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

private def SpatialRegular (u : ℝ → ℝ → ℝ) (T : ℝ) (n : ℕ) : Prop :=
  (∀ s ∈ Icc 0 T, ContDiff ℝ n (u s)) ∧
  (∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (u p.1) p.2)
    (Icc 0 T ×ˢ univ)) ∧
  (∀ k ≤ n, HeatWholeLine.HasExpGrowthOnStrip (fun s x => iteratedDeriv k (u s) x) T)

private theorem strip_growth_add {u v : ℝ → ℝ → ℝ} {T : ℝ}
    (hu : HeatWholeLine.HasExpGrowthOnStrip u T) (hv : HeatWholeLine.HasExpGrowthOnStrip v T) :
    HeatWholeLine.HasExpGrowthOnStrip (fun t x => u t x + v t x) T := by
  obtain ⟨M, c, hM, hc, hb⟩ := hv
  have hn : HeatWholeLine.HasExpGrowthOnStrip (fun t x => -v t x) T :=
    ⟨M, c, hM, hc, fun t ht x => by simpa only [abs_neg] using hb t ht x⟩
  simpa only [sub_neg_eq_add] using hu.sub hn

private theorem strip_growth_mul {u v : ℝ → ℝ → ℝ} {T : ℝ}
    (hu : HeatWholeLine.HasExpGrowthOnStrip u T) (hv : HeatWholeLine.HasExpGrowthOnStrip v T) :
    HeatWholeLine.HasExpGrowthOnStrip (fun t x => u t x * v t x) T := by
  obtain ⟨M, c, hM, hc, hb⟩ := hu
  obtain ⟨N, d, hN, hd, hb'⟩ := hv
  refine ⟨M*N, c+d, mul_nonneg hM hN, add_nonneg hc hd, fun t ht x => ?_⟩
  rw [abs_mul]
  calc
    _ ≤ (M * exp (c * |x|)) * (N * exp (d * |x|)) :=
      mul_le_mul (hb t ht x) (hb' t ht x) (abs_nonneg _) (by positivity)
    _ = _ := by rw [add_mul, exp_add]; ring

private theorem strip_growth_sum {ι : Type*} (s : Finset ι) {u : ι → ℝ → ℝ → ℝ} {T : ℝ}
    (hu : ∀ i ∈ s, HeatWholeLine.HasExpGrowthOnStrip (u i) T) :
    HeatWholeLine.HasExpGrowthOnStrip (fun t x => ∑ i ∈ s, u i t x) T := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HeatWholeLine.HasExpGrowthOnStrip.of_bounded
      (u := fun _ _ => 0) (T := T) ⟨0, fun _ _ _ => by simp⟩)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      strip_growth_add (hu a (Finset.mem_insert_self _ _))
        (ih (fun i hi => hu i (Finset.mem_insert_of_mem hi)))

private theorem spatial_regular_mul {u v : ℝ → ℝ → ℝ} {T : ℝ} {n : ℕ}
    (hu : SpatialRegular u T n) (hv : SpatialRegular v T n) :
    SpatialRegular (fun t x => u t x * v t x) T n := by
  have he (k : ℕ) (hk : k ≤ n) (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
      iteratedDeriv k (fun y => u t y * v t y) x =
        ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
          iteratedDeriv i (u t) x * iteratedDeriv (k-i) (v t) x :=
    iteratedDeriv_fun_mul ((hu.1 t ht).of_le (by exact_mod_cast hk)).contDiffAt
      ((hv.1 t ht).of_le (by exact_mod_cast hk)).contDiffAt
  refine ⟨fun t ht => (hu.1 t ht).mul (hv.1 t ht), ?_, ?_⟩
  · intro k hk
    have hc : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (k+1),
        (k.choose i : ℝ) * iteratedDeriv i (u p.1) p.2 *
          iteratedDeriv (k-i) (v p.1) p.2) (Icc 0 T ×ˢ univ) := by
      apply continuousOn_finsetSum
      intro i hi
      have hi' : i ≤ n := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk
      exact (continuousOn_const.mul (hu.2.1 i hi')).mul
        (hv.2.1 (k-i) ((Nat.sub_le k i).trans hk))
    exact hc.congr (fun p hp => he k hk p.1 hp.1 p.2)
  · intro k hk
    have hbound : HeatWholeLine.HasExpGrowthOnStrip
        (fun t x => ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
          iteratedDeriv i (u t) x * iteratedDeriv (k-i) (v t) x) T := by
      apply strip_growth_sum
      intro i hi
      have hi' : i ≤ n := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk
      exact strip_growth_mul
        (strip_growth_mul (.of_bounded ⟨|(k.choose i : ℝ)|, fun _ _ _ => le_rfl⟩)
          (hu.2.2 i hi')) (hv.2.2 (k-i) ((Nat.sub_le k i).trans hk))
    obtain ⟨M, c, hM, hc, hb⟩ := hbound
    refine ⟨M, c, hM, hc, fun t ht x => ?_⟩
    dsimp only
    rw [he k hk t ht x]
    exact hb t ht x

private theorem spatial_regular_duhamel {f : ℝ → ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hf : SpatialRegular f T n) :
    SpatialRegular (heatDuhamel ν f) T (n+1) := by
  have hcont (k : ℕ) (hk : k ≤ n+1) :
      ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (heatDuhamel ν f p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
    by_cases hkn : k ≤ n
    · exact heatDuhamel_iteratedDeriv_continuousOn hν.le hT
        (fun s hs => (hf.1 s hs).of_le (by exact_mod_cast hkn))
        (fun j hj => hf.2.1 j (hj.trans hkn)) (fun j hj => hf.2.2 j (hj.trans hkn))
    · have he : k = n+1 := by omega
      subst k
      exact heatDuhamel_iteratedDeriv_succ_continuousOn hν hT hf.1 hf.2.1 hf.2.2
  refine ⟨?_, hcont, ?_⟩
  · intro t ht
    apply contDiff_nat_iff_iteratedDeriv.mpr
    refine ⟨fun k hk => (hcont k hk).comp_continuous
      (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩), ?_⟩
    intro k hk x
    have hkn : k ≤ n := Nat.le_of_lt_succ hk
    exact (heatDuhamel_hasDerivAt_iteratedDeriv hν
      (fun s hs => (hf.1 s hs).of_le (by exact_mod_cast hkn))
      (fun j hj => hf.2.1 j (hj.trans hkn))
      (fun j hj => hf.2.2 j (hj.trans hkn)) ht x).differentiableAt
  · intro k hk
    by_cases hkn : k ≤ n
    · exact heatDuhamel_iteratedDeriv_hasExpGrowthOnStrip hν.le hT
        (fun s hs => (hf.1 s hs).of_le (by exact_mod_cast hkn))
        (fun j hj => hf.2.1 j (hj.trans hkn)) (fun j hj => hf.2.2 j (hj.trans hkn))
    · have he : k = n+1 := by omega
      subst k
      exact heatDuhamel_iteratedDeriv_succ_hasExpGrowthOnStrip hν hf.1 hf.2.1 hf.2.2

private theorem spatial_regular_shift {u : ℝ → ℝ → ℝ} {T a : ℝ} {n : ℕ}
    (hu : SpatialRegular u T n) (ha : 0 ≤ a) :
    SpatialRegular (fun t => u (a+t)) (T-a) n := by
  have hs {t : ℝ} (ht : t ∈ Icc 0 (T-a)) : a+t ∈ Icc 0 T :=
    ⟨add_nonneg ha ht.1, by linarith [ht.2]⟩
  refine ⟨fun t ht => hu.1 _ (hs ht), ?_, ?_⟩
  · intro k hk
    exact (hu.2.1 k hk).comp (by fun_prop :
      ContinuousOn (fun p : ℝ × ℝ => (a+p.1, p.2)) (Icc 0 (T-a) ×ˢ univ))
      (fun p hp => ⟨hs hp.1, hp.2⟩)
  · intro k hk
    obtain ⟨M, c, hM, hc, hb⟩ := hu.2.2 k hk
    exact ⟨M, c, hM, hc, fun t ht x => hb _ (hs ht) x⟩

private theorem spatial_regular_add {u v : ℝ → ℝ → ℝ} {T : ℝ} {n : ℕ}
    (hu : SpatialRegular u T n) (hv : SpatialRegular v T n) :
    SpatialRegular (fun t x => u t x + v t x) T n := by
  have he (k : ℕ) (hk : k ≤ n) (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
      iteratedDeriv k (fun y => u t y + v t y) x =
        iteratedDeriv k (u t) x + iteratedDeriv k (v t) x :=
    iteratedDeriv_fun_add ((hu.1 t ht).of_le (by exact_mod_cast hk)).contDiffAt
      ((hv.1 t ht).of_le (by exact_mod_cast hk)).contDiffAt
  refine ⟨fun t ht => (hu.1 t ht).add (hv.1 t ht), ?_, ?_⟩
  · intro k hk
    exact ((hu.2.1 k hk).add (hv.2.1 k hk)).congr (fun p hp => he k hk p.1 hp.1 p.2)
  · intro k hk
    obtain ⟨M, c, hM, hc, hb⟩ := strip_growth_add (hu.2.2 k hk) (hv.2.2 k hk)
    refine ⟨M, c, hM, hc, fun t ht x => ?_⟩
    dsimp only
    rw [he k hk t ht x]
    exact hb t ht x

private theorem spatial_regular_heat {g : ℝ → ℝ} {ν T a : ℝ} {n : ℕ}
    (hν : 0 < ν) (hg : ContDiff ℝ n g) (hgg : ∀ k ≤ n, HasExpGrowth (iteratedDeriv k g))
    (ha : 0 < a) (haT : a ≤ T) :
    SpatialRegular (fun s x => heatSolution g (ν*(a+s)) x) (T-a) (n+1) := by
  have hcont (k : ℕ) (hk : k ≤ n) : Continuous (iteratedDeriv k g) :=
    (contDiff_nat_iff_iteratedDeriv.mp hg).1 k hk
  have he (k : ℕ) (hk : k ≤ n) (t x : ℝ) :
      iteratedDeriv k (heatSolution g (ν*t)) x =
        heatSolution (iteratedDeriv k g) (ν*t) x :=
    heatSolution_iteratedDeriv_of_exp_growth (hg.of_le (by exact_mod_cast hk))
      (fun j hj => hgg j (hj.trans hk)) _ _
  have hen (t : ℝ) : iteratedDeriv (n+1) (heatSolution g (ν*t)) =
      deriv (heatSolution (iteratedDeriv n g) (ν*t)) := by
    rw [iteratedDeriv_succ, funext (he n le_rfl t)]
  have hz : potentialHeatSolution ν (fun _ _ => 0) (iteratedDeriv n g) =
      fun t => heatSolution (iteratedDeriv n g) (ν*t) :=
    funext (fun t => funext (potentialHeatSolution_zero_potential ν (iteratedDeriv n g) t))
  have hgc := potentialHeatSolution_deriv_continuousOn (q := fun _ _ => 0) (T := T)
    hν (by fun_prop) (Q := 0) le_rfl (fun _ _ _ => by simp) (hcont n le_rfl) (hgg n le_rfl)
  rw [hz] at hgc
  have hgb := potentialHeatSolution_deriv_hasExpGrowthOnStrip (q := fun _ _ => 0)
    hν (by fun_prop) (Q := 0) le_rfl (fun _ _ _ => by simp)
    (hcont n le_rfl) (hgg n le_rfl) ha haT
  rw [hz] at hgb
  have hs {s : ℝ} (hs : s ∈ Icc 0 (T-a)) : a+s ∈ Ioc 0 T :=
    ⟨add_pos_of_pos_of_nonneg ha hs.1, by linarith [hs.2]⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s hss
    have h := heatSolution_contDiffOn_scaled_of_exp_growth hg.continuous.aestronglyMeasurable
      (by simpa only [iteratedDeriv_zero] using hgg 0 (Nat.zero_le n)) hν
    have hc : ContDiffOn ℝ ∞ (fun x => heatSolution g (ν*(a+s)) x) univ :=
      h.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x _ => ⟨(hs hss).1, mem_univ x⟩)
    exact (contDiffOn_univ.mp hc).of_le (by simp)
  · intro k hk
    by_cases hkn : k ≤ n
    · have hc : Continuous (fun p : ℝ × ℝ =>
          heatSolution (iteratedDeriv k g) (ν*(a+p.1)) p.2) :=
        (heatSolution_continuous_of_exp_growth (hcont k hkn) (hgg k hkn)).comp
          (by fun_prop : Continuous (fun p : ℝ × ℝ => (ν*(a+p.1), p.2)))
      exact hc.continuousOn.congr (fun p _ => he k hkn (a+p.1) p.2)
    · have hk' : k = n+1 := by omega
      subst k
      have hc := hgc.comp (by fun_prop : ContinuousOn
        (fun p : ℝ × ℝ => (a+p.1, p.2)) (Icc 0 (T-a) ×ˢ univ))
        (fun p hp => ⟨hs hp.1, hp.2⟩)
      exact hc.congr (fun p _ => congrFun (hen (a+p.1)) p.2)
  · intro k hk
    by_cases hkn : k ≤ n
    · obtain ⟨M, c, hM, hc, hb⟩ := heatSolution_hasExpGrowthOnStrip
        (hcont k hkn) (hgg k hkn) hν.le T
      refine ⟨M, c, hM, hc, fun s hss x => ?_⟩
      dsimp only
      rw [he k hkn]
      exact hb _ ⟨(hs hss).1.le, (hs hss).2⟩ x
    · have hk' : k = n+1 := by omega
      subst k
      obtain ⟨M, c, hM, hc, hb⟩ := hgb
      refine ⟨M, c, hM, hc, fun s hss x => ?_⟩
      dsimp only
      rw [hen]
      exact hb s hss x

private theorem spatial_regular_congr {u v : ℝ → ℝ → ℝ} {T : ℝ} {n : ℕ}
    (hu : SpatialRegular u T n) (he : ∀ t ∈ Icc 0 T, u t = v t) :
    SpatialRegular v T n := by
  refine ⟨fun t ht => by rw [← he t ht]; exact hu.1 t ht, ?_, ?_⟩
  · intro k hk
    exact (hu.2.1 k hk).congr (fun p hp => by dsimp only; rw [he p.1 hp.1])
  · intro k hk
    obtain ⟨M, c, hM, hc, hb⟩ := hu.2.2 k hk
    refine ⟨M, c, hM, hc, fun t ht x => ?_⟩
    dsimp only
    rw [← he t ht]
    exact hb t ht x

private theorem potential_spatial_regular {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 < ν)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) {a : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    SpatialRegular (fun s => potentialHeatSolution ν q g (a+s)) (T-a) n := by
  have hq0 : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
    simpa only [iteratedDeriv_zero, Function.uncurry_def] using hqc 0 (Nat.zero_le n)
  obtain ⟨Q, hQ⟩ := hqb 0 (Nat.zero_le n)
  have hqb0 : ∀ s ∈ Icc 0 T, ∀ x, |q s x| ≤ |Q| :=
    fun s hs x => (hQ s hs x).trans (le_abs_self Q)
  clear hQ
  induction n generalizing a with
  | zero =>
    have hc := potentialHeatSolution_continuousOn hν.le (ha.le.trans haT)
      hq0 (abs_nonneg Q) hqb0 hg hgg
    have hb := potentialHeatSolution_hasExpGrowthOnStrip hν.le hq0 (abs_nonneg Q) hqb0 hg hgg
    have hr : SpatialRegular (potentialHeatSolution ν q g) T 0 := by
      refine ⟨fun s hs => contDiff_zero.mpr (hc.comp_continuous
        (continuous_const.prodMk continuous_id) (fun x => ⟨hs, mem_univ x⟩)), ?_, ?_⟩
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        simpa only [iteratedDeriv_zero, Function.uncurry_def] using hc
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        simpa only [iteratedDeriv_zero] using hb
    exact spatial_regular_shift hr ha.le
  | succ n ih =>
    have hqs' : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s) :=
      fun s hs => (hqs s hs).of_le (by exact_mod_cast Nat.le_succ n)
    have hqc' := fun k (hk : k ≤ n) => hqc k (hk.trans (Nat.le_succ n))
    have hqb' := fun k (hk : k ≤ n) => hqb k (hk.trans (Nat.le_succ n))
    have hah : 0 < a/2 := half_pos ha
    have hahT : a/2 ≤ T := (half_le_self ha.le).trans haT
    have hu := ih hqs' hqc' hqb' hah hahT
    have hqr : SpatialRegular q T n :=
      ⟨hqs', hqc', fun k hk => .of_bounded (hqb' k hk)⟩
    have hfr := spatial_regular_mul (spatial_regular_shift hqr hah.le) hu
    have hd := spatial_regular_duhamel hν (sub_nonneg.mpr hahT) hfr
    have hd' : SpatialRegular (fun s => heatDuhamel ν
        (fun r x => q (a/2+r) x * potentialHeatSolution ν q g (a/2+r) x) (a/2+s))
        (T-a) (n+1) := by
      convert spatial_regular_shift hd hah.le using 1
      ring
    have hgi : ContDiff ℝ n (potentialHeatSolution ν q g (a/2)) := by
      simpa only [add_zero] using hu.1 0 ⟨le_rfl, sub_nonneg.mpr hahT⟩
    have hgb (k : ℕ) (hk : k ≤ n) :
        HasExpGrowth (iteratedDeriv k (potentialHeatSolution ν q g (a/2))) := by
      obtain ⟨M, c, hM, hc, hb⟩ := hu.2.2 k hk
      exact ⟨M, c, hM, hc, fun x => by
        simpa only [add_zero] using hb 0 ⟨le_rfl, sub_nonneg.mpr hahT⟩ x⟩
    have hp : SpatialRegular
        (fun s x => heatSolution (potentialHeatSolution ν q g (a/2)) (ν*(a/2+s)) x)
        (T-a) (n+1) := by
      convert spatial_regular_heat hν hgi hgb hah (show a/2 ≤ T-a/2 by linarith) using 1
      ring
    apply spatial_regular_congr (spatial_regular_add hp hd')
    intro s hs
    funext x
    have he := potentialHeatSolution_restart_mild hν.le hq0 (abs_nonneg Q) hqb0 hg hgg
      hah.le (show 0 ≤ a/2+s from add_nonneg hah.le hs.1)
      (show a/2+(a/2+s) ≤ T by linarith [hs.2]) x
    have ht : a/2+(a/2+s) = a+s := by ring
    simpa only [ht] using he.symm

/-- A spatially smooth bounded potential gives finite-order spatial regularity
of the actual constructed field at every positive time. Only continuity and
exponential growth of the initial datum are required. -/
theorem potentialHeatSolution_contDiff_space {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t : ℝ} {n : ℕ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ht : t ∈ Ioc 0 T) :
    ContDiff ℝ n (potentialHeatSolution ν q g t) := by
  have h := potential_spatial_regular hν hqs hqc hqb hg hgg ht.1 ht.2
  simpa only [add_zero] using h.1 0 ⟨le_rfl, sub_nonneg.mpr ht.2⟩

/-- Each actual finite-order spatial derivative is jointly continuous on any
closed strip separated from the initial time, including the terminal slice. -/
theorem potentialHeatSolution_iteratedDeriv_continuousOn
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T a : ℝ} {n : ℕ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ha : 0 < a) (haT : a ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (potentialHeatSolution ν q g p.1) p.2)
      (Icc a T ×ˢ univ) := by
  have hc := (potential_spatial_regular hν hqs hqc hqb hg hgg ha haT).2.1 n le_rfl
  have hm : MapsTo (fun p : ℝ × ℝ => (p.1-a, p.2))
      (Icc a T ×ˢ univ) (Icc 0 (T-a) ×ˢ univ) :=
    fun p hp => ⟨⟨sub_nonneg.mpr hp.1.1, sub_le_sub_right hp.1.2 a⟩, hp.2⟩
  have h := hc.comp (by fun_prop : ContinuousOn
    (fun p : ℝ × ℝ => (p.1-a, p.2)) (Icc a T ×ˢ univ)) hm
  simpa only [Function.comp_def, ← add_sub_assoc, add_sub_cancel_left] using h

/-- Every actual finite-order spatial derivative has uniform exponential growth
on a finite time strip with positive lower endpoint. -/
theorem potentialHeatSolution_iteratedDeriv_hasExpGrowthOnStrip
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T a : ℝ} {n : ℕ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ha : 0 < a) (haT : a ≤ T) :
    HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => iteratedDeriv n (potentialHeatSolution ν q g (a+s)) x) (T-a) :=
  (potential_spatial_regular hν hqs hqc hqb hg hgg ha haT).2.2 n le_rfl

/-- The restarted mild identity can be differentiated through every available
spatial order. Both the new initial derivative and differentiated forcing are
actual derivatives of the constructed solution. -/
theorem potentialHeatSolution_iteratedDeriv_restart_mild
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T a b : ℝ} {n : ℕ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g)
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a+b ≤ T) (x : ℝ) :
    iteratedDeriv n (potentialHeatSolution ν q g (a+b)) x =
      heatSolution (iteratedDeriv n (potentialHeatSolution ν q g a)) (ν*b) x +
        heatDuhamel ν (fun s y => iteratedDeriv n
          (fun z => q (a+s) z * potentialHeatSolution ν q g (a+s) z) y) b x := by
  have haT : a ≤ T := (le_add_of_nonneg_right hb).trans hab
  have hu := potential_spatial_regular hν hqs hqc hqb hg hgg ha haT
  have hqr : SpatialRegular q T n :=
    ⟨hqs, hqc, fun k hk => .of_bounded (hqb k hk)⟩
  have hf := spatial_regular_mul (spatial_regular_shift hqr ha.le) hu
  have hbt : b ∈ Icc 0 (T-a) := ⟨hb, by linarith⟩
  have hd := (spatial_regular_duhamel hν (sub_nonneg.mpr haT) hf).1 b hbt
  have hd' : ContDiff ℝ n (heatDuhamel ν
      (fun s y => q (a+s) y * potentialHeatSolution ν q g (a+s) y) b) :=
    hd.of_le (by exact_mod_cast Nat.le_succ n)
  have hq0 : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
    simpa only [iteratedDeriv_zero, Function.uncurry_def] using hqc 0 (Nat.zero_le n)
  obtain ⟨Q, hQ⟩ := hqb 0 (Nat.zero_le n)
  have hqb0 : ∀ s ∈ Icc 0 T, ∀ y, |q s y| ≤ |Q| :=
    fun s hs y => (hQ s hs y).trans (le_abs_self Q)
  have he : potentialHeatSolution ν q g (a+b) = fun y =>
      heatSolution (potentialHeatSolution ν q g a) (ν*b) y +
        heatDuhamel ν (fun s z => q (a+s) z * potentialHeatSolution ν q g (a+s) z) b y :=
    funext (potentialHeatSolution_restart_mild hν.le hq0 (abs_nonneg Q) hqb0 hg hgg ha.le hb hab)
  have hp : ContDiff ℝ n (heatSolution (potentialHeatSolution ν q g a) (ν*b)) := by
    have he' : heatSolution (potentialHeatSolution ν q g a) (ν*b) = fun y =>
        potentialHeatSolution ν q g (a+b) y -
          heatDuhamel ν (fun s z => q (a+s) z * potentialHeatSolution ν q g (a+s) z) b y := by
      funext y
      rw [he]
      simp only [add_sub_cancel_right]
    rw [he']
    exact (hu.1 b hbt).sub hd'
  have hga : ContDiff ℝ n (potentialHeatSolution ν q g a) := by
    simpa only [add_zero] using hu.1 0 ⟨le_rfl, sub_nonneg.mpr haT⟩
  have hgb (k : ℕ) (hk : k ≤ n) : HasExpGrowth (iteratedDeriv k
      (potentialHeatSolution ν q g a)) := by
    obtain ⟨M, c, hM, hc, hh⟩ := hu.2.2 k hk
    exact ⟨M, c, hM, hc, fun y => by
      simpa only [add_zero] using hh 0 ⟨le_rfl, sub_nonneg.mpr haT⟩ y⟩
  rw [he, iteratedDeriv_fun_add hp.contDiffAt hd'.contDiffAt,
    heatSolution_iteratedDeriv_of_exp_growth hga hgb,
    heatDuhamel_iteratedDeriv hν.le hf.1 hf.2.1 hf.2.2 hbt]

/-- Each actual spatial derivative is jointly continuous on the entire
positive-time strip. Initial time is excluded; terminal time is included. -/
theorem potentialHeatSolution_iteratedDeriv_continuousOn_pos
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (potentialHeatSolution ν q g p.1) p.2)
      (Ioc 0 T ×ˢ univ) := by
  intro p hp
  have ha : 0 < p.1/2 := half_pos hp.1.1
  have haT : p.1/2 ≤ T := (half_le_self hp.1.1.le).trans hp.1.2
  have hc := potentialHeatSolution_iteratedDeriv_continuousOn hν hqs hqc hqb hg hgg ha haT
    p ⟨⟨half_le_self hp.1.1.le, hp.1.2⟩, hp.2⟩
  apply hc.mono_of_mem_nhdsWithin
  have hn : Ioi (p.1/2) ×ˢ (univ : Set ℝ) ∈ 𝓝 p :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨half_lt_self hp.1.1, hp.2⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with y hy hya
  exact ⟨⟨hya.1.le, hy.1.2⟩, hy.2⟩

/-- The actual differentiated potential forcing is jointly continuous on each
restarted positive-time strip, for subsequent Duhamel time differentiation. -/
theorem potentialHeatSolution_forcing_iteratedDeriv_continuousOn
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T a : ℝ} {n : ℕ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ha : 0 < a) (haT : a ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n
      (fun y => q (a+p.1) y * potentialHeatSolution ν q g (a+p.1) y) p.2)
      (Icc 0 (T-a) ×ˢ univ) := by
  have hqr : SpatialRegular q T n :=
    ⟨hqs, hqc, fun k hk => .of_bounded (hqb k hk)⟩
  have hu := potential_spatial_regular hν hqs hqc hqb hg hgg ha haT
  exact (spatial_regular_mul (spatial_regular_shift hqr ha.le) hu).2.1 n le_rfl

/-- Actual differentiated potential forcing has uniform exponential growth on
each restarted positive-time strip, without a potential time derivative. -/
theorem potentialHeatSolution_forcing_iteratedDeriv_hasExpGrowthOnStrip
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T a : ℝ} {n : ℕ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ha : 0 < a) (haT : a ≤ T) :
    HeatWholeLine.HasExpGrowthOnStrip (fun s x => iteratedDeriv n
      (fun y => q (a+s) y * potentialHeatSolution ν q g (a+s) y) x) (T-a) := by
  have hqr : SpatialRegular q T n :=
    ⟨hqs, hqc, fun k hk => .of_bounded (hqb k hk)⟩
  have hu := potential_spatial_regular hν hqs hqc hqb hg hgg ha haT
  exact (spatial_regular_mul (spatial_regular_shift hqr ha.le) hu).2.2 n le_rfl

end MathlibExt.Analysis.PDE.HeatKernel
