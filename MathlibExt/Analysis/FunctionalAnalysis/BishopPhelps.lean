/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted

open Set Metric
open Filter

-- Ekeland-type lemma for linear functions on the closed unit ball (replaces the
-- unavailable `MetaMathlibExt.ekeland_variational_principle_general`).
private theorem ekeland_linear_aux
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : F →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε)
    {y : F} (hy : y ∈ Metric.closedBall (0 : F) 1) :
    ∃ x1 ∈ Metric.closedBall (0 : F) 1,
      ∀ b ∈ Metric.closedBall (0 : F) 1, b ≠ x1 → f b - f x1 < ε * ‖b - x1‖ := by
  set B : Set F := Metric.closedBall (0 : F) 1 with hBdef
  have hBclosed : IsClosed B := by rw [hBdef]; exact Metric.isClosed_closedBall
  have := hBclosed.completeSpace_coe
  set ψ : ↥B → ℝ := fun x => -(f (x : F)) with hψdef
  set S : ↥B → Set ↥B := fun x => {z | ψ z + ε * dist z x ≤ ψ x} with hSdef
  have hSmem : ∀ x z : ↥B, z ∈ S x ↔ ψ z + ε * dist z x ≤ ψ x := by
    intro x z; simp only [hSdef, Set.mem_ofPred_eq]
  have hψcont : Continuous ψ := (f.continuous.comp continuous_subtype_val).neg
  have hlb : ∀ z : ↥B, -(‖f‖) ≤ ψ z := by
    intro z
    have h1 : ‖f (z : F)‖ ≤ ‖f‖ * ‖(z : F)‖ := f.le_opNorm _
    have h2 : ‖(z : F)‖ ≤ 1 := mem_closedBall_zero_iff.mp (by rw [← hBdef]; exact z.2)
    have h3 : f (z : F) ≤ ‖f‖ := by
      calc f (z : F) ≤ |f (z : F)| := le_abs_self _
        _ = ‖f (z : F)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖f‖ * ‖(z : F)‖ := h1
        _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖f‖ := mul_one _
    simp only [hψdef]
    linarith
  have hS_self : ∀ x : ↥B, x ∈ S x := by
    intro x; rw [hSmem]; rw [dist_self]; simp [hψdef]
  have hbdd : ∀ x : ↥B, BddBelow (ψ '' S x) := by
    intro x
    refine ⟨-(‖f‖), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hlb z
  have hne : ∀ x : ↥B, (ψ '' S x).Nonempty := by
    intro x
    exact ⟨ψ x, x, hS_self x, rfl⟩
  have hstep : ∀ (n : ℕ) (x : ↥B),
      ∃ z, (ψ z + ε * dist z x ≤ ψ x) ∧
        (ψ z < sInf (ψ '' S x) + (1 / 2 : ℝ) ^ (n + 1)) := by
    intro n x
    have h1 := hbdd x
    have h2 := hne x
    have h3 : sInf (ψ '' S x) < sInf (ψ '' S x) + (1 / 2 : ℝ) ^ (n + 1) :=
      lt_add_of_pos_right _ (by positivity)
    obtain ⟨w, hwmem, hwlt⟩ := (csInf_lt_iff h1 h2).mp h3
    obtain ⟨z, hzS, rfl⟩ := hwmem
    exact ⟨z, (hSmem x z).mp hzS, hwlt⟩
  choose g hgS hglt using hstep
  have hxn : ∃ xn : ℕ → ↥B, xn 0 = ⟨y, hy⟩ ∧ ∀ n, xn (n + 1) = g n (xn n) :=
    ⟨Nat.rec (motive := fun _ => ↥B) ⟨y, hy⟩ (fun n prev => g n prev), rfl, fun n => rfl⟩
  obtain ⟨xn, h0, hsucc⟩ := hxn
  have hxS : ∀ n, xn (n + 1) ∈ S (xn n) := by
    intro n; rw [hSmem, hsucc n]; exact hgS n _
  have hnest : ∀ n, S (xn (n + 1)) ⊆ S (xn n) := by
    intro n z hz
    rw [hSmem] at hz ⊢
    have hle2 := (hSmem (xn n) (xn (n + 1))).mp (hxS n)
    have htri := dist_triangle z (xn (n + 1)) (xn n)
    have hmul := mul_le_mul_of_nonneg_left htri hε.le
    linarith
  have hsub : ∀ m n : ℕ, n ≤ m → S (xn m) ⊆ S (xn n) := by
    intro m n h; induction m, h using Nat.le_induction with
    | base => exact Subset.rfl
    | succ k hnk ih => exact (hnest k).trans ih
  have hmem_le : ∀ m n : ℕ, n ≤ m → xn m ∈ S (xn n) := by
    intro m n h
    exact hsub m n h (hS_self _)
  have hanti : Antitone (fun n => ψ (xn n)) := by
    intro a b hab
    have hle := (hSmem (xn a) (xn b)).mp (hmem_le b a hab)
    have hnn : 0 ≤ ε * dist (xn b) (xn a) := mul_nonneg hε.le dist_nonneg
    linarith
  have hbddrange : BddBelow (Set.range (fun n => ψ (xn n))) := by
    refine ⟨-(‖f‖), ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hlb _
  have htend := tendsto_atTop_ciInf hanti hbddrange
  have hcauchy : CauchySeq (fun n => ψ (xn n)) := htend.cauchySeq
  have hxcauchy : CauchySeq xn := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hcauchy (ε * δ) (mul_pos hε hδ)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist : ∀ m' n' : ℕ, N ≤ m' → N ≤ n' → n' ≤ m' → dist (xn m') (xn n') < δ := by
      intro m' n' hm' hn' hmn'
      have hle2 := ((hSmem (xn n') (xn m')).mp (hmem_le m' n' hmn'))
      have hdi := hN m' hm' n' hn'
      rw [Real.dist_eq] at hdi
      have hanti' := hanti hmn'
      simp only [hψdef] at hle2 hdi hanti' ⊢
      rw [abs_of_nonpos (by linarith)] at hdi
      have hmul : ε * dist (xn m') (xn n') < ε * δ := by linarith
      exact lt_of_mul_lt_mul_left hmul hε.le
    rcases le_total m n with h | h
    · rw [dist_comm]; exact hdist n m hn hm h
    · exact hdist m n hm hn h
  obtain ⟨x1, hx1⟩ := CompleteSpace.complete (f := Filter.map xn Filter.atTop) hxcauchy
  have hx1' : Filter.Tendsto xn Filter.atTop (nhds x1) := hx1
  have hclosedS : ∀ n, IsClosed (S (xn n)) := by
    intro n
    have h1 : Continuous (fun z : ↥B => ψ z + ε * dist z (xn n)) :=
      hψcont.add (continuous_const.mul (continuous_id.dist continuous_const))
    have h4 : IsClosed {z : ↥B | ψ z + ε * dist z (xn n) ≤ ψ (xn n)} :=
      isClosed_le h1 continuous_const
    have heq : S (xn n) = {z : ↥B | ψ z + ε * dist z (xn n) ≤ ψ (xn n)} := by
      simp only [hSdef]
    rw [heq]; exact h4
  have hx1S : ∀ n, x1 ∈ S (xn n) := by
    intro n
    apply (hclosedS n).mem_of_tendsto hx1'
    rw [Filter.eventually_atTop]
    exact ⟨n, fun m hm => hmem_le m n hm⟩
  have hSsub : ∀ n, S x1 ⊆ S (xn n) := by
    intro n z hz
    rw [hSmem] at hz ⊢
    have hle1 := (hSmem (xn n) x1).mp (hx1S n)
    have htri := dist_triangle z x1 (xn n)
    have hmul := mul_le_mul_of_nonneg_left htri hε.le
    linarith
  have hSeq : S x1 ⊆ {x1} := by
    intro z hz
    have h1 : ∀ k, dist z (xn (k + 1)) ≤ ((1 / 2 : ℝ) ^ (k + 1)) / ε := by
      intro k
      have hzmem := hSsub (k + 1) hz
      have hle := ((hSmem (xn (k + 1)) z).mp hzmem)
      have hglt' := hglt k (xn k)
      rw [← hsucc k] at hglt'
      have hleS : sInf (ψ '' S (xn k)) ≤ ψ z := by
        apply csInf_le (hbdd _)
        exact ⟨z, hSsub k hz, rfl⟩
      have hmul : dist z (xn (k + 1)) * ε ≤ (1 / 2 : ℝ) ^ (k + 1) := by
        rw [mul_comm]; linarith
      exact (le_div_iff₀ hε).mpr hmul
    have hlim0 : Filter.Tendsto (fun k => ((1 / 2 : ℝ) ^ (k + 1)) / ε) Filter.atTop (nhds 0) := by
      have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      have hpow : Filter.Tendsto (fun k => (1 / 2 : ℝ) ^ (k + 1)) Filter.atTop (nhds 0) :=
        (Filter.tendsto_add_atTop_iff_nat 1).mpr hbase
      have hdiv := hpow.div_const ε
      simpa using hdiv
    have hT1 : Filter.Tendsto (fun k => dist (xn k) x1) Filter.atTop (nhds 0) := by
      have hconst : Filter.Tendsto (fun _ : ℕ => x1) Filter.atTop (nhds x1) :=
        tendsto_const_nhds
      have h := hx1'.dist hconst
      simpa [dist_self] using h
    have hT1s : Filter.Tendsto (fun k => dist (xn (k + 1)) x1) Filter.atTop (nhds 0) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr hT1
    have hlim : Filter.Tendsto (fun k => dist z (xn (k + 1)) + dist (xn (k + 1)) x1) Filter.atTop
        (nhds (0 + 0)) :=
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0 (fun k => dist_nonneg)
          (fun k => h1 k)).add hT1s
    have hle0 : dist z x1 ≤ 0 := by
      have h := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Filter.Eventually.of_forall (fun k => dist_triangle z (xn (k + 1)) x1))
      simpa using h
    have hze : z = x1 := dist_eq_zero.mp (le_antisymm hle0 dist_nonneg)
    exact Set.mem_singleton_iff.mpr hze
  refine ⟨(x1 : F), x1.2, fun b hb hne' => ?_⟩
  have hbS : (⟨b, hb⟩ : ↥B) ∉ S x1 := by
    intro h
    apply hne'
    have := Set.mem_singleton_iff.mp (hSeq h)
    exact congrArg Subtype.val this
  have hcon : ¬ (ψ (⟨b, hb⟩ : ↥B) + ε * dist (⟨b, hb⟩ : ↥B) x1 ≤ ψ x1) := by
    intro h
    apply hbS
    rwa [hSmem]
  have hlt : ψ x1 < ψ (⟨b, hb⟩ : ↥B) + ε * dist (⟨b, hb⟩ : ↥B) x1 := not_le.mp hcon
  have hdist : dist (⟨b, hb⟩ : ↥B) x1 = ‖b - (x1 : F)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
  simp only [hψdef] at hlt
  rw [hdist] at hlt
  linarith

-- Part 1 (real core): quantitative Bishop-Phelps lemma for a real Banach space.
-- For `‖f‖ = 1` and `0 < ε ≤ 1/10`, there are `‖g‖ = 1` and `x1 ∈ B` with
-- `g x1 = 1` and `‖f - g‖ ≤ 6ε`.
private theorem bishop_phelps_real_core
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : StrongDual ℝ F) (hf : ‖f‖ = 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ g : StrongDual ℝ F, ∃ x1 ∈ Metric.closedBall (0 : F) 1,
      ‖g‖ = 1 ∧ g x1 = 1 ∧ ‖f - g‖ ≤ 6 * ε := by
  -- 1a: pick y with ‖y‖ < 1 and f y > 1 - ε.
  obtain ⟨y, hyn, hyf⟩ : ∃ y : F, ‖y‖ < 1 ∧ 1 - ε < f y := by
    obtain ⟨y0, hy0n, hy0f⟩ := ContinuousLinearMap.exists_lt_apply_of_lt_opNorm f
      (show (1 : ℝ) - ε < ‖f‖ by rw [hf]; linarith)
    rw [Real.norm_eq_abs] at hy0f
    rcases lt_or_ge 0 (f y0) with hpos | hneg
    · exact ⟨y0, hy0n, by rwa [abs_of_nonneg (le_of_lt hpos)] at hy0f⟩
    · refine ⟨-y0, by rwa [norm_neg], ?_⟩
      rw [f.map_neg]
      rwa [abs_of_nonpos hneg] at hy0f
  have hyB : y ∈ Metric.closedBall (0 : F) 1 :=
    mem_closedBall_zero_iff.mpr (le_of_lt hyn)
  have hfyK : ε * ‖y‖ < f y := by
    have e1 : ε * ‖y‖ < ε * 1 := mul_lt_mul_of_pos_left hyn hε0
    have e2 : ε * 1 ≤ 1 - ε := by linarith [hε10]
    linarith [hyf]
  have hfb : ∀ x : F, |f x| ≤ ‖x‖ := by
    intro x
    calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ = ‖x‖ := by rw [hf, one_mul]
  -- 1b: Ekeland point.
  obtain ⟨x1, hx1B, hx1min⟩ := ekeland_linear_aux f hε0 hyB
  -- 1c: the open convex set s and the cone K.
  set s : Set F := {w | ε * ‖w - x1‖ < f w - f x1} with hsdef
  have hs_mem : ∀ w : F, w ∈ s ↔ ε * ‖w - x1‖ < f w - f x1 := by
    intro w; simp only [hsdef, Set.mem_ofPred_eq]
  have hs_open : IsOpen s := by
    have hL : Continuous (fun w : F => ε * ‖w - x1‖) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm)
    have hR : Continuous (fun w : F => f w - f x1) :=
      f.continuous.sub continuous_const
    rw [hsdef]
    exact isOpen_lt hL hR
  have hs_conv : Convex ℝ s := by
    intro a ha b hb x y hx hy hxy
    rw [hs_mem] at ha hb ⊢
    have hdecomp : (x • a + y • b) - x1 = x • (a - x1) + y • (b - x1) := by
      have h1 : x • x1 + y • x1 = x1 := by rw [← add_smul, hxy, one_smul]
      have h2 : (x • a + y • b) - (x • x1 + y • x1)
          = x • (a - x1) + y • (b - x1) := by
        simp only [smul_sub]
        abel
      rwa [h1] at h2
    have hfadd : f (x • a + y • b) = x * f a + y * f b := by
      rw [f.map_add, f.map_smul, f.map_smul, smul_eq_mul, smul_eq_mul]
    have hn1 : ‖x • (a - x1)‖ = x * ‖a - x1‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx]
    have hn2 : ‖y • (b - x1)‖ = y * ‖b - x1‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hy]
    have htri : ‖x • (a - x1) + y • (b - x1)‖ ≤ x * ‖a - x1‖ + y * ‖b - x1‖ := by
      calc ‖x • (a - x1) + y • (b - x1)‖ ≤ ‖x • (a - x1)‖ + ‖y • (b - x1)‖ :=
            norm_add_le _ _
        _ = x * ‖a - x1‖ + y * ‖b - x1‖ := by rw [hn1, hn2]
    have key : x * (ε * ‖a - x1‖) + y * (ε * ‖b - x1‖)
        < x * (f a - f x1) + y * (f b - f x1) := by
      rcases eq_or_lt_of_le hx with rfl | hxpos
      · rw [zero_add] at hxy
        subst hxy
        simpa using hb
      · have e1 : x * (ε * ‖a - x1‖) < x * (f a - f x1) :=
          mul_lt_mul_of_pos_left ha hxpos
        have e2 : y * (ε * ‖b - x1‖) ≤ y * (f b - f x1) :=
          mul_le_mul_of_nonneg_left hb.le hy
        linarith
    have hmul : ε * ‖x • (a - x1) + y • (b - x1)‖
        ≤ x * (ε * ‖a - x1‖) + y * (ε * ‖b - x1‖) := by
      have h := mul_le_mul_of_nonneg_left htri hε0.le
      linear_combination h
    have heq : x * (f a - f x1) + y * (f b - f x1)
        = (x * f a + y * f b) - f x1 := by
      have hrr : x * (f a - f x1) + y * (f b - f x1)
          = (x * f a + y * f b) - (x + y) * f x1 := by ring
      rw [hrr, hxy, one_mul]
    rw [hdecomp, hfadd]
    linarith [hmul, key, heq]
  have hdisj : Disjoint s (Metric.closedBall (0 : F) 1) := by
    rw [Set.disjoint_left]
    intro w hws hwB
    rw [hs_mem] at hws
    by_cases heq : w = x1
    · subst heq
      simp at hws
    · have hlt := hx1min w hwB heq
      linarith
  have hKmem : ∀ z : F, ε * ‖z‖ < f z → x1 + z ∈ s := by
    intro z hz
    rw [hs_mem]
    have e1 : x1 + z - x1 = z := add_sub_cancel_left x1 z
    have e2 : f (x1 + z) - f x1 = f z := by
      rw [f.map_add]
      exact add_sub_cancel_left _ _
    rw [e1, e2]
    exact hz
  have htyK : ∀ t : ℝ, 0 < t → ε * ‖t • y‖ < f (t • y) := by
    intro t ht
    have n1 : ‖t • y‖ = t * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have m1 : f (t • y) = t * f y := by rw [f.map_smul, smul_eq_mul]
    rw [n1, m1]
    have e : ε * (t * ‖y‖) = t * (ε * ‖y‖) := by ring
    rw [e]
    exact mul_lt_mul_of_pos_left hfyK ht
  -- 1d: separation.
  obtain ⟨h, u, hlt, hle⟩ := geometric_hahn_banach_open hs_conv hs_open
    (convex_closedBall (0 : F) 1) hdisj
  have hi : ∀ z : F, ε * ‖z‖ < f z → h z < 0 := by
    intro z hz
    have h1 := hlt _ (hKmem z hz)
    have h2 := hle _ hx1B
    have h3 : h (x1 + z) = h x1 + h z := h.map_add _ _
    linarith
  have hii : h x1 ≤ u := by
    by_contra hcon
    have hcon' : u < h x1 := lt_of_not_ge hcon
    set t : ℝ := (h x1 - u) / (|h y| + 1) with htdef
    have ht : 0 < t := div_pos (by linarith) (by positivity)
    have hmem : x1 + t • y ∈ s := hKmem _ (htyK t ht)
    have hltm := hlt _ hmem
    have hval : h (x1 + t • y) = h x1 + t * h y := by
      rw [h.map_add, h.map_smul, smul_eq_mul]
    have htd : t * |h y| < h x1 - u := by
      have hd1 : (0 : ℝ) < |h y| + 1 := by positivity
      have hc : 0 < h x1 - u := by linarith
      calc t * |h y| = (h x1 - u) * |h y| / (|h y| + 1) := by rw [htdef]; ring
        _ < h x1 - u := by
          rw [div_lt_iff₀ hd1]
          have hrr : (h x1 - u) * (|h y| + 1)
              = (h x1 - u) * |h y| + (h x1 - u) := by ring
          linarith
    have hlo : -(t * |h y|) ≤ t * h y := by
      have hmul := mul_le_mul_of_nonneg_left (neg_abs_le (h y)) ht.le
      rwa [mul_neg] at hmul
    linarith
  have hne0 : h ≠ 0 := by
    intro h0
    have hhy := hi y hfyK
    rw [h0] at hhy
    have h00 : (0 : StrongDual ℝ F) y = 0 := by simp
    rw [h00] at hhy
    exact lt_irrefl _ hhy
  set c : ℝ := 1 / ‖h‖ with hcdef
  have hcpos : 0 < c := one_div_pos.mpr (norm_pos_iff.mpr hne0)
  set g : StrongDual ℝ F := -(c • h) with hgdef
  have hg_app : ∀ x : F, g x = -(c * h x) := by
    intro x
    rw [hgdef]
    simp [smul_eq_mul]
  have hg_norm : ‖g‖ = 1 := by
    have hch : ‖c • h‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hcdef,
        one_div_mul_cancel (ne_of_gt (norm_pos_iff.mpr hne0))]
    rw [hgdef, norm_neg]
    exact hch
  have hgK : ∀ z : F, ε * ‖z‖ < f z → 0 < g z := by
    intro z hz
    have hhz := hi z hz
    rw [hg_app]
    have hmul := mul_neg_of_pos_of_neg hcpos hhz
    linarith
  have hgb : ∀ b ∈ Metric.closedBall (0 : F) 1, g b ≤ g x1 := by
    intro b hb
    have h1 := hle b hb
    have h2 : h x1 = u := le_antisymm hii (hle x1 hx1B)
    rw [hg_app b, hg_app x1]
    have h3 : c * h x1 ≤ c * h b :=
      mul_le_mul_of_nonneg_left (by linarith : h x1 ≤ h b) hcpos.le
    linarith
  have hg0 : 0 ≤ g x1 := by
    have hmem : (0 : F) ∈ Metric.closedBall (0 : F) 1 := by simp
    have hle0 := hgb 0 hmem
    simpa using hle0
  have hbound : ∀ x : F, ‖g x‖ ≤ g x1 * ‖x‖ := by
    intro x
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hc : 0 < (1 : ℝ) / ‖x‖ := one_div_pos.mpr hxpos
      have hB1 : (1 / ‖x‖) • x ∈ Metric.closedBall (0 : F) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        exact le_of_eq (one_div_mul_cancel (ne_of_gt hxpos))
      have hB2 : (1 / ‖x‖) • (-x) ∈ Metric.closedBall (0 : F) 1 := by
        have heq : (1 / ‖x‖) • (-x) = -((1 / ‖x‖) • x) := smul_neg _ _
        rw [heq, mem_closedBall_zero_iff, norm_neg]
        exact mem_closedBall_zero_iff.mp hB1
      have h1 := hgb _ hB1
      have h2 := hgb _ hB2
      have g1 : g ((1 / ‖x‖) • x) = (1 / ‖x‖) * g x := by
        rw [g.map_smul, smul_eq_mul]
      have g2 : g ((1 / ‖x‖) • (-x)) = -((1 / ‖x‖) * g x) := by
        rw [smul_neg, g.map_neg, g1]
      have habs : |(1 / ‖x‖) * g x| ≤ g x1 := by
        rw [abs_le]
        constructor <;> linarith [h1, h2, g1, g2]
      have hfin : |g x| ≤ g x1 * ‖x‖ := by
        have e : (1 / ‖x‖) * ‖x‖ = 1 := one_div_mul_cancel (ne_of_gt hxpos)
        have e2 : (1 / ‖x‖) * |g x| * ‖x‖ = |g x| := by
          calc (1 / ‖x‖) * |g x| * ‖x‖ = |g x| * ((1 / ‖x‖) * ‖x‖) := by ring
            _ = |g x| * 1 := by rw [e]
            _ = |g x| := mul_one _
        have e3 := mul_le_mul_of_nonneg_right habs hxpos.le
        rw [abs_mul, abs_of_pos hc] at e3
        rwa [e2] at e3
      rw [Real.norm_eq_abs]
      exact hfin
  have hg_op : ‖g‖ ≤ g x1 := ContinuousLinearMap.opNorm_le_bound g hg0 hbound
  have hgx1_le : g x1 ≤ 1 := by
    have h1 := g.le_opNorm x1
    have h2 : ‖x1‖ ≤ 1 := mem_closedBall_zero_iff.mp hx1B
    rw [hg_norm] at h1
    calc g x1 ≤ |g x1| := le_abs_self _
      _ = ‖g x1‖ := (Real.norm_eq_abs _).symm
      _ ≤ 1 * ‖x1‖ := h1
      _ ≤ 1 := by rw [one_mul]; exact h2
  have hgx1 : g x1 = 1 := le_antisymm hgx1_le (by rwa [hg_norm] at hg_op)
  -- 1e: Phelps estimate.
  set δ : ℝ := ε / (1 - 2 * ε) with hδdef
  have h12 : (0 : ℝ) < 1 - 2 * ε := by linarith [hε10]
  have h12ne : (1 : ℝ) - 2 * ε ≠ 0 := ne_of_gt h12
  have hδpos : 0 < δ := div_pos hε0 h12
  have hδle : δ ≤ 5 * ε / 4 := by
    have h10 : (0 : ℝ) ≤ 1 - 10 * ε := by linarith [hε10]
    have hprod : (0 : ℝ) ≤ ε * (1 - 10 * ε) := mul_nonneg hε0.le h10
    rw [hδdef, div_le_iff₀ h12]
    nlinarith [hprod]
  have hker : ∀ z : F, f z = 0 → |g z| ≤ δ * ‖z‖ := by
    intro z hz0
    by_cases hz : z = 0
    · subst hz
      simp
    · have htz : 0 < δ * ‖z‖ := mul_pos hδpos (norm_pos_iff.mpr hz)
      set t : ℝ := δ * ‖z‖ with htdef
      have e2 : t * (1 - ε) = ε * t + ε * ‖z‖ := by
        have hd : δ * (1 - 2 * ε) = ε := by
          rw [hδdef]
          exact div_mul_cancel₀ _ h12ne
        have key : t * (1 - ε) - (ε * t + ε * ‖z‖)
            = ‖z‖ * (δ * (1 - 2 * ε) - ε) := by rw [htdef]; ring
        rw [hd] at key
        simp at key
        linarith
      have e3 : t * (1 - ε) < t * f y :=
        mul_lt_mul_of_pos_left (by linarith [hyf]) htz
      have e5 : ‖t • y‖ ≤ t := by
        have n1 : ‖t • y‖ = t * ‖y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos htz]
        have hy1 : ‖y‖ ≤ 1 := le_of_lt hyn
        calc ‖t • y‖ = t * ‖y‖ := n1
          _ ≤ t * 1 := mul_le_mul_of_nonneg_left hy1 htz.le
          _ = t := mul_one _
      have hmem1 : ε * ‖t • y + z‖ < f (t • y + z) := by
        have e1 : f (t • y + z) = t * f y := by
          rw [f.map_add, f.map_smul, smul_eq_mul, hz0, add_zero]
        have e4 : ‖t • y + z‖ ≤ ‖t • y‖ + ‖z‖ := norm_add_le _ _
        have e6 : ε * ‖t • y + z‖ ≤ ε * (‖t • y‖ + ‖z‖) :=
          mul_le_mul_of_nonneg_left e4 hε0.le
        have e5' : ε * ‖t • y‖ ≤ ε * t :=
          mul_le_mul_of_nonneg_left e5 hε0.le
        linarith [e1, e2, e3, e5', e6]
      have hmem2 : ε * ‖t • y - z‖ < f (t • y - z) := by
        have e1 : f (t • y - z) = t * f y := by
          rw [f.map_sub, f.map_smul, smul_eq_mul, hz0, sub_zero]
        have e4 : ‖t • y - z‖ ≤ ‖t • y‖ + ‖z‖ := norm_sub_le _ _
        have e6 : ε * ‖t • y - z‖ ≤ ε * (‖t • y‖ + ‖z‖) :=
          mul_le_mul_of_nonneg_left e4 hε0.le
        have e5' : ε * ‖t • y‖ ≤ ε * t :=
          mul_le_mul_of_nonneg_left e5 hε0.le
        linarith [e1, e2, e3, e5', e6]
      have g1 := hgK _ hmem1
      have g2 := hgK _ hmem2
      have a1 : g (t • y + z) = t * g y + g z := by
        rw [g.map_add, g.map_smul, smul_eq_mul]
      have a2 : g (t • y - z) = t * g y - g z := by
        rw [g.map_sub, g.map_smul, smul_eq_mul]
      have hgy : g y ≤ 1 := by
        have h1 := g.le_opNorm y
        rw [hg_norm] at h1
        have hy1 : ‖y‖ ≤ 1 := le_of_lt hyn
        calc g y ≤ ‖g y‖ := le_trans (le_abs_self _) (le_of_eq (Real.norm_eq_abs _))
          _ ≤ 1 * ‖y‖ := h1
          _ ≤ 1 := by rw [one_mul]; exact hy1
      have hgy1 : t * g y ≤ t * 1 :=
        mul_le_mul_of_nonneg_left hgy htz.le
      have habs : |g z| < t := by
        rw [abs_lt]
        constructor <;> linarith [g1, g2, a1, a2, hgy1]
      exact le_of_lt habs
  have hfy_pos : 0 < f y := by linarith [hyf, hε10]
  have hfy_ne : f y ≠ 0 := ne_of_gt hfy_pos
  set y0 : F := (1 / f y) • y with hy0def
  have hfy0 : f y0 = 1 := by
    rw [hy0def, f.map_smul, smul_eq_mul, one_div_mul_cancel hfy_ne]
  have hy0norm : ‖y0‖ ≤ 10 / 9 := by
    have n1 : ‖y0‖ = (1 / f y) * ‖y‖ := by
      rw [hy0def, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hfy_pos)]
    have h9 : (0 : ℝ) < 1 - ε := by linarith [hε10]
    have e1 : (1 : ℝ) / f y ≤ 1 / (1 - ε) :=
      one_div_le_one_div_of_le h9 (by linarith [hyf])
    have e2 : (1 : ℝ) / (1 - ε) ≤ 10 / 9 := by
      rw [div_le_iff₀ h9]
      linarith [hε10]
    have e3 : (0 : ℝ) ≤ 1 / (1 - ε) := le_of_lt (one_div_pos.mpr h9)
    calc ‖y0‖ = (1 / f y) * ‖y‖ := n1
      _ ≤ 1 / (1 - ε) * 1 :=
          mul_le_mul e1 (le_of_lt hyn) (norm_nonneg _) e3
      _ = 1 / (1 - ε) := mul_one _
      _ ≤ 10 / 9 := e2
  set lam : ℝ := g y0 with hlamdef
  have hlam_pos : 0 < lam := by
    rw [hlamdef, hy0def, g.map_smul, smul_eq_mul]
    exact mul_pos (one_div_pos.mpr hfy_pos) (hgK y hfyK)
  have e0 : ∀ x : F, (g - lam • f) x = g x - lam * f x := by
    intro x
    have hsm : ((lam • f : StrongDual ℝ F)) x = lam * f x := by simp [smul_eq_mul]
    change g x - (lam • f) x = g x - lam * f x
    rw [hsm]
  have hmain : ∀ x : F, ‖(g - lam • f) x‖ ≤ (δ * (1 + ‖y0‖)) * ‖x‖ := by
    intro x
    have e1 : f (x - (f x) • y0) = 0 := by
      rw [f.map_sub, f.map_smul, smul_eq_mul, hfy0, mul_one, sub_self]
    have e2 := hker _ e1
    have e3 : g (x - (f x) • y0) = g x - lam * f x := by
      rw [g.map_sub, g.map_smul, smul_eq_mul, hlamdef]
      ring
    have e4 : ‖x - (f x) • y0‖ ≤ (1 + ‖y0‖) * ‖x‖ := by
      have n1 : ‖(f x) • y0‖ = |f x| * ‖y0‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      calc ‖x - (f x) • y0‖ ≤ ‖x‖ + ‖(f x) • y0‖ := norm_sub_le _ _
        _ = ‖x‖ + |f x| * ‖y0‖ := by rw [n1]
        _ ≤ ‖x‖ + ‖x‖ * ‖y0‖ := by
          have hmul := mul_le_mul_of_nonneg_right (hfb x) (norm_nonneg y0)
          linarith
        _ = (1 + ‖y0‖) * ‖x‖ := by ring
    have e5 : δ * ‖x - (f x) • y0‖ ≤ (δ * (1 + ‖y0‖)) * ‖x‖ := by
      have hmul := mul_le_mul_of_nonneg_left e4 hδpos.le
      linear_combination hmul
    rw [Real.norm_eq_abs, e0, ← e3]
    linarith [e2, e5]
  have hC_le : δ * (1 + ‖y0‖) ≤ 3 * ε := by
    have h1 : (1 : ℝ) + ‖y0‖ ≤ 19 / 9 := by linarith [hy0norm]
    have h2 := mul_le_mul hδle h1 (by positivity) (by linarith [hε0.le])
    have h3 : (5 : ℝ) * ε / 4 * (19 / 9) ≤ 3 * ε := by
      have heq : (5 : ℝ) * ε / 4 * (19 / 9) = (95 / 36) * ε := by ring
      rw [heq]
      linarith [hε0.le]
    linarith
  have hnorm1 : ‖g - lam • f‖ ≤ 3 * ε :=
    le_trans (ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hδpos.le (by positivity)) hmain) hC_le
  have hlam1 : |1 - lam| ≤ 3 * ε := by
    have h1 := abs_norm_sub_norm_le g (lam • f)
    rw [hg_norm] at h1
    have h2 : ‖lam • f‖ = lam := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam_pos, hf, mul_one]
    rw [h2] at h1
    linarith [hnorm1]
  have hfinal : ‖f - g‖ ≤ 6 * ε := by
    have hbound : ∀ x : F, ‖(f - g) x‖ ≤ (6 * ε) * ‖x‖ := by
      intro x
      have e0' : (f - g) x = f x - g x := rfl
      have e1 : f x - g x = (1 - lam) * f x - (g x - lam * f x) := by ring
      have e2 : |(1 - lam) * f x| ≤ |1 - lam| * ‖x‖ := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hfb x) (abs_nonneg _)
      have e3 : |g x - lam * f x| ≤ (3 * ε) * ‖x‖ := by
        have hmx := hmain x
        rw [Real.norm_eq_abs, e0 x] at hmx
        have hmul := mul_le_mul_of_nonneg_right hC_le (norm_nonneg x)
        linarith
      have tri : |(1 - lam) * f x - (g x - lam * f x)|
          ≤ |(1 - lam) * f x| + |g x - lam * f x| := by
        have h := abs_add_le ((1 - lam) * f x) (-(g x - lam * f x))
        rwa [← sub_eq_add_neg, abs_neg] at h
      have e4 : |(1 - lam) * f x| ≤ (3 * ε) * ‖x‖ := by
        have hmul := mul_le_mul_of_nonneg_right hlam1 (norm_nonneg x)
        linarith [e2, hmul]
      rw [Real.norm_eq_abs, e0', e1]
      linarith [tri, e4, e3]
    have hle : ‖f - g‖ ≤ 6 * ε :=
      ContinuousLinearMap.opNorm_le_bound _ (by linarith [hε0.le]) hbound
    exact hle
  exact ⟨g, x1, hx1B, hg_norm, hgx1, hfinal⟩

-- Part 2 (real density): norm-attaining functionals are dense in `StrongDual ℝ F`.
private theorem bishop_phelps_real_dense
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    Dense { f : StrongDual ℝ F | ∃ x ∈ Metric.closedBall (0 : F) 1, ‖f x‖ = ‖f‖ } := by
  rw [Metric.dense_iff]
  intro f r hr
  by_cases hf0 : f = 0
  · subst hf0
    refine ⟨0, Metric.mem_ball.mpr ?_, (0 : F), ?_, ?_⟩
    · rw [dist_self]
      exact hr
    · simp
    · simp
  · have hfr : 0 < ‖f‖ := norm_pos_iff.mpr hf0
    have hfn : (‖f‖ : ℝ) ≠ 0 := ne_of_gt hfr
    set fn : StrongDual ℝ F := (1 / ‖f‖) • f with hfndef
    have hfn_norm : ‖fn‖ = 1 := by
      rw [hfndef, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hfr),
        one_div_mul_cancel hfn]
    set ε : ℝ := min (1 / 10) (r / (7 * ‖f‖)) with hεdef
    have hε0 : 0 < ε :=
      lt_min (by norm_num) (div_pos hr (mul_pos (by norm_num) hfr))
    have hε10 : ε ≤ 1 / 10 := min_le_left _ _
    obtain ⟨g1, x1, hx1B, hg1, hg1x, hfg⟩ :=
      bishop_phelps_real_core fn hfn_norm hε0 hε10
    set g : StrongDual ℝ F := ‖f‖ • g1 with hgdef
    have hgx : g x1 = ‖f‖ := by
      rw [hgdef]
      change ‖f‖ • g1 x1 = _
      rw [hg1x, smul_eq_mul, mul_one]
    have hg_norm : ‖g‖ = ‖f‖ := by
      rw [hgdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hg1,
        mul_one]
    have hmem : g ∈ { f : StrongDual ℝ F |
        ∃ x ∈ Metric.closedBall (0 : F) 1, ‖f x‖ = ‖f‖ } := by
      refine ⟨x1, hx1B, ?_⟩
      rw [hgx, hg_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hfg_bound : ‖f - g‖ < r := by
      have e1 : f = ‖f‖ • fn := by
        rw [hfndef, ← mul_smul]
        have hcan : ‖f‖ * (1 / ‖f‖) = 1 := by
          rw [mul_comm]
          exact one_div_mul_cancel hfn
        rw [hcan, one_smul]
      have e2 : f - g = ‖f‖ • (fn - g1) := by
        conv_lhs => rw [e1]
        rw [hgdef, smul_sub]
      have e3 : ‖f - g‖ = ‖f‖ * ‖fn - g1‖ := by
        rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have e6 : ‖f‖ * (6 * ε) ≤ ‖f‖ * (6 * (r / (7 * ‖f‖))) := by
        have h3 : (6 : ℝ) * ε ≤ 6 * (r / (7 * ‖f‖)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      have h4 : ‖f‖ * (6 * (r / (7 * ‖f‖))) < r := by
        have h7 : (7 : ℝ) * ‖f‖ ≠ 0 := mul_ne_zero (by norm_num) hfn
        field_simp
        nlinarith [mul_pos hr hfr]
      rw [e3]
      have e4 : ‖f‖ * ‖fn - g1‖ ≤ ‖f‖ * (6 * ε) :=
        mul_le_mul_of_nonneg_left hfg (norm_nonneg _)
      linarith
    refine ⟨g, Metric.mem_ball.mpr ?_, hmem⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact hfg_bound

/--
**Bishop–Phelps theorem.** Let $E$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, with dual space $E^*$. The functionals that attain their norm on the closed unit
ball, that is, the $f \in E^*$ such that $|f(x)| = \|f\|$ for some $x \in E$ with
$\|x\| \le 1$, form a dense subset of $E^*$ in the norm topology.

Proves `Wanted` entry `bishop_phelps`.

Source: E. Bishop and R. R. Phelps, Bull. Amer. Math. Soc. 67 (1961)
97-98 and Pacific J. Math. 1961; Bollobas quantitative version; Lean states `RCLike` Banach case
as density of attaining functionals.
-/
theorem bishop_phelps
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    Dense { f : StrongDual 𝕜 E | ∃ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ = ‖f‖ } := by
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  have hst : IsScalarTower ℝ 𝕜 E := inferInstance
  rw [Metric.dense_iff]
  intro f r hr
  set fr : StrongDual ℝ E := RCLike.reCLM.comp (f.restrictScalars ℝ) with hfrdef
  have hfr_app : ∀ x : E, fr x = RCLike.re (f x) := by
    intro x
    simp [hfrdef, RCLike.reCLM_apply]
  have hdense := bishop_phelps_real_dense (F := E)
  rw [Metric.dense_iff] at hdense
  obtain ⟨gr, hgrball, x1, hx1B, hgratt⟩ := hdense fr r hr
  set g : StrongDual 𝕜 E := gr.extendRCLike with hgdef
  have hext : fr.extendRCLike = f := by
    apply ContinuousLinearMap.ext
    intro x
    apply RCLike.ext_iff.mpr
    constructor
    · rw [StrongDual.re_extendRCLike_apply, hfr_app]
    · rw [StrongDual.im_extendRCLike_apply, hfr_app]
      have e1 : f ((RCLike.I : 𝕜) • x) = (RCLike.I : 𝕜) • f x := f.map_smul _ _
      rw [e1]
      have e2 : (RCLike.I : 𝕜) • f x = RCLike.I * f x := smul_eq_mul _ _
      rw [e2, RCLike.I_mul_re, neg_neg]
  have hnorm : ‖f - g‖ = ‖fr - gr‖ := by
    have e : f - g = StrongDual.extendRCLikeₗ (fr - gr) := by
      rw [map_sub, StrongDual.extendRCLikeₗ_apply, StrongDual.extendRCLikeₗ_apply,
        hext, ← hgdef]
    rw [e, StrongDual.extendRCLikeₗ_apply, StrongDual.norm_extendRCLike]
  have hdist : dist f g < r := by
    have h1 := Metric.mem_ball.mp hgrball
    rw [dist_eq_norm, norm_sub_rev] at h1
    rw [dist_eq_norm, hnorm]
    exact h1
  have h1 : ‖gr‖ = ‖g‖ := by rw [hgdef, StrongDual.norm_extendRCLike]
  have h5 : |RCLike.re (g x1)| = ‖g‖ := by
    have e : RCLike.re (g x1) = gr x1 := by
      rw [hgdef, StrongDual.re_extendRCLike_apply]
    rw [e, ← Real.norm_eq_abs, hgratt, h1]
  have h4 : |RCLike.re (g x1)| ≤ ‖g x1‖ := RCLike.abs_re_le_norm _
  have h2 : ‖g x1‖ ≤ ‖g‖ := by
    have hle := g.le_opNorm x1
    have h3 : ‖x1‖ ≤ 1 := mem_closedBall_zero_iff.mp hx1B
    calc ‖g x1‖ ≤ ‖g‖ * ‖x1‖ := hle
      _ ≤ ‖g‖ * 1 := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ‖g‖ := mul_one _
  refine ⟨g, Metric.mem_ball.mpr ?_, x1, hx1B, le_antisymm h2 ?_⟩
  · rw [dist_comm]
    exact hdist
  · linarith [h5, h4]

end MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted
end
