/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.PotentialHeatSpatial
import MathlibExt.Analysis.Calculus.IteratedDerivPartial
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Time derivatives and joint smoothness of potential-heat evolution

Differentiating the already established spatially differentiated restart
identity supplies actual time derivatives, without presuming mixed commutation.
For jointly smooth potentials whose Fréchet derivatives have separate uniform
strip bounds, these identities imply joint positive-time smoothness of every
spatial jet of the actual Volterra solution. Initial data remain merely
continuous with exponential growth.

The classical starting points are Gaussian differentiation and Duhamel's
formula in James Nolen, *Partial Differential Equations and Diffusion Processes*,
§§2.3–2.4, https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf.
The weighted restart and simultaneous jet regularity arguments here derive the
stated conclusions from the estimates proved in the imported modules.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ContDiff
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

private theorem heat_initial_jet_hasDerivAt_time {g : ℝ → ℝ} {ν t : ℝ} {n : ℕ}
    (hg : ContDiff ℝ (n + 2) g) (hgg : ∀ k ≤ n + 2, HasExpGrowth (iteratedDeriv k g))
    (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatSolution (iteratedDeriv n g) (ν*s) x)
      (ν * heatSolution (iteratedDeriv (n + 2) g) (ν*t) x) t := by
  have hn : n ≤ n + 2 := by omega
  have hc := (contDiff_nat_iff_iteratedDeriv.mp hg).1 n hn
  have h := heatSolution_hasDerivAt_time_scaled_of_exp_growth hc.aestronglyMeasurable
    (hgg n hn) hν ht x
  have he : heatSolution (iteratedDeriv n g) (ν*t) = iteratedDeriv n (heatSolution g (ν*t)) :=
    (funext (heatSolution_iteratedDeriv_of_exp_growth (hg.of_le (by exact_mod_cast hn))
      (fun k hk => hgg k (hk.trans hn)) (ν*t))).symm
  rw [he, ← iteratedDeriv_succ, ← iteratedDeriv_succ] at h
  simpa only [heatSolution_iteratedDeriv_of_exp_growth hg hgg] using h

/-- The actual nth spatial derivative satisfies its differentiated potential-heat
identity at every interior time. Two further spatial potential derivatives
suffice; no potential time derivative or initial derivative is assumed. -/
theorem potentialHeatSolution_iteratedDeriv_hasDerivAt_time
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t : ℝ} {n : ℕ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ (n + 2) (q s))
    (hqc : ∀ k ≤ n + 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n + 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => iteratedDeriv n (potentialHeatSolution ν q g r) x)
      (ν * iteratedDeriv (n + 2) (potentialHeatSolution ν q g t) x +
        iteratedDeriv n (fun y => q t y * potentialHeatSolution ν q g t y) x) t := by
  let a := t/2
  let f := fun s y => q (a+s) y * potentialHeatSolution ν q g (a+s) y
  have ha : 0 < a := half_pos ht.1
  have hat : a < t := half_lt_self ht.1
  have haT : a ≤ T := hat.le.trans ht.2.le
  have hbt : t-a ∈ Ioo 0 (T-a) := ⟨sub_pos.mpr hat, sub_lt_sub_right ht.2 a⟩
  have hn : n ≤ n + 2 := by omega
  have hqs_k (k : ℕ) (hk : k ≤ n + 2) : ∀ s ∈ Icc 0 T, ContDiff ℝ k (q s) :=
    fun s hs => (hqs s hs).of_le (by exact_mod_cast hk)
  have hqc_k (k : ℕ) (hk : k ≤ n + 2) := fun j (hj : j ≤ k) => hqc j (hj.trans hk)
  have hqb_k (k : ℕ) (hk : k ≤ n + 2) := fun j (hj : j ≤ k) => hqb j (hj.trans hk)
  have hshift {s : ℝ} (hs : s ∈ Icc 0 (T-a)) : a+s ∈ Ioc 0 T :=
    ⟨add_pos_of_pos_of_nonneg ha hs.1, by linarith [hs.2]⟩
  have hfs : ∀ s ∈ Icc 0 (T-a), ContDiff ℝ (n + 2) (f s) := by
    intro s hs
    exact (hqs _ ⟨(hshift hs).1.le, (hshift hs).2⟩).mul
      (potentialHeatSolution_contDiff_space hν hqs hqc hqb hg hgg (hshift hs))
  have hfc (k : ℕ) (hk : k ≤ n + 2) :
      ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2) (Icc 0 (T-a) ×ˢ univ) :=
    potentialHeatSolution_forcing_iteratedDeriv_continuousOn hν (hqs_k k hk)
      (hqc_k k hk) (hqb_k k hk) hg hgg ha haT
  have hfg (k : ℕ) (hk : k ≤ n + 2) :
      HeatWholeLine.HasExpGrowthOnStrip (fun s y => iteratedDeriv k (f s) y) (T-a) :=
    potentialHeatSolution_forcing_iteratedDeriv_hasExpGrowthOnStrip hν (hqs_k k hk)
      (hqc_k k hk) (hqb_k k hk) hg hgg ha haT
  have hga := potentialHeatSolution_contDiff_space hν hqs hqc hqb hg hgg ⟨ha, haT⟩
  have hgb (k : ℕ) (hk : k ≤ n + 2) :
      HasExpGrowth (iteratedDeriv k (potentialHeatSolution ν q g a)) := by
    obtain ⟨M, c, hM, hc, hb⟩ := potentialHeatSolution_iteratedDeriv_hasExpGrowthOnStrip
      hν (hqs_k k hk) (hqc_k k hk) (hqb_k k hk) hg hgg ha haT
    exact ⟨M, c, hM, hc, fun y => by
      simpa only [add_zero] using hb 0 ⟨le_rfl, sub_nonneg.mpr haT⟩ y⟩
  have hp := heat_initial_jet_hasDerivAt_time hga hgb hν hbt.1 x
  have hd := heatDuhamel_iteratedDeriv_hasDerivAt_time hν hfs hfc hfg hbt x
  have hsum := hp.add hd
  have hre := potentialHeatSolution_iteratedDeriv_restart_mild hν hqs hqc hqb hg hgg
    ha hbt.1.le (show a+(t-a) ≤ T by linarith [ht.2]) x
  have hval :
      ν * heatSolution (iteratedDeriv (n + 2) (potentialHeatSolution ν q g a)) (ν*(t-a)) x +
        (iteratedDeriv n (f (t-a)) x +
          ν * heatDuhamel ν (fun s y => iteratedDeriv (n + 2) (f s) y) (t-a) x) =
        ν * iteratedDeriv (n + 2) (potentialHeatSolution ν q g t) x +
          iteratedDeriv n (fun y => q t y * potentialHeatSolution ν q g t y) x := by
    have htime : a+(t-a) = t := by ring
    dsimp only [f] at hre ⊢
    rw [htime] at hre ⊢
    rw [hre]
    ring
  rw [hval] at hsum
  have hlocal : HasDerivAt (fun r => iteratedDeriv n (potentialHeatSolution ν q g (a+r)) x)
      (ν * iteratedDeriv (n + 2) (potentialHeatSolution ν q g t) x +
        iteratedDeriv n (fun y => q t y * potentialHeatSolution ν q g t y) x) (t-a) := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hbt.1 hbt.2] with r hr
    have h := potentialHeatSolution_iteratedDeriv_restart_mild hν (hqs_k n hn)
      (hqc_k n hn) (hqb_k n hn) hg hgg ha hr.1.le (by linarith [hr.2]) x
    dsimp only [Pi.add_apply]
    rw [heatDuhamel_iteratedDeriv hν.le
      (fun s hs => (hfs s hs).of_le (by exact_mod_cast hn))
      (fun k hk => hfc k (hk.trans hn)) (fun k hk => hfg k (hk.trans hn))
      ⟨hr.1.le, hr.2.le⟩ x]
    exact h
  have hfinal := hlocal.comp t ((hasDerivAt_id t).sub_const a)
  simpa only [Function.comp_def, id_eq, mul_one, ← add_sub_assoc, add_sub_cancel_left] using hfinal

private theorem spatial_jet_contDiff {q : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ ∞ (Function.uncurry q)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv n (q p.1) p.2) :=
  hq.contDiff_iteratedDeriv_snd n

private theorem spatial_jet_bound {q : ℝ → ℝ → ℝ} {T : ℝ}
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (n : ℕ) :
    ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |iteratedDeriv n (q t) x| ≤ M := by
  obtain ⟨M, hM⟩ := hb n
  refine ⟨M, fun t ht x => ?_⟩
  have h := (hq.of_le (by simp : (n : WithTop ℕ∞) ≤ ∞)).norm_iteratedDeriv_snd_le (t,x)
  have he : |iteratedDeriv n (q t) x| ≤
      ‖iteratedFDeriv ℝ n (Function.uncurry q) (t,x)‖ := by
    simpa only [Real.norm_eq_abs] using h
  exact he.trans (hM (t,x) ⟨ht, mem_univ x⟩)

private theorem joint_contDiff_succ {u ut ux : ℝ → ℝ → ℝ} {s : Set (ℝ × ℝ)} {m : ℕ}
    (hs : IsOpen s)
    (hdt : ∀ p ∈ s, HasDerivAt (fun t => u t p.2) (ut p.1 p.2) p.1)
    (hdx : ∀ p ∈ s, HasDerivAt (u p.1) (ux p.1 p.2) p.2)
    (hct : ContDiffOn ℝ m (Function.uncurry ut) s)
    (hcx : ContDiffOn ℝ m (Function.uncurry ux) s) :
    ContDiffOn ℝ (m+1 : ℕ) (Function.uncurry u) s := by
  let D := fun p : ℝ × ℝ => ut p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    ux p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hfull (p : ℝ × ℝ) (hp : p ∈ s) : HasFDerivAt (Function.uncurry u) (D p) p := by
    have h := hasStrictFDerivAt_uncurry_coprod (f := u)
      (f₁ := fun t x => (1 : ℝ →L[ℝ] ℝ).smulRight (ut t x))
      (f₂ := fun t x => (1 : ℝ →L[ℝ] ℝ).smulRight (ux t x))
      (by
        filter_upwards [hs.mem_nhds hp] with v hv
        exact (hdt v hv).hasFDerivAt)
      (by
        filter_upwards [hs.mem_nhds hp] with v hv
        exact (hdx v hv).hasFDerivAt)
      (((contDiffOn_const.smulRight hct).continuousOn p hp).continuousAt (hs.mem_nhds hp))
      (((contDiffOn_const.smulRight hcx).continuousOn p hp).continuousAt (hs.mem_nhds hp))
    convert! h.hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro z
    change ut p.1 p.2 * z.1 + ux p.1 p.2 * z.2 =
      z.1 * ut p.1 p.2 + z.2 * ux p.1 p.2
    ring
  rw [show (↑(m+1) : WithTop ℕ∞) = (m : WithTop ℕ∞)+1 by simp,
    contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨fun p hp => (hfull p hp).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro hm
    simp at hm
  · have hc : ContDiffOn ℝ m D s :=
      (hct.smul contDiffOn_const).add (hcx.smul contDiffOn_const)
    exact hc.congr (fun p hp => (hfull p hp).fderiv)

private theorem spatial_slice_contDiff {q : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ ∞ (Function.uncurry q)) (n : ℕ) (s : ℝ) : ContDiff ℝ n (q s) := by
  have hc : ContDiff ℝ ∞ (q s) := by
    simpa only [Function.uncurry_def, Function.comp_def, id_eq] using
      hq.comp (contDiff_const.prodMk contDiff_id)
  exact hc.of_le (by simp)

private theorem potential_spatial_jets_contDiffOn {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (m k : ℕ) :
    ContDiffOn ℝ m (fun p : ℝ × ℝ => iteratedDeriv k (potentialHeatSolution ν q g p.1) p.2)
      (Ioo 0 T ×ˢ univ) := by
  have hqs (n : ℕ) (s : ℝ) (_ : s ∈ Icc 0 T) : ContDiff ℝ n (q s) :=
    spatial_slice_contDiff hq n s
  have hqc (n : ℕ) : ContinuousOn
      (fun p : ℝ × ℝ => iteratedDeriv n (q p.1) p.2) (Icc 0 T ×ˢ univ) :=
    (spatial_jet_contDiff hq n).continuous.continuousOn
  have hqb (n : ℕ) : ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv n (q s) x| ≤ M :=
    spatial_jet_bound hq hb n
  have hphi (n : ℕ) {s : ℝ} (hs : s ∈ Ioc 0 T) :
      ContDiff ℝ n (potentialHeatSolution ν q g s) :=
    potentialHeatSolution_contDiff_space hν (hqs n) (fun j _ => hqc j)
      (fun j _ => hqb j) hg hgg hs
  induction m generalizing k with
  | zero =>
    apply contDiffOn_zero.mpr
    exact (potentialHeatSolution_iteratedDeriv_continuousOn_pos hν (hqs k)
      (fun j _ => hqc j) (fun j _ => hqb j) hg hgg).mono
      (fun p hp => ⟨⟨hp.1.1, hp.1.2.le⟩, hp.2⟩)
  | succ m ih =>
    have hforcing : ContDiffOn ℝ m (fun p : ℝ × ℝ => iteratedDeriv k
        (fun y => q p.1 y * potentialHeatSolution ν q g p.1 y) p.2) (Ioo 0 T ×ˢ univ) := by
      have hc : ContDiffOn ℝ m (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (k+1),
          (k.choose i : ℝ) * iteratedDeriv i (q p.1) p.2 *
            iteratedDeriv (k-i) (potentialHeatSolution ν q g p.1) p.2) (Ioo 0 T ×ˢ univ) := by
        apply ContDiffOn.sum
        intro i _
        exact (contDiffOn_const.mul
          ((spatial_jet_contDiff hq i).of_le (by simp)).contDiffOn).mul (ih (k-i))
      apply hc.congr
      intro p hp
      exact iteratedDeriv_fun_mul (hqs k p.1 ⟨hp.1.1.le, hp.1.2.le⟩).contDiffAt
        (hphi k ⟨hp.1.1, hp.1.2.le⟩).contDiffAt
    apply joint_contDiff_succ (u := fun t x => iteratedDeriv k (potentialHeatSolution ν q g t) x)
      (ut := fun t x => ν * iteratedDeriv (k+2) (potentialHeatSolution ν q g t) x +
        iteratedDeriv k (fun y => q t y * potentialHeatSolution ν q g t y) x)
      (ux := fun t x => iteratedDeriv (k+1) (potentialHeatSolution ν q g t) x)
      (isOpen_Ioo.prod isOpen_univ)
    · intro p hp
      exact potentialHeatSolution_iteratedDeriv_hasDerivAt_time hν (hqs (k+2))
        (fun j _ => hqc j) (fun j _ => hqb j) hg hgg hp.1 p.2
    · intro p hp
      simpa only [iteratedDeriv_succ] using
        ((contDiff_nat_iff_iteratedDeriv.mp (hphi (k+1) ⟨hp.1.1, hp.1.2.le⟩)).2
          k (Nat.lt_succ_self k) p.2).hasDerivAt
    · exact (contDiffOn_const.mul (ih (k+2))).add hforcing
    · exact ih (k+1)

/-- Every actual spatial derivative of the constructed potential-heat solution
is jointly smooth at interior positive times when the potential is jointly
smooth with separately uniform bounds for every Fréchet derivative on the strip. -/
theorem potentialHeatSolution_iteratedDeriv_contDiffOn
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv k (potentialHeatSolution ν q g p.1) p.2)
      (Ioo 0 T ×ˢ univ) := by
  apply contDiffOn_infty.mpr
  intro m
  exact potential_spatial_jets_contDiffOn hν hq hb hg hgg m k

/-- The actual Volterra solution is jointly smooth on the open positive-time
strip for a bounded smooth potential and continuous exponentially growing data. -/
theorem potentialHeatSolution_contDiffOn
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) :
    ContDiffOn ℝ ∞ (Function.uncurry (potentialHeatSolution ν q g)) (Ioo 0 T ×ˢ univ) := by
  simpa only [iteratedDeriv_zero, Function.uncurry_def] using
    potentialHeatSolution_iteratedDeriv_contDiffOn hν hq hb hg hgg 0

/-- The constructed field satisfies the actual potential-heat time derivative
formula at interior times under two bounded continuous spatial potential derivatives. -/
theorem potentialHeatSolution_hasDerivAt_time
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => potentialHeatSolution ν q g r x)
      (ν * deriv (deriv (potentialHeatSolution ν q g t)) x +
        q t x * potentialHeatSolution ν q g t x) t := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    potentialHeatSolution_iteratedDeriv_hasDerivAt_time (n := 0) hν hqs hqc hqb hg hgg ht x

/-- A potential with the bounded smooth Fréchet-derivative hypotheses gives the
actual classical potential-heat equation for the constructed Volterra field. -/
theorem potentialHeatSolution_hasDerivAt_time_of_contDiff
    {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => potentialHeatSolution ν q g r x)
      (ν * deriv (deriv (potentialHeatSolution ν q g t)) x +
        q t x * potentialHeatSolution ν q g t x) t :=
  potentialHeatSolution_hasDerivAt_time hν (fun s _ => spatial_slice_contDiff hq 2 s)
    (fun k _ => (spatial_jet_contDiff hq k).continuous.continuousOn)
    (fun k _ => spatial_jet_bound hq hb k) hg hgg ht x

end MathlibExt.Analysis.PDE.HeatKernel
