/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatDuhamelDerivatives
public import MathlibExt.Analysis.PDE.HeatDuhamelSmoothing
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Repeated spatial differentiation of heat and Duhamel integrals

Finite-order derivative transfer preserves the actual iterated spatial
derivatives. Continuous differentiated forcing gains one further spatial
derivative under Duhamel integration at positive viscosity. Two further spatial
forcing derivatives give the actual time derivative of each differentiated
Duhamel field at interior times; no forcing time derivative is assumed.

The proofs iterate Gaussian differentiation and Duhamel differentiation.
For the classical formulas, see James Nolen, *Partial Differential Equations
and Diffusion Processes*, §§2.3–2.4, especially formula (4.42):
https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf.
The exponential-growth and finite-order statements here follow from the
weighted Gaussian and continuous-forcing estimates in the imported modules.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- Heat evolution commutes with every available spatial derivative when all
initial derivatives through that order have exponential growth. This includes
the stationary extension at nonpositive heat parameters. -/
theorem heatSolution_iteratedDeriv_of_exp_growth {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ n f) (hg : ∀ k ≤ n, HasExpGrowth (iteratedDeriv k f)) (t x : ℝ) :
    iteratedDeriv n (heatSolution f t) x = heatSolution (iteratedDeriv n f) t x := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    have hfn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hi : iteratedDeriv n (heatSolution f t) = heatSolution (iteratedDeriv n f) t :=
      funext (fun y => ih hfn (fun k hk => hg k (hk.trans (Nat.le_succ n))) y)
    rw [iteratedDeriv_succ, hi]
    have hgd : HasExpGrowth (deriv (iteratedDeriv n f)) := by
      rw [← iteratedDeriv_succ]
      exact hg (n + 1) le_rfl
    simpa only [iteratedDeriv_succ] using
      (heatSolution_hasDerivAt_deriv_of_exp_growth
        (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hf).2
        (hg n (Nat.le_succ n)) hgd t x).deriv

/-- Duhamel integration commutes with any finite number of spatial derivatives
when those forcing derivatives are jointly continuous and uniformly exponentially
bounded on the closed strip. No forcing time derivative is assumed. -/
theorem heatDuhamel_iteratedDeriv {f : ℝ → ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 ≤ ν) (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ n (f s))
    (hc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hg : ∀ k ≤ n, HeatWholeLine.HasExpGrowthOnStrip (fun s y => iteratedDeriv k (f s) y) T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    iteratedDeriv n (heatDuhamel ν f t) x =
      heatDuhamel ν (fun s y => iteratedDeriv n (f s) y) t x := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    have hfn : ∀ s ∈ Icc 0 T, ContDiff ℝ n (f s) :=
      fun s hs => (hf s hs).of_le (by exact_mod_cast Nat.le_succ n)
    have hi : iteratedDeriv n (heatDuhamel ν f t) =
        heatDuhamel ν (fun s y => iteratedDeriv n (f s) y) t :=
      funext (fun y => ih hfn (fun k hk => hc k (hk.trans (Nat.le_succ n)))
        (fun k hk => hg k (hk.trans (Nat.le_succ n))) y)
    rw [iteratedDeriv_succ, hi]
    apply HasDerivAt.deriv
    apply heatDuhamel_hasDerivAt_space (f := fun s y => iteratedDeriv n (f s) y)
      (fx := fun s y => iteratedDeriv (n + 1) (f s) y) hν
      (hc n (Nat.le_succ n)) (hc (n + 1) le_rfl)
      (hg n (Nat.le_succ n)) (hg (n + 1) le_rfl) ?_ ht x
    intro s hs y
    simpa only [iteratedDeriv_succ] using
      ((contDiff_nat_iff_iteratedDeriv.mp (hf s hs)).2 n (Nat.lt_succ_self n) y).hasDerivAt

/-- The transferred finite-order spatial derivative is jointly continuous on
the closed strip, including its zero initial value. -/
theorem heatDuhamel_iteratedDeriv_continuousOn {f : ℝ → ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T) (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ n (f s))
    (hc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hg : ∀ k ≤ n, HeatWholeLine.HasExpGrowthOnStrip (fun s y => iteratedDeriv k (f s) y) T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (heatDuhamel ν f p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  exact (heatDuhamel_continuousOn (f := fun s y => iteratedDeriv n (f s) y)
    hT (hc n le_rfl) (hg n le_rfl) ν).congr
      (fun p hp => heatDuhamel_iteratedDeriv hν hf hc hg hp.1 p.2)

/-- Transferring finitely many spatial derivatives preserves uniform
exponential growth on the closed time strip. -/
theorem heatDuhamel_iteratedDeriv_hasExpGrowthOnStrip {f : ℝ → ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T) (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ n (f s))
    (hc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hg : ∀ k ≤ n, HeatWholeLine.HasExpGrowthOnStrip (fun s y => iteratedDeriv k (f s) y) T) :
    HeatWholeLine.HasExpGrowthOnStrip (fun t x => iteratedDeriv n (heatDuhamel ν f t) x) T := by
  obtain ⟨M, c, hM, hc', hb⟩ := heatDuhamel_hasExpGrowthOnStrip
    (f := fun s y => iteratedDeriv n (f s) y) (hc n le_rfl) (hg n le_rfl) hν hT
  refine ⟨M, c, hM, hc', fun t ht x => ?_⟩
  dsimp only
  rw [heatDuhamel_iteratedDeriv hν hf hc hg ht x]
  exact hb t ht x

/-- Positive viscosity gains one additional spatial derivative after transferring
all available forcing derivatives. Only continuity, not differentiability, of
the last forcing derivative is required. -/
theorem heatDuhamel_hasDerivAt_iteratedDeriv {f : ℝ → ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 < ν) (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ n (f s))
    (hc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hg : ∀ k ≤ n, HeatWholeLine.HasExpGrowthOnStrip (fun s y => iteratedDeriv k (f s) y) T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (iteratedDeriv n (heatDuhamel ν f t))
      (deriv (heatDuhamel ν (fun s y => iteratedDeriv n (f s) y) t) x) x := by
  have he := funext (heatDuhamel_iteratedDeriv hν.le hf hc hg ht)
  rw [he]
  exact (heatDuhamel_hasDerivAt_space_of_continuous (f := fun s y => iteratedDeriv n (f s) y)
    hν (hc n le_rfl) (hg n le_rfl) ht x).differentiableAt.hasDerivAt

/-- The additional spatial derivative gained from continuous forcing is jointly
continuous even at the initial endpoint. -/
theorem heatDuhamel_iteratedDeriv_succ_continuousOn {f : ℝ → ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ n (f s))
    (hc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hg : ∀ k ≤ n, HeatWholeLine.HasExpGrowthOnStrip (fun s y => iteratedDeriv k (f s) y) T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv (n + 1) (heatDuhamel ν f p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  apply (heatDuhamel_deriv_continuousOn_of_continuous
    (f := fun s y => iteratedDeriv n (f s) y) hν hT (hc n le_rfl) (hg n le_rfl)).congr
  intro p hp
  simpa only [iteratedDeriv_succ] using
    (heatDuhamel_hasDerivAt_iteratedDeriv hν hf hc hg hp.1 p.2).deriv

/-- The additional spatial derivative has a uniform exponential growth bound,
without requiring the next spatial derivative of the forcing. -/
theorem heatDuhamel_iteratedDeriv_succ_hasExpGrowthOnStrip
    {f : ℝ → ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 < ν) (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ n (f s))
    (hc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hg : ∀ k ≤ n, HeatWholeLine.HasExpGrowthOnStrip (fun s y => iteratedDeriv k (f s) y) T) :
    HeatWholeLine.HasExpGrowthOnStrip
      (fun t x => iteratedDeriv (n + 1) (heatDuhamel ν f t) x) T := by
  obtain ⟨M, c, hM, hc', hb⟩ := heatDuhamel_deriv_hasExpGrowthOnStrip
    (f := fun s y => iteratedDeriv n (f s) y) hν (hc n le_rfl) (hg n le_rfl)
  refine ⟨M, c, hM, hc', fun t ht x => ?_⟩
  dsimp only
  rw [iteratedDeriv_succ,(heatDuhamel_hasDerivAt_iteratedDeriv hν hf hc hg ht x).deriv]
  exact hb t ht x

/-- After establishing the differentiated Duhamel identity, two more spatial
forcing derivatives justify its actual time derivative at interior times.
No forcing time derivative or prior mixed-derivative commutation is assumed. -/
theorem heatDuhamel_iteratedDeriv_hasDerivAt_time {f : ℝ → ℝ → ℝ} {ν T : ℝ} {n : ℕ}
    (hν : 0 < ν) (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ (n + 2) (f s))
    (hc : ∀ k ≤ n + 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hg : ∀ k ≤ n + 2, HeatWholeLine.HasExpGrowthOnStrip (fun s y => iteratedDeriv k (f s) y) T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => iteratedDeriv n (heatDuhamel ν f r) x)
      (iteratedDeriv n (f t) x +
        ν * heatDuhamel ν (fun s y => iteratedDeriv (n + 2) (f s) y) t x) t := by
  have hn : n ≤ n + 2 := by omega
  have hn1 : n + 1 ≤ n + 2 := by omega
  have hd (k : ℕ) (hk : k < n + 2) (s : ℝ) (hs : s ∈ Icc 0 T) (y : ℝ) :
      HasDerivAt (iteratedDeriv k (f s)) (iteratedDeriv (k + 1) (f s) y) y := by
    simpa only [iteratedDeriv_succ] using
      ((contDiff_nat_iff_iteratedDeriv.mp (hf s hs)).2 k hk y).hasDerivAt
  have h := heatDuhamel_hasDerivAt_time (f := fun s y => iteratedDeriv n (f s) y)
    (fx := fun s y => iteratedDeriv (n + 1) (f s) y)
    (fxx := fun s y => iteratedDeriv (n + 2) (f s) y)
    hν (hc n hn) (hc (n + 1) hn1) (hc (n + 2) le_rfl)
    (hg n hn) (hg (n + 1) hn1) (hg (n + 2) le_rfl)
    (hd n (by omega)) (hd (n + 1) (by omega)) ht x
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact heatDuhamel_iteratedDeriv hν.le
    (fun s hs => (hf s hs).of_le (by exact_mod_cast hn))
    (fun k hk => hc k (hk.trans hn)) (fun k hk => hg k (hk.trans hn)) ⟨hr.1.le, hr.2.le⟩ x

end MathlibExt.Analysis.PDE.HeatKernel
