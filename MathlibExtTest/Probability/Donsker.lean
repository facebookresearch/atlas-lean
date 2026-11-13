/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Donsker
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Moments.Variance
import MathlibExt.Probability.Martingale.McLeishCLT

@[expose] public section

open scoped BigOperators

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.DonskerWanted
open MathlibExt.Probability.Martingale
open scoped NNReal

namespace MathlibExtTest.Probability.Donsker

-- At the right endpoint, polygonal interpolation is the normalized full partial sum.
example {Ω : Type*} (n : ℕ) (hn : n ≠ 0) (X : ℕ → Ω → ℝ) (ω : Ω) :
    donskerProcess n X ω ⟨1, zero_le_one, le_rfl⟩ =
      (∑ i ∈ Finset.range n, X i ω) / Real.sqrt (n : ℝ) := by
  simpa using
    donskerProcess_apply_eq (n := n) (X := X) (ω := ω)
      (t := ⟨1, zero_le_one, le_rfl⟩) hn

-- Equal finite-dimensional laws of two Dirac measures determine the paths themselves.
example (f g : C(Set.Icc (0 : ℝ) 1, ℝ))
    (h : ∀ I : Finset (Set.Icc (0 : ℝ) 1),
      (Measure.dirac f).map (fun u => I.restrict (fun t => u t)) =
        (Measure.dirac g).map (fun u => I.restrict (fun t => u t))) :
    f = g := by
  apply MeasureTheory.injective_dirac
  exact continuousMap_measure_ext_of_finset_eval (Measure.dirac f) (Measure.dirac g) h

-- Etemadi and Chebyshev bound the running maximum by the partial-sum variances.
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X P)
    (n : ℕ) (a : ℝ) (ha : 0 < a)
    (hLp : ∀ k, MemLp (fun ω => ∑ i ∈ Finset.range k, X i ω) 2 P)
    (hmean : ∀ k, ∫ ω, ∑ i ∈ Finset.range k, X i ω ∂P = 0) :
    P {ω | ∃ k ∈ Finset.range (n + 1),
        3 * a ≤ |∑ i ∈ Finset.range k, X i ω|} ≤
      3 * (⨆ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (Var[fun ω => ∑ i ∈ Finset.range k, X i ω; P] / a ^ 2)) := by
  calc
    P {ω | ∃ k ∈ Finset.range (n + 1),
        3 * a ≤ |∑ i ∈ Finset.range k, X i ω|} ≤
        3 * (⨆ k ∈ Finset.range (n + 1),
          P {ω | a ≤ |∑ i ∈ Finset.range k, X i ω|}) :=
      etemadi_maximal_inequality X hX hIndep n a
    _ ≤ 3 * (⨆ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (Var[fun ω => ∑ i ∈ Finset.range k, X i ω; P] / a ^ 2)) := by
      gcongr with k hk
      simpa [hmean k] using meas_ge_le_variance_div_sq (hLp k) ha

-- Boundary computed from the definition of the variance formula, not via the adapter: for one
-- time `t` and coefficient `1` the double sum is `t`, the variance of `B t`.
example (t : Set.Icc (0 : ℝ) 1) :
    (∑ s : ({t} : Finset (Set.Icc (0 : ℝ) 1)), ∑ u : ({t} : Finset (Set.Icc (0 : ℝ) 1)),
      (fun _ => (1 : ℝ)) s * (fun _ => (1 : ℝ)) u * (min (s : Set.Icc (0 : ℝ) 1) u).1) = t.1 := by
  simp

-- Same, at the left endpoint: the variance is `0`, so the predicted law is the Dirac mass.
example (c : ({⟨0, le_rfl, zero_le_one⟩} : Finset (Set.Icc (0 : ℝ) 1)) → ℝ) :
    gaussianReal 0 (∑ s : ({⟨0, le_rfl, zero_le_one⟩} : Finset (Set.Icc (0 : ℝ) 1)),
      ∑ u : ({⟨0, le_rfl, zero_le_one⟩} : Finset (Set.Icc (0 : ℝ) 1)),
        c s * c u * (min (s : Set.Icc (0 : ℝ) 1) u).1).toNNReal = Measure.dirac 0 := by
  simp

-- Cross-check against an independent route: the adapter's one-point law of `Zc · t` agrees with
-- Mathlib's `IsPreBrownianReal.hasLaw_eval` transported along the a.e. equality `Zc = B`.
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') (t : Set.Icc (0 : ℝ) 1) :
    ∃ Zc : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ), Measurable Zc ∧
      P'.map (fun ω => Zc ω t) = gaussianReal 0 (iccToNNReal t) ∧
      P'.map (fun ω => ∑ s : ({t} : Finset (Set.Icc (0 : ℝ) 1)), (1 : ℝ) * Zc ω s) =
        gaussianReal 0 (iccToNNReal t) := by
  obtain ⟨Zc, hm, hae, hZ⟩ := exists_measurable_brownianPath_gaussian B hB
  refine ⟨Zc, hm, ?_, ?_⟩
  · rw [Measure.map_congr (g := B (iccToNNReal t)) (by filter_upwards [hae] with ω hω using hω t)]
    exact (hB.hasLaw_eval (iccToNNReal t)).map_eq
  · rw [hZ {t} (fun _ => 1)]
    congr 1
    ext
    simp [iccToNNReal, t.2.1]
    rfl

-- Two-point cross-check covering the off-diagonal covariance: with `I = {s, u}` and
-- `c = (1, -1)` the adapter's predicted variance `s + u - 2 * min s u` is `|s - u|`, the law of
-- `B s - B u` given independently by Mathlib's `IsPreBrownianReal.hasLaw_sub`. Replacing `min` by
-- `max` would give `-|s - u|`, so this distinguishes the Brownian covariance.
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') (s u : Set.Icc (0 : ℝ) 1) (hsu : s ≠ u) :
    ∃ Zc : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ), Measurable Zc ∧
      P'.map (fun ω => Zc ω s - Zc ω u) = gaussianReal 0 (nndist s.1 u.1) ∧
      P'.map (fun ω => ∑ x : ({s, u} : Finset (Set.Icc (0 : ℝ) 1)),
        (if (x : Set.Icc (0 : ℝ) 1) = s then (1 : ℝ) else -1) * Zc ω x) =
          gaussianReal 0 (nndist s.1 u.1) := by
  obtain ⟨Zc, hm, hae, hZ⟩ := exists_measurable_brownianPath_gaussian B hB
  refine ⟨Zc, hm, ?_, ?_⟩
  · rw [Measure.map_congr (g := B (iccToNNReal s) - B (iccToNNReal u))
      (by filter_upwards [hae] with ω hω using by simp [hω s, hω u])]
    exact (hB.hasLaw_sub (iccToNNReal s) (iccToNNReal u)).map_eq
  · have key : ∀ x : Set.Icc (0 : ℝ) 1,
        (∑ y : ({s, u} : Finset (Set.Icc (0 : ℝ) 1)), (if x = s then (1 : ℝ) else -1) *
          (if (y : Set.Icc (0 : ℝ) 1) = s then (1 : ℝ) else -1) * (min x y).1) =
        ∑ y ∈ ({s, u} : Finset (Set.Icc (0 : ℝ) 1)), (if x = s then (1 : ℝ) else -1) *
          (if y = s then (1 : ℝ) else -1) * (min x y).1 := fun x =>
      Finset.sum_coe_sort _ (fun y => (if x = s then (1 : ℝ) else -1) *
          (if y = s then (1 : ℝ) else -1) * (min x y).1)
    have hv : (∑ x : ({s, u} : Finset (Set.Icc (0 : ℝ) 1)),
        ∑ y : ({s, u} : Finset (Set.Icc (0 : ℝ) 1)),
          (if (x : Set.Icc (0 : ℝ) 1) = s then (1 : ℝ) else -1) *
            (if (y : Set.Icc (0 : ℝ) 1) = s then (1 : ℝ) else -1) *
              (min (x : Set.Icc (0 : ℝ) 1) y).1) = |s.1 - u.1| := by
      rw [Finset.sum_coe_sort ({s, u} : Finset (Set.Icc (0 : ℝ) 1))
        (fun x => ∑ y : ({s, u} : Finset (Set.Icc (0 : ℝ) 1)),
          (if x = s then (1 : ℝ) else -1) *
            (if (y : Set.Icc (0 : ℝ) 1) = s then (1 : ℝ) else -1) * (min x y).1)]
      simp only [key]
      rw [Finset.sum_pair hsu, Finset.sum_pair hsu, Finset.sum_pair hsu]
      simp only [↓reduceIte, hsu.symm, min_self]
      rcases le_total s u with h | h
      · rw [min_eq_left h, min_eq_right h,
          abs_of_nonpos (sub_nonpos.2 (Subtype.coe_le_coe.2 h))]
        ring
      · rw [min_eq_right h, min_eq_left h,
          abs_of_nonneg (sub_nonneg.2 (Subtype.coe_le_coe.2 h))]
        ring
    rw [hZ {s, u} (fun x => if (x : Set.Icc (0 : ℝ) 1) = s then 1 else -1), hv]
    congr 1
    ext
    simp [Real.dist_eq]

-- The adapter output is pinned at `0` at the left endpoint, as Brownian motion is.
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    ∃ Zc : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ), Measurable Zc ∧
      ∀ᵐ ω ∂P', Zc ω ⟨0, le_rfl, zero_le_one⟩ = 0 := by
  obtain ⟨Zc, hm, hae, -⟩ := exists_measurable_brownianPath_gaussian B hB
  refine ⟨Zc, hm, ?_⟩
  filter_upwards [hae, hB.eval_zero_ae_eq_zero] with ω h1 h2
  rw [h1]
  exact h2

-- Downstream use: the adapter discharges the `hZm` and `hZ` inputs of McLeish's
-- finite-dimensional CLT, so its conclusion (the `hT81` input of the martingale functional CLT)
-- holds with a Brownian limit.
example {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {𝓕 : ℕ → Filtration ℕ m0} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hLind : LindebergConditionTriangular ξ μ)
    (hRQV : ∀ t : Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n j ω ^ 2) Filter.atTop
        (fun _ => t.1))
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') :
    ∃ Zc : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ),
      (∀ᵐ ω ∂P', ∀ t : Set.Icc (0 : ℝ) 1, Zc ω t = B (iccToNNReal t) ω) ∧
      ∀ I : Finset (Set.Icc (0 : ℝ) 1), TendstoInDistribution
        (fun (n : ℕ) ω => I.restrict (fun t => ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n i ω))
        Filter.atTop (fun ω => I.restrict (fun t => Zc ω t)) (fun _ => μ) P' := by
  obtain ⟨Zc, hm, hae, hZ⟩ := exists_measurable_brownianPath_gaussian B hB
  exact ⟨Zc, hae, tendstoInDistribution_fdd_martingaleDifference_floor hξ hmds hL2 hLind hRQV
    Zc hm hZ⟩

end MathlibExtTest.Probability.Donsker
