/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Replicator dynamics

A population plays strategies `i : ι` (a finite type) with frequencies `x i`. The fitness of
strategy `i` in state `x` is `f x i`, and the mean fitness is `f̄(x) = ∑ i, x i * f x i`. The
replicator equation (Taylor and Jonker 1978) is

  `x_i' = x_i (f_i(x) - f̄(x))`.

`IsSolution f x` states that `x : ℝ → ι → ℝ` solves it for all `t ≥ 0`.

## Main results

* `IsSolution.hasDerivAt_sum`: `(∑ x_i)' = f̄(x) (1 - ∑ x_i)`.
* `IsSolution.sum_eq_one`: for continuous fitness, the hyperplane `∑ x_i = 1` is invariant: a
  solution starting there stays there for all `t ≥ 0`.
* `IsSolution.eq_zero_of_eq_zero`, `IsSolution.pos_of_pos`: for continuous fitness, absent
  strategies stay absent and present ones stay present, so every face of the simplex and its
  relative interior are invariant.
* `IsSolution.mem_simplex`: for continuous fitness, the standard simplex is invariant.
* `isRestPoint_iff`: an interior state (all `x i > 0`) is a rest point iff it is an equalizer,
  i.e. all strategies have the same fitness (equal to `f̄(x)`).

## References

* P. D. Taylor and L. B. Jonker, *Evolutionarily stable strategies and game dynamics*,
  Math. Biosci. 40 (1978) 145–156.
* J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge
  University Press (1998), §7.1–7.2.
-/

@[expose] public section

open Set Finset

namespace MathlibExt.Biology.Dynamics.Replicator

variable {ι : Type*} [Fintype ι]

/-- The mean fitness `f̄(x) = ∑ i, x i * f x i` of the population state `x` for the fitness
function `f`. -/
def meanFitness (f : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * f x i

/-- `x` solves the replicator equation `x_i' = x_i (f_i(x) - f̄(x))` for all times `t ≥ 0`. -/
structure IsSolution (f : (ι → ℝ) → ι → ℝ) (x : ℝ → ι → ℝ) : Prop where
  /-- Each frequency grows at the rate of its excess fitness. -/
  hasDerivAt : ∀ i t, 0 ≤ t →
    HasDerivAt (fun s => x s i) (x t i * (f (x t) i - meanFitness f (x t))) t

/-- `x` is a rest point of the replicator equation: `x_i (f_i(x) - f̄(x)) = 0` for all `i`. -/
def IsRestPoint (f : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : Prop :=
  ∀ i, x i * (f x i - meanFitness f x) = 0

/-- **Rest points in the interior are equalizers.** If every strategy is present (`x i > 0`),
then `x` is a rest point iff every strategy has fitness equal to the mean fitness. -/
theorem isRestPoint_iff {f : (ι → ℝ) → ι → ℝ} {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    IsRestPoint f x ↔ ∀ i, f x i = meanFitness f x := by
  refine forall_congr' fun i => ?_
  rw [mul_eq_zero, sub_eq_zero, or_iff_right (hx i).ne']

namespace IsSolution

variable {f : (ι → ℝ) → ι → ℝ} {x : ℝ → ι → ℝ}

/-- The total frequency `∑ x_i` evolves by `(∑ x_i)' = f̄(x) (1 - ∑ x_i)`. -/
theorem hasDerivAt_sum (h : IsSolution f x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => ∑ i, x s i) (meanFitness f (x t) * (1 - ∑ i, x t i)) t := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h.hasDerivAt i t ht
  convert hs using 1
  simp only [mul_sub, Finset.sum_sub_distrib, meanFitness, ← Finset.sum_mul]
  ring

/-- A solution is continuous on `[0, ∞)`. -/
private theorem continuousAt (h : IsSolution f x) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt x t :=
  continuousAt_pi.2 fun i => (h.hasDerivAt i t ht).continuousAt

/-- Grönwall step: on `[0, T]`, a function `u` with `u' = c(t) u`, `c` continuous along the
solution and `u 0 = 0`, vanishes. -/
private theorem eq_zero_of_hasDerivAt_mul (h : IsSolution f x)
    {u : ℝ → ℝ} {c : (ι → ℝ) → ℝ} (hc : Continuous c)
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (c (x t) * u t) t) (hu0 : u 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) : u T = 0 := by
  have hcont : ContinuousOn (fun t => c (x t)) (Icc 0 T) := fun t ht =>
    (hc.continuousAt.comp (h.continuousAt ht.1)).continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn hcont.norm).bddAbove
  refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K) (f' := fun t =>
    c (x t) * u t) (fun t ht => (hu t ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (hu t ht.1).hasDerivWithinAt) hu0 (fun t ht => ?_) T ⟨hT, le_rfl⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hK ⟨t, Ico_subset_Icc_self ht, rfl⟩) (norm_nonneg _)

/-- Backward uniqueness: on `[0, T]`, a function `u` with `u' = c(t) u` and `u T = 0` has
`u 0 = 0` (Grönwall applied to `s ↦ u (T - s)`). -/
private theorem eq_zero_left_of_hasDerivAt_mul (h : IsSolution f x)
    {u : ℝ → ℝ} {c : (ι → ℝ) → ℝ} (hc : Continuous c)
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (c (x t) * u t) t) {T : ℝ} (hT : 0 ≤ T) (huT : u T = 0) :
    u 0 = 0 := by
  have hcont : ContinuousOn (fun t => c (x t)) (Icc 0 T) := fun t ht =>
    (hc.continuousAt.comp (h.continuousAt ht.1)).continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn hcont.norm).bddAbove
  have hmem : ∀ s ∈ Icc 0 T, T - s ∈ Icc 0 T := fun s hs =>
    ⟨sub_nonneg.2 hs.2, by linarith [hs.1]⟩
  have hv : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => u (T - s)) (-(c (x (T - s)) * u (T - s))) s :=
    fun s hs => ((hu (T - s) (hmem s hs).1).comp s
      ((hasDerivAt_id' s).const_sub T)).congr_deriv (by ring)
  have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K)
    (f := fun s => u (T - s)) (f' := fun s => -(c (x (T - s)) * u (T - s)))
    (fun s hs => (hv s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hv s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (by simpa using huT)
    (fun s hs => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hK ⟨T - s, hmem s (Ico_subset_Icc_self hs), rfl⟩) (norm_nonneg _)) T ⟨hT, le_rfl⟩
  simpa using this

/-- **Invariance of the simplex hyperplane.** For continuous fitness `f`, a solution with
`∑ x_i(0) = 1` satisfies `∑ x_i(t) = 1` for all `t ≥ 0`. -/
theorem sum_eq_one (h : IsSolution f x) (hf : Continuous f) (h0 : ∑ i, x 0 i = 1) {t : ℝ}
    (ht : 0 ≤ t) : ∑ i, x t i = 1 := by
  have hc : Continuous fun y : ι → ℝ => -meanFitness f y := by
    unfold meanFitness
    fun_prop
  have := h.eq_zero_of_hasDerivAt_mul hc (u := fun s => ∑ i, x s i - 1)
    (fun s hs => by
      convert (h.hasDerivAt_sum hs).sub_const 1 using 1
      ring) (by simp [h0]) ht
  linarith

/-- **Invariance of the faces of the simplex.** For continuous fitness `f`, a strategy absent
at time `0` (`x_i(0) = 0`) stays absent for all `t ≥ 0`. -/
theorem eq_zero_of_eq_zero (h : IsSolution f x) (hf : Continuous f) {i : ι} (h0 : x 0 i = 0)
    {t : ℝ} (ht : 0 ≤ t) : x t i = 0 := by
  have hc : Continuous fun y : ι → ℝ => f y i - meanFitness f y := by
    unfold meanFitness
    fun_prop
  exact h.eq_zero_of_hasDerivAt_mul hc (u := fun s => x s i)
    (fun s hs => by simpa only [mul_comm] using h.hasDerivAt i s hs) h0 ht

/-- **Present strategies stay present.** For continuous fitness `f`, a strategy with positive
frequency at time `0` has positive frequency for all `t ≥ 0`. -/
theorem pos_of_pos (h : IsSolution f x) (hf : Continuous f) {i : ι} (h0 : 0 < x 0 i)
    {t : ℝ} (ht : 0 ≤ t) : 0 < x t i := by
  have hc : Continuous fun y : ι → ℝ => f y i - meanFitness f y := by
    unfold meanFitness
    fun_prop
  have hu : ∀ s, 0 ≤ s → HasDerivAt (fun s => x s i)
      ((fun y : ι → ℝ => f y i - meanFitness f y) (x s) * x s i) s := fun s hs => by
    simpa only [mul_comm] using h.hasDerivAt i s hs
  by_contra hneg
  obtain ⟨s, hs, hs0⟩ : ∃ s ∈ Icc 0 t, x s i = 0 :=
    intermediate_value_Icc' ht (fun s hs => (hu s hs.1).continuousAt.continuousWithinAt)
      ⟨not_lt.1 hneg, h0.le⟩
  have := h.eq_zero_left_of_hasDerivAt_mul hc hu hs.1 hs0
  exact h0.ne' this

/-- **Invariance of the simplex (Hofbauer–Sigmund 1998, §7.1).** For continuous fitness `f`, a
solution starting in the standard simplex (`x i ≥ 0` for all `i` and `∑ i, x i = 1`) stays in
it for all `t ≥ 0`. -/
theorem mem_simplex (h : IsSolution f x) (hf : Continuous f) (h0 : ∀ i, 0 ≤ x 0 i)
    (h1 : ∑ i, x 0 i = 1) {t : ℝ} (ht : 0 ≤ t) : (∀ i, 0 ≤ x t i) ∧ ∑ i, x t i = 1 := by
  refine ⟨fun i => ?_, h.sum_eq_one hf h1 ht⟩
  rcases (h0 i).eq_or_lt with h0i | h0i
  · exact (h.eq_zero_of_eq_zero hf h0i.symm ht).ge
  · exact (h.pos_of_pos hf h0i ht).le

end IsSolution

end MathlibExt.Biology.Dynamics.Replicator
