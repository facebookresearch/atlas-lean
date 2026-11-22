/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.Rejection
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# The Metropolis–Hastings algorithm on a finite state space

A transition rule `P : α → PMF α` on a finite state space gives a Markov kernel `pmfKernel P`.

* `isReversible_pmfKernel`: pointwise detailed balance `π x P(x, y) = π y P(y, x)` makes the
  kernel reversible in Mathlib's sense (`ProbabilityTheory.Kernel.IsReversible`).
  `invariant_pmfKernel` then gets stationarity from Mathlib's `Kernel.IsReversible.invariant`.
  `bind_eq_of_detailedBalance` is the same fact for `PMF`s: `∑ₓ π x P(x, y) = π y`.
* `mhStep π Q x`: one **Metropolis–Hastings** step for the target `π` and proposal `Q`. Propose
  `y ~ Q x` and move with probability `mhAccept π Q x y = min(1, π y Q(y, x) / (π x Q(x, y)))`;
  otherwise stay at `x`.
* `mh_detailedBalance`: Metropolis–Hastings satisfies detailed balance, since both sides equal
  `min (π x Q(x, y)) (π y Q(y, x))`. No positivity or symmetry assumption on `π` or `Q` is needed.
* `isReversible_mhKernel`, `invariant_mhKernel`, `bind_mhStep` (**the target is stationary**).

## References

* C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer, 2004, §7.3.
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §11.2.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Detailed balance on a finite state space -/

/-- The Markov kernel of a transition rule `P : α → PMF α` on a finite state space. -/
noncomputable def pmfKernel (P : α → PMF α) : Kernel α α :=
  Kernel.ofFunOfCountable fun x ↦ (P x).toMeasure

instance (P : α → PMF α) : IsMarkovKernel (pmfKernel P) :=
  ⟨fun x ↦ by change IsProbabilityMeasure (P x).toMeasure; infer_instance⟩

theorem pmfKernel_apply (P : α → PMF α) (x : α) : pmfKernel P x = (P x).toMeasure := rfl

theorem lintegral_pmfKernel (π : PMF α) (P : α → PMF α) (A B : Set α) :
    ∫⁻ x in A, pmfKernel P x B ∂π.toMeasure = ∑ x, ∑ y, A.indicator π x * B.indicator (P x) y := by
  classical
  rw [← lintegral_indicator A.toFinite.measurableSet, lintegral_fintype]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)]
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, pmfKernel_apply,
      PMF.toMeasure_apply_fintype, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ ↦ mul_comm _ _
  · simp [Set.indicator_of_notMem hx]

/-- **Detailed balance implies reversibility**: if `π x P(x, y) = π y P(y, x)` for all states, the
kernel of `P` is reversible with respect to `π` in Mathlib's sense. -/
theorem isReversible_pmfKernel {π : PMF α} {P : α → PMF α}
    (h : ∀ x y, π x * P x y = π y * P y x) : (pmfKernel P).IsReversible π.toMeasure := by
  intro A B _ _
  rw [lintegral_pmfKernel, lintegral_pmfKernel, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ B <;> simp [hx, hy, h x y]

/-- Under detailed balance, `π` is invariant for the kernel (Mathlib's
`Kernel.IsReversible.invariant`). -/
theorem invariant_pmfKernel {π : PMF α} {P : α → PMF α} (h : ∀ x y, π x * P x y = π y * P y x) :
    (pmfKernel P).Invariant π.toMeasure :=
  (isReversible_pmfKernel h).invariant

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Under detailed balance, one step from `π` stays at `π`: `∑ₓ π x P(x, y) = π y`. -/
theorem bind_eq_of_detailedBalance [Finite α] {π : PMF α} {P : α → PMF α}
    (h : ∀ x y, π x * P x y = π y * P y x) : π.bind P = π := by
  have := Fintype.ofFinite α
  ext y
  rw [PMF.bind_apply, tsum_fintype]
  simp_rw [h _ y]
  have h1 : ∑ x, P y x = 1 := by simpa [tsum_fintype] using (P y).tsum_coe
  rw [← Finset.mul_sum, h1, mul_one]

/-! ### The Metropolis–Hastings algorithm -/

/-- The Metropolis–Hastings acceptance probability `min(1, π y Q(y, x) / (π x Q(x, y)))` of a
move from `x` to `y` proposed by `Q`. -/
noncomputable def mhAccept (π : PMF α) (Q : α → PMF α) (x y : α) : ℝ≥0∞ :=
  min 1 (π y * Q y x / (π x * Q x y))

/-- One **Metropolis–Hastings** step from `x` for the target `π` and proposal `Q`: propose
`y ~ Q x`, move to `y` with probability `mhAccept π Q x y`, and otherwise stay at `x`. -/
noncomputable def mhStep (π : PMF α) (Q : α → PMF α) (x : α) : PMF α :=
  (Q x).bind fun y ↦ (coin (mhAccept π Q x y) (min_le_left _ _)).map fun b ↦ cond b y x

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem mhStep_apply_of_ne {π : PMF α} {Q : α → PMF α} {x y : α} (hxy : x ≠ y) :
    mhStep π Q x y = Q x y * mhAccept π Q x y := by
  classical
  rw [mhStep, PMF.bind_apply, tsum_eq_single y]
  · rw [PMF.map_apply, tsum_eq_single true]
    · simp [coin]
    · intro b hb
      cases b
      · simp [Ne.symm hxy]
      · exact absurd rfl hb
  · intro z hz
    rw [PMF.map_apply]
    simp only [mul_eq_zero]
    right
    refine ENNReal.tsum_eq_zero.mpr fun b ↦ ?_
    cases b
    · simp [Ne.symm hxy]
    · simp [Ne.symm hz]

theorem mul_min_one_div {a b : ℝ≥0∞} (ha : a ≠ ∞) : a * min 1 (b / a) = min a b := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [mul_min, mul_one, ENNReal.mul_div_cancel h0 ha]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Detailed balance for Metropolis–Hastings**: `π x P(x, y) = π y P(y, x)`. Both sides are
`min (π x Q(x, y)) (π y Q(y, x))`. -/
theorem mh_detailedBalance (π : PMF α) (Q : α → PMF α) (x y : α) :
    π x * mhStep π Q x y = π y * mhStep π Q y x := by
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  rw [mhStep_apply_of_ne hxy, mhStep_apply_of_ne hxy.symm, ← mul_assoc, ← mul_assoc, mhAccept,
    mhAccept, mul_min_one_div (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)),
    mul_min_one_div (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)), min_comm]

/-- The Metropolis–Hastings kernel is reversible with respect to the target. -/
theorem isReversible_mhKernel (π : PMF α) (Q : α → PMF α) :
    (pmfKernel (mhStep π Q)).IsReversible π.toMeasure :=
  isReversible_pmfKernel (mh_detailedBalance π Q)

/-- **The target is stationary for Metropolis–Hastings.** -/
theorem invariant_mhKernel (π : PMF α) (Q : α → PMF α) :
    (pmfKernel (mhStep π Q)).Invariant π.toMeasure :=
  invariant_pmfKernel (mh_detailedBalance π Q)

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem bind_mhStep [Finite α] (π : PMF α) (Q : α → PMF α) : π.bind (mhStep π Q) = π :=
  bind_eq_of_detailedBalance (mh_detailedBalance π Q)

end Cslib.MachineLearning.Sampling
