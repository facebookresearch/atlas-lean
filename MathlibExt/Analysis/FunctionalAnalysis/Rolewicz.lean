/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.Hypercyclicity
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rolewicz's theorem: multiples of the backward shift are hypercyclic

Let `B` be the backward shift on `ℓ²(ℕ, 𝕜)`, `(B x) n = x (n + 1)`.
*Rolewicz's theorem* (1969) says that the scalar multiple `μ • B` is
hypercyclic — it has an orbit that is dense in `ℓ²(ℕ, 𝕜)` — if and only
if `‖μ‖ > 1`. The forward direction is a boundedness argument: if
`‖μ‖ ≤ 1` then every orbit is contained in the closed ball of radius
`‖x‖` around `0`, so no orbit can be dense. The reverse direction is
the hypercyclicity criterion from `Hypercyclicity.lean`, applied with
`X₀ = Y₀` the span of the single-coordinate vectors (finitely
supported sequences) and `S n y = (μ ^ n)⁻¹ • Fⁿ y`, where `F` is the
forward shift: `Bⁿ` kills finitely supported vectors eventually,
`(‖μ‖⁻¹) ^ n → 0` since `‖μ‖ > 1`, and `Bⁿ Fⁿ = 1`.

Because second countability is not inferred for `ℓ²` in the pinned
Mathlib, the criterion is fed an explicit countable dense set: the
finite sequences whose coefficients lie in `ℚ + ℚ * I`, the image of
`ℚ × ℚ` under `(a, b) ↦ a + b * I`. Its density in `𝕜` is proved from
density of `ℚ` in `ℝ` together with the identity
`‖z‖ ^ 2 = re z * re z + im z * im z`; its density in `ℓ²` follows from
truncation of the canonical series `x = ∑ i, lp.single 2 i (x i)`.

This is a companion to the Baire-category, bounded-operator, and
Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/`. It is not one of the
72 v1 targets, and it is not in the pinned Mathlib or in base
MathlibExt, which have the Baire theorem and shift-free operator
theory but no hypercyclicity. Classical reference: S. Rolewicz,
"On orbits of elements", *Studia Math.* 32 (1969), 17–22; see also
F. Bayart and É. Matheron, *Dynamics of Linear Operators*, Cambridge
University Press, 2009, Example 1.8.

## Main declarations

* `forwardShiftCLM` / `backwardShiftCLM` : the forward and backward
  shifts as bounded operators on `ℓ²(ℕ, 𝕜)`, defined from scratch in
  this file's own namespace.
* `forwardShiftCLM_pow_apply` / `backwardShiftCLM_pow_apply` : the
  pointwise action of the powers of the shifts.
* `dense_range_ratApproxScalar` : `ℚ + ℚ * I` is dense in `𝕜`.
* `dense_range_ratApproxSeq` : finite `ℚ + ℚ * I`-coefficient sequences
  are dense in `ℓ²(ℕ, 𝕜)`.
* `isHypercyclic_smul_backwardShiftCLM_iff` : Rolewicz's theorem.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.Rolewicz

open Filter Topology Set Metric
open MathlibExt.Analysis.FunctionalAnalysis.Hypercyclicity
open scoped _root_.lp ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The forward and backward shifts on `ℓ²(ℕ, 𝕜)` -/

/-- The forward-shift function on sequences: insert `0` at `0` and shift up by one. -/
def forwardShiftFun (x : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => x n

/-- The backward-shift function on sequences: drop coordinate `0` and shift down by one. -/
def backwardShiftFun (x : ℕ → 𝕜) (i : ℕ) : 𝕜 := x (i + 1)

@[simp] theorem forwardShiftFun_zero (x : ℕ → 𝕜) : forwardShiftFun x 0 = 0 := rfl

@[simp] theorem forwardShiftFun_succ (x : ℕ → 𝕜) (n : ℕ) :
    forwardShiftFun x (n + 1) = x n := rfl

omit [RCLike 𝕜] in
@[simp] theorem backwardShiftFun_apply (x : ℕ → 𝕜) (i : ℕ) :
    backwardShiftFun x i = x (i + 1) :=
  rfl

/-- The shifted sequence of an `ℓ²` sequence is in `ℓ²`. -/
theorem memℓp_forwardShiftFun {x : ℓ²(ℕ, 𝕜)} : Memℓp (forwardShiftFun (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖forwardShiftFun (x : ℕ → 𝕜) (n + 1)‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [forwardShiftFun_succ] using h
  exact (summable_nat_add_iff 1).mp h'

/-- The backward-shifted sequence of an `ℓ²` sequence is in `ℓ²`. -/
theorem memℓp_backwardShiftFun {x : ℓ²(ℕ, 𝕜)} : Memℓp (backwardShiftFun (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖backwardShiftFun (x : ℕ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [backwardShiftFun_apply] using (summable_nat_add_iff 1).mpr h
  exact h'

/-- The forward shift as a linear map. -/
noncomputable def forwardShiftLinMap : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨forwardShiftFun (x : ℕ → 𝕜), memℓp_forwardShiftFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_add, forwardShiftFun_zero, Pi.add_apply, add_zero]
    | succ n => simp only [lp.coeFn_add, forwardShiftFun_succ, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_smul, forwardShiftFun_zero, Pi.smul_apply, smul_zero]
    | succ n =>
        simp only [lp.coeFn_smul, forwardShiftFun_succ, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]

/-- The backward shift as a linear map. -/
noncomputable def backwardShiftLinMap : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨backwardShiftFun (x : ℕ → 𝕜), memℓp_backwardShiftFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, backwardShiftFun_apply, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, backwardShiftFun_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

/-- Pointwise action of the forward-shift linear map. -/
theorem forwardShiftLinMap_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    forwardShiftLinMap x i = forwardShiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- Pointwise action of the backward-shift linear map. -/
theorem backwardShiftLinMap_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    backwardShiftLinMap x i = backwardShiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- The squared norms of a shifted sequence sum to the squared norms of
the original sequence. -/
theorem tsum_forwardShiftFun_norm (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖forwardShiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal =
      ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖forwardShiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    memℓp_forwardShiftFun.summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [forwardShiftFun_zero, forwardShiftFun_succ, norm_zero,
    Real.zero_rpow (by simp : (2 : ℝ≥0∞).toReal ≠ 0), zero_add]

/-- The squared norms of a backward-shifted sequence sum to at most the
squared norms of the original sequence: they are a tail sum. -/
theorem tsum_backwardShiftFun_norm_le (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖backwardShiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal ≤
      ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [backwardShiftFun_apply]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)

/-- The forward shift preserves norms. -/
theorem norm_forwardShiftLinMap_apply (x : ℓ²(ℕ, 𝕜)) : ‖forwardShiftLinMap x‖ = ‖x‖ := by
  have hpow : ‖forwardShiftLinMap x‖ ^ (2 : ℝ≥0∞).toReal = ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (forwardShiftLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_forwardShiftFun_norm x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

/-- The backward shift does not increase norms. -/
theorem norm_backwardShiftLinMap_apply_le (x : ℓ²(ℕ, 𝕜)) : ‖backwardShiftLinMap x‖ ≤ ‖x‖ := by
  have hpow : ‖backwardShiftLinMap x‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (backwardShiftLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_backwardShiftFun_norm_le x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact le_of_sq_le_sq hpow (norm_nonneg _)

/-- The forward shift as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def forwardShiftCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  forwardShiftLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact le_of_eq (norm_forwardShiftLinMap_apply x))

/-- The backward shift as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def backwardShiftCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  backwardShiftLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_backwardShiftLinMap_apply_le x)

/-- Pointwise action of the forward shift. -/
theorem forwardShiftCLM_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    forwardShiftCLM x i = forwardShiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- Pointwise action of the backward shift. -/
theorem backwardShiftCLM_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    backwardShiftCLM x i = backwardShiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- The forward shift is an isometry: `‖F x‖ = ‖x‖`. -/
theorem norm_forwardShiftCLM_apply (x : ℓ²(ℕ, 𝕜)) : ‖forwardShiftCLM x‖ = ‖x‖ :=
  norm_forwardShiftLinMap_apply x

/-- The backward shift does not increase norms. -/
theorem norm_backwardShiftCLM_apply_le (x : ℓ²(ℕ, 𝕜)) : ‖backwardShiftCLM x‖ ≤ ‖x‖ :=
  norm_backwardShiftLinMap_apply_le x

/-! ### Powers of the shifts -/

/-- Pointwise action of the `n`-th power of the backward shift:
`(Bⁿ x) i = x (i + n)`. -/
theorem backwardShiftCLM_pow_apply : ∀ (n : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ),
    ((backwardShiftCLM ^ n) x) i = x (i + n) := by
  intro n
  induction n with
  | zero => intro x i; simp
  | succ n ih =>
    intro x i
    rw [pow_succ, mul_apply_eq_comp, ih, backwardShiftCLM_apply, backwardShiftFun_apply]
    congr 1

/-- Pointwise action of the `n`-th power of the forward shift:
`(Fⁿ x) i = 0` for `i < n` and `x (i - n)` otherwise. -/
theorem forwardShiftCLM_pow_apply : ∀ (n : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ),
    ((forwardShiftCLM ^ n) x) i = if i < n then 0 else x (i - n) := by
  intro n
  induction n with
  | zero => intro x i; simp
  | succ n ih =>
    intro x i
    rw [pow_succ, mul_apply_eq_comp, ih]
    by_cases hi : i < n
    · rw [ite_eq_left hi, ite_eq_left (hi.trans (Nat.lt_succ_self n))]
    · rw [ite_eq_right hi]
      rcases Nat.eq_zero_or_pos (i - n) with h0 | hpos
      · have hi' : i = n := by omega
        rw [hi', Nat.sub_self, forwardShiftCLM_apply, forwardShiftFun_zero,
          ite_eq_left (Nat.lt_succ_self n)]
      · obtain ⟨m, hm⟩ : ∃ m, i - n = m + 1 := ⟨i - n - 1, by omega⟩
        rw [hm, forwardShiftCLM_apply, forwardShiftFun_succ,
          ite_eq_right (by omega : ¬ i < n + 1)]
        have hsub : i - (n + 1) = m := by omega
        rw [hsub]

/-- `Bⁿ Fⁿ = 1`: the powers of the backward shift undo the powers of
the forward shift. -/
theorem backwardShiftCLM_pow_forwardShiftCLM_pow_apply (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    (backwardShiftCLM ^ n) ((forwardShiftCLM ^ n) x) = x := by
  apply lp.ext
  funext i
  rw [backwardShiftCLM_pow_apply, forwardShiftCLM_pow_apply,
    ite_eq_right (by omega : ¬ i + n < n)]
  have hsub : i + n - n = i := by omega
  rw [hsub]

/-- Powers of the forward shift preserve norms. -/
theorem norm_forwardShiftCLM_pow_apply (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ‖(forwardShiftCLM ^ n) x‖ = ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, norm_forwardShiftCLM_apply]

/-- Powers of the backward shift do not increase norms. -/
theorem norm_backwardShiftCLM_pow_apply_le (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ‖(backwardShiftCLM ^ n) x‖ ≤ ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp]
    exact le_trans (ih (backwardShiftCLM x)) (norm_backwardShiftCLM_apply_le x)

/-- Powers of a scalar multiple of the backward shift, applied pointwise. -/
theorem smul_backwardShiftCLM_pow_apply (μ : 𝕜) (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    (((μ • backwardShiftCLM) ^ n) x) = μ ^ n • (backwardShiftCLM ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    calc (((μ • backwardShiftCLM) ^ (n + 1)) x)
        = ((μ • backwardShiftCLM) ^ n) ((μ • backwardShiftCLM) x) := by
          rw [pow_succ, mul_apply_eq_comp]
      _ = μ ^ n • (backwardShiftCLM ^ n) ((μ • backwardShiftCLM) x) := by rw [ih]
      _ = μ ^ n • (backwardShiftCLM ^ n) (μ • backwardShiftCLM x) := by rfl
      _ = μ ^ n • (μ • (backwardShiftCLM ^ n) (backwardShiftCLM x)) := by rw [map_smul]
      _ = (μ ^ n * μ) • (backwardShiftCLM ^ n) (backwardShiftCLM x) := by rw [smul_smul]
      _ = μ ^ (n + 1) • (backwardShiftCLM ^ (n + 1)) x := by
          have h1 : μ ^ (n + 1) = μ ^ n * μ := pow_succ _ _
          have h2 : (backwardShiftCLM ^ (n + 1)) x =
              (backwardShiftCLM ^ n) (backwardShiftCLM x) := by
            rw [pow_succ, mul_apply_eq_comp]
          rw [h1, h2]

/-! ### A countable dense set in `ℓ²(ℕ, 𝕜)` -/

/-- The rational approximants in `𝕜`: `a + b * I` with `a b : ℚ`. -/
def ratApproxScalar (q : ℚ × ℚ) : 𝕜 := (q.1 : ℝ) + (q.2 : ℝ) * RCLike.I

/-- `|im I| ≤ 1`: indeed `im I` is `0` or `1`, since
`im I * im I = im I`. -/
theorem abs_im_I_le_one : |RCLike.im (RCLike.I : 𝕜)| ≤ 1 := by
  have h : RCLike.im (RCLike.I : 𝕜) * RCLike.im (RCLike.I : 𝕜) = RCLike.im (RCLike.I : 𝕜) :=
    RCLike.I_im (RCLike.I : 𝕜)
  have h2 : RCLike.im (RCLike.I : 𝕜) * (RCLike.im (RCLike.I : 𝕜) - 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h0 | h1
  · simp [h0]
  · have hI : RCLike.im (RCLike.I : 𝕜) = 1 := sub_eq_zero.mp h1
    simp [hI]

/-- `ℚ + ℚ * I` is dense in `𝕜`. -/
theorem dense_range_ratApproxScalar : Dense (Set.range (ratApproxScalar (𝕜 := 𝕜))) := by
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨z, hzU⟩ := hUne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen z hzU
  have hQ : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  obtain ⟨q1', hq1ball, ⟨q1, hq1eq⟩⟩ :=
    hQ.inter_open_nonempty _ Metric.isOpen_ball
      ⟨RCLike.re z, Metric.mem_ball_self (half_pos hε)⟩
  obtain ⟨q2', hq2ball, ⟨q2, hq2eq⟩⟩ :=
    hQ.inter_open_nonempty _ Metric.isOpen_ball
      ⟨RCLike.im z, Metric.mem_ball_self (half_pos hε)⟩
  have hq1 : |(q1 : ℝ) - RCLike.re z| < ε / 2 := by
    have h := Metric.mem_ball.mp hq1ball
    rw [← hq1eq, Real.dist_eq] at h
    exact h
  have hq2 : |(q2 : ℝ) - RCLike.im z| < ε / 2 := by
    have h := Metric.mem_ball.mp hq2ball
    rw [← hq2eq, Real.dist_eq] at h
    exact h
  refine ⟨ratApproxScalar (q1, q2), ?_, ⟨⟨q1, q2⟩, rfl⟩⟩
  apply hball
  rw [Metric.mem_ball]
  -- The difference `ratApproxScalar (q1, q2) - z` has small real and imaginary parts.
  set w := ratApproxScalar (q1, q2) - z with hw
  have hreS : RCLike.re ((ratApproxScalar (𝕜 := 𝕜)) (q1, q2)) = (q1 : ℝ) := by
    simp [ratApproxScalar]
  have himS : RCLike.im ((ratApproxScalar (𝕜 := 𝕜)) (q1, q2)) =
      (q2 : ℝ) * RCLike.im (RCLike.I : 𝕜) := by
    simp [ratApproxScalar]
  have hrew : RCLike.re w = (q1 : ℝ) - RCLike.re z := by
    rw [hw, map_sub, hreS]
  have himw : RCLike.im w = ((q2 : ℝ) - RCLike.im z) * RCLike.im (RCLike.I : 𝕜) := by
    have h2 : RCLike.im w = RCLike.im (ratApproxScalar (q1, q2)) - RCLike.im z :=
      map_sub _ _ _
    rw [h2, himS]
    linear_combination RCLike.I_im z
  have hre : |RCLike.re w| < ε / 2 := by rw [hrew]; exact hq1
  have him : |RCLike.im w| < ε / 2 := by
    rw [himw, abs_mul]
    calc |(q2 : ℝ) - RCLike.im z| * |RCLike.im (RCLike.I : 𝕜)|
        ≤ |(q2 : ℝ) - RCLike.im z| * 1 :=
          mul_le_mul_of_nonneg_left abs_im_I_le_one (abs_nonneg _)
      _ = |(q2 : ℝ) - RCLike.im z| := mul_one _
      _ < ε / 2 := hq2
  have hre2 : RCLike.re w * RCLike.re w < (ε / 2) * (ε / 2) := by
    have h := abs_lt.mp hre
    nlinarith [mul_pos (sub_pos.mpr h.2)
      (show (0 : ℝ) < ε / 2 + RCLike.re w from by linarith [h.1, hε])]
  have him2 : RCLike.im w * RCLike.im w < (ε / 2) * (ε / 2) := by
    have h := abs_lt.mp him
    nlinarith [mul_pos (sub_pos.mpr h.2)
      (show (0 : ℝ) < ε / 2 + RCLike.im w from by linarith [h.1, hε])]
  have hsq : ‖w‖ ^ 2 < ε ^ 2 := by
    rw [RCLike.norm_sq_eq_def]
    nlinarith [hre2, him2, mul_pos hε hε]
  have hnorm : ‖w‖ < ε := by
    have h := abs_lt_of_sq_lt_sq hsq (le_of_lt hε)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [dist_eq_norm]
  exact hnorm

/-- Finite sequences with coefficients in `ℚ + ℚ * I`: the index is a
finite set `s` together with a rational pair for each `i ∈ s`. The
index type is countable, since `s` is finite. -/
noncomputable def ratApproxSeq (p : Σ s : Finset ℕ, (s → ℚ × ℚ)) : ℓ²(ℕ, 𝕜) :=
  ∑ i : ↥p.1, lp.single 2 (i : ℕ) ((ratApproxScalar (𝕜 := 𝕜)) (p.2 i))

/-- The finite `ℚ + ℚ * I`-coefficient sequences are dense in `ℓ²(ℕ, 𝕜)`. -/
theorem dense_range_ratApproxSeq : Dense (Set.range (ratApproxSeq (𝕜 := 𝕜))) := by
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  have hT := (lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hT) (ε / 2) (half_pos hε)
  -- The truncation of `x` to the first `N` coordinates is within `ε / 2` of `x`.
  set s₀ := Finset.range N with hs₀
  have htrunc : dist (∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)) x < ε / 2 := hN N le_rfl
  -- Approximate each coefficient of the truncation by a rational approximant.
  set c : ℝ := (s₀.card : ℝ) with hc
  set δ : ℝ := ε / (2 * (c + 1)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    exact div_pos hε (mul_pos two_pos (by linarith))
  have hchoice : ∀ i ∈ s₀, ∃ q : ℚ × ℚ, ‖(x : ℕ → 𝕜) i - ratApproxScalar q‖ < δ := by
    intro i _
    obtain ⟨y, hyball, ⟨q, hq⟩⟩ :=
      dense_range_ratApproxScalar.inter_open_nonempty _ Metric.isOpen_ball
        ⟨(x : ℕ → 𝕜) i, Metric.mem_ball_self hδpos⟩
    refine ⟨q, ?_⟩
    have hd : dist y ((x : ℕ → 𝕜) i) < δ := Metric.mem_ball.mp hyball
    rw [← hq, dist_eq_norm, norm_sub_rev] at hd
    exact hd
  have hchoice' : ∀ i, ∃ q : ℚ × ℚ, i ∈ s₀ → ‖(x : ℕ → 𝕜) i - ratApproxScalar q‖ < δ := by
    intro i
    by_cases hi : i ∈ s₀
    · obtain ⟨q, hq⟩ := hchoice i hi
      exact ⟨q, fun _ => hq⟩
    · exact ⟨(0, 0), fun h => absurd h hi⟩
  choose g hg using hchoice'
  -- The rational approximant `y` is within `ε / 2` of the truncation.
  set g' : ↥s₀ → ℚ × ℚ := fun i => g (i : ℕ) with hg'
  set y : ℓ²(ℕ, 𝕜) := ratApproxSeq ⟨s₀, g'⟩ with hy
  have hy_rat : y = ∑ i ∈ s₀, lp.single 2 i (ratApproxScalar (g i)) := by
    show (∑ i : ↥s₀, lp.single 2 (i : ℕ) (ratApproxScalar (g' i))) = _
    exact Finset.sum_attach s₀ (fun i => lp.single 2 i (ratApproxScalar (g i)))
  have hdiff : y - ∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i) =
      ∑ i ∈ s₀, lp.single 2 i (ratApproxScalar (g i) - (x : ℕ → 𝕜) i) := by
    rw [hy_rat, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (lp.single_sub 2 i _ _).symm
  have hnorm2 : ‖y - ∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)‖ ^ 2 < (ε / 2) ^ 2 := by
    have hsum : ‖∑ i ∈ s₀, lp.single 2 i (ratApproxScalar (g i) - (x : ℕ → 𝕜) i)‖ ^ (2 : ℝ) =
        ∑ i ∈ s₀, ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ ^ (2 : ℝ) := by
      have h := lp.norm_sum_single (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
        (fun i => ratApproxScalar (g i) - (x : ℕ → 𝕜) i) s₀
      rwa [show (2 : ℝ≥0∞).toReal = (2 : ℝ) from by simp] at h
    have hsum2 : ‖∑ i ∈ s₀, lp.single 2 i (ratApproxScalar (g i) - (x : ℕ → 𝕜) i)‖ ^ 2 =
        ∑ i ∈ s₀, ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ ^ 2 := by
      have h := hsum
      simp only [Real.rpow_two] at h
      exact h
    rw [hdiff, hsum2]
    have hterm : ∀ i ∈ s₀, ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ ^ 2 < δ ^ 2 := by
      intro i hi
      have h := hg i hi
      rw [norm_sub_rev] at h
      nlinarith [mul_pos (sub_pos.mpr h)
        (show (0 : ℝ) < δ + ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ from by
          linarith [norm_nonneg (ratApproxScalar (g i) - (x : ℕ → 𝕜) i), hδpos])]
    have hsumle : ∑ i ∈ s₀, ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ ^ 2 ≤ s₀.card • δ ^ 2 :=
      Finset.sum_le_card_nsmul s₀ _ _ fun i hi => le_of_lt (hterm i hi)
    have hcard : (s₀.card : ℝ) * δ ^ 2 < (ε / 2) ^ 2 := by
      have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
      have hc1 : (0 : ℝ) < c + 1 := by linarith
      have hlt : c < (c + 1) ^ 2 := by nlinarith [sq_nonneg c]
      have hfrac : c / (c + 1) ^ 2 < 1 := by
        rw [div_lt_one (pow_pos hc1 2)]
        exact hlt
      have heq : (s₀.card : ℝ) * δ ^ 2 = (c / (c + 1) ^ 2) * (ε / 2) ^ 2 := by
        rw [hδ, ← hc]
        field_simp
      rw [heq]
      calc (c / (c + 1) ^ 2) * (ε / 2) ^ 2
          < 1 * (ε / 2) ^ 2 :=
            mul_lt_mul_of_pos_right hfrac (pow_pos (half_pos hε) 2)
        _ = (ε / 2) ^ 2 := one_mul _
    rw [nsmul_eq_mul] at hsumle
    have hc_eq : (s₀.card : ℝ) = c := rfl
    rw [hc_eq] at hsumle
    exact lt_of_le_of_lt hsumle hcard
  have hnorm : ‖y - ∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)‖ < ε / 2 := by
    have h := abs_lt_of_sq_lt_sq hnorm2 (le_of_lt (half_pos hε))
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  refine ⟨y, ?_, ⟨⟨s₀, g'⟩, rfl⟩⟩
  apply hball
  rw [Metric.mem_ball]
  have hdist : dist y x ≤ dist y (∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)) +
      dist (∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)) x := dist_triangle _ _ _
  rw [dist_eq_norm] at htrunc
  simp only [dist_eq_norm] at hdist
  rw [dist_eq_norm]
  linarith [hnorm, htrunc]

/-! ### Finitely supported vectors -/

/-- The span of the single-coordinate vectors is dense in `ℓ²(ℕ, 𝕜)`:
every vector is the sum of its canonical series. -/
theorem dense_span_single :
    Dense (↑(Submodule.span 𝕜
      (Set.range fun i => (lp.single 2 i (1 : 𝕜) : ℓ²(ℕ, 𝕜)))) : Set (ℓ²(ℕ, 𝕜))) := by
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro x
  refine mem_closure_of_tendsto
    ((lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat) ?_
  refine Eventually.of_forall fun s => ?_
  exact sum_mem fun i _ => by
    have h : lp.single (E := fun _ : ℕ => 𝕜) 2 i ((x : ℕ → 𝕜) i) =
        (x : ℕ → 𝕜) i • lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜) := by
      rw [← lp.single_smul]
      simp [smul_eq_mul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Every vector in the span of the single-coordinate vectors is
eventually zero: it has finite support. -/
theorem exists_forall_eq_zero_of_mem_span_single {x : ℓ²(ℕ, 𝕜)}
    (hx : x ∈ Submodule.span 𝕜 (Set.range fun i => lp.single 2 i (1 : 𝕜))) :
    ∃ N, ∀ i, N ≤ i → (x : ℕ → 𝕜) i = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨i + 1, fun j hj => ?_⟩
    show (↑(lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)) : ℕ → 𝕜) j = 0
    exact lp.single_apply_ne (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜) (by omega : j ≠ i)
  | zero => exact ⟨0, fun _ _ => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N₁, h₁⟩ := hy
    obtain ⟨N₂, h₂⟩ := hz
    refine ⟨max N₁ N₂, fun i hi => ?_⟩
    rw [lp.coeFn_add, Pi.add_apply, h₁ i (le_trans (le_max_left _ _) hi),
      h₂ i (le_trans (le_max_right _ _) hi), add_zero]
  | smul c y _ hy =>
    obtain ⟨N, hN⟩ := hy
    exact ⟨N, fun i hi => by rw [lp.coeFn_smul, Pi.smul_apply, hN i hi, smul_zero]⟩

/-! ### Rolewicz's theorem -/

/-- **Rolewicz's theorem.** The scalar multiple `μ • B` of the backward
shift on `ℓ²(ℕ, 𝕜)` is hypercyclic if and only if `‖μ‖ > 1`. -/
theorem isHypercyclic_smul_backwardShiftCLM_iff (μ : 𝕜) :
    IsHypercyclic ((μ • backwardShiftCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))) ↔ 1 < ‖μ‖ := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hx⟩ := h
    have hbound : ∀ n, ‖((μ • backwardShiftCLM) ^ n) x‖ ≤ ‖x‖ := by
      intro n
      rw [smul_backwardShiftCLM_pow_apply, norm_smul, norm_pow]
      calc ‖μ‖ ^ n * ‖(backwardShiftCLM ^ n) x‖
          ≤ (1 : ℝ) * ‖x‖ :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) hlt)
              (norm_backwardShiftCLM_pow_apply_le n x) (norm_nonneg _) zero_le_one
        _ = ‖x‖ := one_mul _
    have hmem : ((‖x‖ + 1 : ℝ) : 𝕜) • lp.single 2 0 (1 : 𝕜) ∈
        closure (Set.range fun n => ((μ • backwardShiftCLM) ^ n) x) := by
      rw [hx.closure_eq]
      exact Set.mem_univ _
    have hsub : closure (Set.range fun n => ((μ • backwardShiftCLM) ^ n) x) ⊆
        Metric.closedBall 0 ‖x‖ := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      rintro y ⟨n, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hbound n
    have hle := hsub hmem
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      lp.norm_single (by simp : (0 : ℝ≥0∞) < 2), norm_one, mul_one, RCLike.norm_ofReal,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ + 1)] at hle
    linarith [norm_nonneg x]
  · intro hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hμ
      exact (by norm_num : ¬ (1 : ℝ) < 0) hμ
    refine isHypercyclic_of_criterion _ (Set.range (ratApproxSeq (𝕜 := 𝕜)))
      (↑(Submodule.span 𝕜
        (Set.range fun i => (lp.single 2 i (1 : 𝕜) : ℓ²(ℕ, 𝕜)))) : Set (ℓ²(ℕ, 𝕜)))
      (↑(Submodule.span 𝕜
        (Set.range fun i => (lp.single 2 i (1 : 𝕜) : ℓ²(ℕ, 𝕜)))) : Set (ℓ²(ℕ, 𝕜)))
      (Set.countable_range (ratApproxSeq (𝕜 := 𝕜))) dense_range_ratApproxSeq
      dense_span_single dense_span_single
      (fun n y => (μ ^ n)⁻¹ • (forwardShiftCLM ^ n) y) ?_ ?_ ?_
    · intro x hx
      have hx' : x ∈ Submodule.span 𝕜 (Set.range fun i => lp.single 2 i (1 : 𝕜)) := hx
      obtain ⟨N, hN⟩ := exists_forall_eq_zero_of_mem_span_single hx'
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
      have hzero : (backwardShiftCLM ^ n) x = 0 := by
        apply lp.ext
        funext i
        rw [backwardShiftCLM_pow_apply]
        exact hN (i + n) (by omega)
      rw [smul_backwardShiftCLM_pow_apply, hzero, smul_zero]
    · intro y _
      show Tendsto (fun n => (μ ^ n)⁻¹ • (forwardShiftCLM ^ n) y) atTop (𝓝 0)
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hnormlim : Tendsto (fun n => ‖(μ ^ n)⁻¹ • (forwardShiftCLM ^ n) y‖) atTop (𝓝 0) := by
        have hnorm : ∀ n, ‖(μ ^ n)⁻¹ • (forwardShiftCLM ^ n) y‖ = (‖μ‖⁻¹) ^ n * ‖y‖ := by
          intro n
          rw [norm_smul, norm_inv, norm_pow, inv_pow, norm_forwardShiftCLM_pow_apply]
        simp_rw [hnorm]
        have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one
          (inv_nonneg.mpr (norm_nonneg μ)) (inv_lt_one_of_one_lt₀ hμ)).mul_const ‖y‖
        simpa using hlim
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hnormlim) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have h := hN n hn
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
      rwa [dist_zero_right]
    · intro n y _
      show ((μ • backwardShiftCLM) ^ n) ((μ ^ n)⁻¹ • (forwardShiftCLM ^ n) y) = y
      rw [smul_backwardShiftCLM_pow_apply, map_smul,
        backwardShiftCLM_pow_forwardShiftCLM_pow_apply, smul_smul,
        mul_inv_cancel₀ (pow_ne_zero n hμ0), one_smul]

end MathlibExt.Analysis.FunctionalAnalysis.Rolewicz
