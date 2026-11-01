/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Gamma
public import MathlibExt.Probability.Distributions.GammaMoments

import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Poisson–Gamma duality and the exact (Garwood) upper confidence bound for a Poisson mean

The Poisson distribution function `F_k(x) = P(Poisson(x) ≤ k) = ∑_{j ≤ k} e^{-x} x^j / (j!)`
is a Gamma upper tail, `F_k(x) = P(Gamma(k + 1, 1) > x)`. It is continuous and strictly
decreasing in the mean `x ≥ 0`, from `F_k(0) = 1` to `0`, and strictly increasing in `k`.
Garwood's exact one-sided upper confidence bound for a Poisson mean after observing `k` is
the root `u_α(k)` of `F_k(u) = α`; it covers the true mean with probability at least `1 - α`
for every mean.

## Main results

* `poissonMeasure_real_Iic`: `F_k(r)` is the distribution function of `poissonMeasure r`.
* `hasDerivAt_poissonCDF`: `∂_x F_k(x) = -e^{-x} x^k / (k!)`.
* `gammaMeasure_real_Ioi_poissonCDF`: **Poisson–Gamma duality** with Mathlib's Gamma law of
  shape `k + 1` and rate `r`: `P(Gamma(k + 1, r) > x) = F_k(r x)` for `0 < r`, `0 ≤ x`
  (a corollary of `gammaMeasure_real_Ioi_natCast_add_one` in `GammaMoments`).
* `poissonCDF_strictAntiOn`, `poissonCDF_lt_poissonCDF_succ`, `tendsto_poissonCDF_atTop`:
  monotonicity in the mean and in `k`, and the limit `0` as the mean grows.
* `garwoodUpper`: the bound `u_α(k) = sup {x ≥ 0 | α ≤ F_k(x)}`; `poissonCDF_garwoodUpper`
  (it solves `F_k(u) = α`), `le_garwoodUpper_iff`, `garwoodUpper_strictMono` (strictly
  increasing in `k`), `garwoodUpper_zero` (`u_α(0) = log (1 / α)`).
* `poissonMeasure_real_poissonCDF_le`: `P(F_r(K) ≤ α) ≤ α` for `K ~ Poisson(r)` and `α ≥ 0`, the
  super-uniformity of the distribution-function transform of a discrete law.
* `garwoodUpper_coverage`: **exact coverage**, `P_r(r ≤ u_α(K)) ≥ 1 - α` for every `r ≥ 0`.

## Conventions

The mean is a real `x` in the analytic statements (the identities hold for all real `x`
where stated) and a nonnegative `r : ℝ≥0` in the measure statements, matching Mathlib's
`poissonMeasure`. The confidence level is `0 < α < 1`. Outside that range `garwoodUpper` is
a junk value (`sSup` of an empty or unbounded set is `0` in `ℝ`).

## References

* F. Garwood, *Fiducial limits for the Poisson distribution*, Biometrika 28 (1936), 437–442.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley
  (2005), ch. 4 (the Poisson–Gamma relation and exact confidence limits).
-/

@[expose] public section

open Real Finset MeasureTheory Set Filter Topology
open scoped NNReal Nat

namespace ProbabilityTheory

/-- The Poisson distribution function `F_k(x) = ∑_{j ≤ k} e^{-x} x^j / (j!)` as a function of
the mean `x` (defined for every real `x`; it is a probability only for `0 ≤ x`). -/
noncomputable def poissonCDF (x : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), exp (-x) * x ^ j / (j ! : ℝ)

/-- `poissonCDF r k` is the distribution function of Mathlib's `poissonMeasure r` at `k`. -/
theorem poissonMeasure_real_Iic (r : ℝ≥0) (k : ℕ) :
    (poissonMeasure r).real (Set.Iic k) = poissonCDF r k := by
  have hset : Set.Iic k = (Finset.range (k + 1) : Set ℕ) := by
    ext n
    simp only [Set.mem_Iic, mem_coe, Finset.mem_range, Nat.lt_succ_iff]
  rw [hset, ← sum_measureReal_singleton]
  simp only [poissonMeasure_real_singleton, poissonCDF]

/-- At mean `0` the Poisson law is the point mass at `0`: `F_k(0) = 1`. -/
theorem poissonCDF_zero_left (k : ℕ) : poissonCDF 0 k = 1 := by
  induction k with
  | zero => simp [poissonCDF]
  | succ k ih => simpa [poissonCDF, sum_range_succ] using ih

/-- `F_0(x) = e^{-x}`. -/
theorem poissonCDF_zero_right (x : ℝ) : poissonCDF x 0 = exp (-x) := by
  simp [poissonCDF]

/-- The distribution function is positive at every real mean. -/
theorem poissonCDF_pos {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 < poissonCDF x k := by
  apply sum_pos'
  · intro j hj
    positivity
  · exact ⟨0, by simp, by simpa using exp_pos (-x)⟩

/-- The derivative in the mean telescopes: `∂_x F_k(x) = -e^{-x} x^k / (k!)`. -/
theorem hasDerivAt_poissonCDF (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => poissonCDF y k) (-(exp (-x) * x ^ k / (k ! : ℝ))) x := by
  have he : HasDerivAt (fun y : ℝ => exp (-y)) (-exp (-x)) x := by
    simpa using (hasDerivAt_id x).neg.exp
  induction k with
  | zero =>
      simpa only [poissonCDF_zero_right, pow_zero, Nat.factorial_zero,
        Nat.cast_one, mul_one, div_one] using he
  | succ k ih =>
      have hd := ih.add ((he.mul (hasDerivAt_pow (k + 1) x)).div_const
        ((k + 1)! : ℝ))
      convert hd using 1
      · ext y
        change poissonCDF y (k + 1) =
          poissonCDF y k + exp (-y) * y ^ (k + 1) / ((k + 1)! : ℝ)
        exact sum_range_succ _ _
      · simp only [Nat.add_sub_cancel, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hk : (k ! : ℝ) ≠ 0 := by positivity
        have hsucc : (k : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring

/-- The distribution function is continuous in the mean. -/
theorem continuous_poissonCDF (k : ℕ) : Continuous fun x => poissonCDF x k := by
  exact continuous_iff_continuousAt.mpr fun x => (hasDerivAt_poissonCDF k x).continuousAt

/-- **Poisson–Gamma duality**: the Gamma law of shape `k + 1` and rate `r` (Mathlib's
`gammaMeasure`) has upper tail `P(Gamma(k + 1, r) > x) = F_k(r x)`. This is the Erlang tail
`gammaMeasure_real_Ioi_natCast_add_one` in `GammaMoments`, rewritten with the definition of
`poissonCDF`. -/
theorem gammaMeasure_real_Ioi_poissonCDF (k : ℕ) {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    (gammaMeasure (k + 1) r).real (Ioi x) = poissonCDF (r * x) k := by
  rw [gammaMeasure_real_Ioi_natCast_add_one k hr hx]
  simp only [poissonCDF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc]

/-- The distribution function is strictly decreasing in the mean on `[0, ∞)`. -/
theorem poissonCDF_strictAntiOn (k : ℕ) : StrictAntiOn (fun x => poissonCDF x k) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) (continuous_poissonCDF k).continuousOn
  intro x hx
  have hx0 : 0 < x := by simpa using hx
  rw [(hasDerivAt_poissonCDF k x).deriv]
  exact neg_neg_of_pos (by positivity)

/-- The distribution function is strictly increasing in `k` at every positive mean. -/
theorem poissonCDF_lt_poissonCDF_succ {x : ℝ} (hx : 0 < x) (k : ℕ) :
    poissonCDF x k < poissonCDF x (k + 1) := by
  simp only [poissonCDF, sum_range_succ]
  exact lt_add_of_pos_right _ (by positivity)

/-- The distribution function is monotone in `k` at every nonnegative mean. -/
theorem poissonCDF_mono {x : ℝ} (hx : 0 ≤ x) : Monotone fun k => poissonCDF x k := by
  intro j k hjk
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    fun i _ _ => by positivity

/-- For fixed `k`, `F_k(x) → 0` as the mean `x → ∞`. -/
theorem tendsto_poissonCDF_atTop (k : ℕ) :
    Tendsto (fun x => poissonCDF x k) atTop (𝓝 0) := by
  have ht : ∀ j ∈ range (k + 1),
      Tendsto (fun x : ℝ => exp (-x) * x ^ j / (j ! : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    intro j hj
    simpa only [mul_comm, zero_div] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).div_const (j ! : ℝ)
  simpa only [poissonCDF, sum_const_zero] using tendsto_finsetSum (range (k + 1)) ht

/-- For a fixed nonnegative mean, `F_k(x) → 1` as `k → ∞`. -/
theorem tendsto_poissonCDF_nat {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun k => poissonCDF x k) atTop (𝓝 1) := by
  simpa [poissonCDF, Function.comp_def, NNReal.coe_mk] using
    (hasSum_one_poissonMeasure (NNReal.mk x hx)).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)

/-- **Garwood's exact upper confidence bound** for a Poisson mean after observing `k`, at
level `α`: `u_α(k) = sup {x ≥ 0 | α ≤ F_k(x)}`. For `0 < α < 1` it is the root of
`F_k(u) = α` (`poissonCDF_garwoodUpper`). -/
noncomputable def garwoodUpper (α : ℝ) (k : ℕ) : ℝ :=
  sSup {x : ℝ | 0 ≤ x ∧ α ≤ poissonCDF x k}

private theorem poissonCDF_root_exists (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (k : ℕ) : ∃ u : ℝ, 0 < u ∧ poissonCDF u k = α := by
  have ht : ∀ᶠ x in atTop, poissonCDF x k < α :=
    (tendsto_poissonCDF_atTop k).eventually (gt_mem_nhds hα0)
  obtain ⟨b, hb0, hb⟩ := ((eventually_gt_atTop (0 : ℝ)).and ht).exists
  have hα : α ∈ Set.Icc (poissonCDF b k) (poissonCDF 0 k) := by
    simp only [Set.mem_Icc, poissonCDF_zero_left]
    exact ⟨hb.le, hα1.le⟩
  obtain ⟨u, hu, hroot⟩ :=
    intermediate_value_Icc' hb0.le (continuous_poissonCDF k).continuousOn hα
  change poissonCDF u k = α at hroot
  refine ⟨u, ?_, hroot⟩
  by_contra h
  have hu0 : u = 0 := le_antisymm (le_of_not_gt h) hu.1
  rw [hu0, poissonCDF_zero_left] at hroot
  linarith

private theorem garwoodUpper_eq_root (α : ℝ) (k : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hroot : poissonCDF u k = α) : garwoodUpper α k = u := by
  have hs : {x : ℝ | 0 ≤ x ∧ α ≤ poissonCDF x k} = Set.Icc 0 u := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      by_contra h
      have hlt := poissonCDF_strictAntiOn k hu hx.1 (lt_of_not_ge h)
      change poissonCDF x k < poissonCDF u k at hlt
      rw [hroot] at hlt
      exact (not_lt_of_ge hx.2) hlt
    · intro hx
      refine ⟨hx.1, ?_⟩
      simpa only [hroot] using (poissonCDF_strictAntiOn k).antitoneOn hx.1 hu hx.2
  rw [garwoodUpper, hs, csSup_Icc hu]

/-- The bound is positive for `0 < α < 1`. -/
theorem garwoodUpper_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    0 < garwoodUpper α k := by
  obtain ⟨u, hu, hr⟩ := poissonCDF_root_exists α hα0 hα1 k
  rw [garwoodUpper_eq_root α k u hu.le hr]
  exact hu

/-- The bound solves `F_k(u_α(k)) = α`. -/
theorem poissonCDF_garwoodUpper {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    poissonCDF (garwoodUpper α k) k = α := by
  obtain ⟨u, hu, hr⟩ := poissonCDF_root_exists α hα0 hα1 k
  rw [garwoodUpper_eq_root α k u hu.le hr]
  exact hr

/-- A nonnegative mean lies below the bound iff it is not rejected: `x ≤ u_α(k) ↔ α ≤ F_k(x)`.
-/
theorem le_garwoodUpper_iff {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : x ≤ garwoodUpper α k ↔ α ≤ poissonCDF x k := by
  have hu := (garwoodUpper_pos hα0 hα1 k).le
  have hr := poissonCDF_garwoodUpper hα0 hα1 k
  constructor
  · intro h
    simpa only [hr] using (poissonCDF_strictAntiOn k).antitoneOn hx hu h
  · intro h
    by_contra hle
    have hlt := poissonCDF_strictAntiOn k hu hx (lt_of_not_ge hle)
    change poissonCDF x k < poissonCDF (garwoodUpper α k) k at hlt
    rw [hr] at hlt
    exact (not_lt_of_ge h) hlt

/-- The bound is strictly increasing in the observed count. -/
theorem garwoodUpper_strictMono {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    StrictMono (garwoodUpper α) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hu := garwoodUpper_pos hα0 hα1 k
  have hlt : α < poissonCDF (garwoodUpper α k) (k + 1) := by
    calc
      α = poissonCDF (garwoodUpper α k) k := (poissonCDF_garwoodUpper hα0 hα1 k).symm
      _ < poissonCDF (garwoodUpper α k) (k + 1) := poissonCDF_lt_poissonCDF_succ hu k
  have hle := (le_garwoodUpper_iff hα0 hα1 (k + 1) hu.le).mpr hlt.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  rw [heq, poissonCDF_garwoodUpper hα0 hα1 (k + 1)] at hlt
  exact lt_irrefl _ hlt

/-- After observing `0` the bound is `u_α(0) = log (1 / α)` (`e^{-u} = α`). -/
theorem garwoodUpper_zero {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    garwoodUpper α 0 = log (1 / α) := by
  have hr := poissonCDF_garwoodUpper hα0 hα1 0
  rw [poissonCDF_zero_right] at hr
  have heq : -(garwoodUpper α 0) = log α := by
    calc
      -(garwoodUpper α 0) = log (exp (-garwoodUpper α 0)) := (log_exp _).symm
      _ = log α := congrArg log hr
  rw [one_div, log_inv]
  linarith

private theorem poissonMeasure_real_range (r : ℝ≥0) (m : ℕ) :
    (poissonMeasure r).real (Finset.range m : Set ℕ) =
      ∑ j ∈ range m, exp (-(r : ℝ)) * (r : ℝ) ^ j / (j ! : ℝ) := by
  rw [← sum_measureReal_singleton]
  simp only [poissonMeasure_real_singleton]

/-- **Super-uniformity of the distribution-function transform**: for `K ~ Poisson(r)` and
every `α ≥ 0`, `P(F_r(K) ≤ α) ≤ α`. (For `α < 0` the event is empty.) -/
theorem poissonMeasure_real_poissonCDF_le (r : ℝ≥0) {α : ℝ} (hα : 0 ≤ α) :
    (poissonMeasure r).real {k | poissonCDF r k ≤ α} ≤ α := by
  rcases le_or_gt 1 α with h1 | h1
  · exact (measureReal_le_one).trans h1
  have hex : ∃ k, α < poissonCDF r k :=
    ((tendsto_order.1 (tendsto_poissonCDF_nat r.2)).1 α h1).exists
  classical
  set m := Nat.find hex
  have hset : {k | poissonCDF r k ≤ α} = (Finset.range m : Set ℕ) := by
    ext k
    simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro hk
      by_contra hkm
      have := poissonCDF_mono r.2 (le_of_not_gt hkm) |>.trans_lt' (Nat.find_spec hex)
      exact absurd hk (not_le.mpr this)
    · intro hk
      exact not_lt.1 (Nat.find_min hex hk)
  rw [hset, poissonMeasure_real_range]
  rcases Nat.eq_zero_or_eq_succ_pred m with hm | hm
  · rw [hm]; simpa using hα
  · rw [hm]
    exact not_lt.1 (Nat.find_min hex (by omega : m - 1 < m))

/-- **Exact coverage of Garwood's bound**: for every mean `r ≥ 0` and `0 < α < 1`,
`P_r(r ≤ u_α(K)) ≥ 1 - α` when `K ~ Poisson(r)`. -/
theorem garwoodUpper_coverage (r : ℝ≥0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α ≤ (poissonMeasure r).real {k | (r : ℝ) ≤ garwoodUpper α k} := by
  have hset : {k | (r : ℝ) ≤ garwoodUpper α k} = {k | poissonCDF r k < α}ᶜ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    exact le_garwoodUpper_iff hα0 hα1 k r.2
  rw [hset, probReal_compl_eq_one_sub (MeasurableSet.of_discrete)]
  have := (measureReal_mono (μ := poissonMeasure r) (s₁ := {k | poissonCDF r k < α})
    (s₂ := {k | poissonCDF r k ≤ α}) fun k (hk : poissonCDF r k < α) => hk.le).trans
    (poissonMeasure_real_poissonCDF_le r hα0.le)
  linarith

end ProbabilityTheory
