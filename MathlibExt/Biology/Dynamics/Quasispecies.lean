/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Eigen's error threshold for the single-peak quasispecies

Eigen's quasispecies model on a single-peak fitness landscape has one *master* sequence of
length `L` that replicates with relative fitness `σ > 1`, while every mutant replicates with
fitness `1`. Each copy of the master is error-free with probability `Q = q ^ L`, where `q` is
the per-site copying fidelity. Neglecting back mutation from mutants to the master (the
standard approximation of Eigen 1971 and Nowak 2006, ch. 3), the master frequency `x`
(mutants `1 - x`) obeys

  `x' = σ Q x - φ(x) x`,   `φ(x) = σ x + (1 - x)` (mean fitness),

which is the logistic equation `x' = x ((σ Q - 1) - (σ - 1) x)` (`masterField_eq`).

## Main results

* `masterField_eq_zero_iff`: the equilibria are `x = 0` and `x* = (σ Q - 1) / (σ - 1)`.
* `masterEquilibrium_pos_iff`, `masterEquilibrium_le_one`: for `σ > 1` and `Q ≤ 1`, the
  interior equilibrium lies in `(0, 1]` iff `σ Q > 1` (the **error threshold**).
* `one_lt_mul_pow_iff`: for `0 < q < 1` and `σ > 0`, `σ q ^ L > 1` iff
  `L < log σ / (-log q)`, the maximal genome length.
* `tendsto_masterEquilibrium_fidelity`: the fixed-`q_L` limit. With `q_L = 1 - μ / L`
  (`μ` = expected mutations per genome copy), `x*_L → (σ e^{-μ} - 1)/(σ - 1)`, which is
  positive iff `μ < log σ` (`masterEquilibrium_exp_pos_iff`).
* `tendsto_master_of_one_lt`, `tendsto_master_zero_of_le_one`: every solution started at a
  positive master frequency converges to `x*` above the threshold and to `0` at or below it.

The statement is the finite-`L` two-class system with `Q = q_L ^ L`; the limit `L → ∞` is
taken only along `q_L = 1 - μ / L`, so that `σ q_L ^ L → σ e^{-μ}` (see the correction of the
"`σ q ^ L > 1` as `L → ∞`" phrasing in the source roadmap). Back mutation, the full mutation
matrix and its Perron eigenvector are not modeled here.

## References

* M. Eigen, *Selforganization of matter and the evolution of biological macromolecules*,
  Naturwissenschaften 58 (1971) 465–523.
* M. A. Nowak, *Evolutionary Dynamics: Exploring the Equations of Life*, Harvard University
  Press (2006), ch. 3.
-/

@[expose] public section

open Filter Topology Real

namespace MathlibExt.Biology.Dynamics.Quasispecies

/-- The master-sequence vector field of the single-peak quasispecies without back mutation:
`x' = σ Q x - (σ x + (1 - x)) x`, where `σ` is the master fitness relative to the mutants and
`Q` the probability of an error-free copy. Meaningful for `σ > 1`, `0 ≤ Q ≤ 1`,
`0 ≤ x ≤ 1`; it is a polynomial and is defined for all reals. -/
def masterField (σ Q x : ℝ) : ℝ :=
  σ * Q * x - (σ * x + (1 - x)) * x

/-- The interior equilibrium `x* = (σ Q - 1) / (σ - 1)` of the master frequency. For
`σ = 1` (no selective advantage) Lean's `x / 0 = 0` gives the junk value `0`; every result
below assumes `1 < σ`. -/
noncomputable def masterEquilibrium (σ Q : ℝ) : ℝ :=
  (σ * Q - 1) / (σ - 1)

/-- The master-sequence equation is logistic: `x' = x ((σ Q - 1) - (σ - 1) x)`. -/
theorem masterField_eq (σ Q x : ℝ) :
    masterField σ Q x = x * ((σ * Q - 1) - (σ - 1) * x) := by
  unfold masterField; ring

/-- The equilibria of the master frequency are `0` and `x* = (σ Q - 1)/(σ - 1)`. -/
theorem masterField_eq_zero_iff {σ Q x : ℝ} (hσ : 1 < σ) :
    masterField σ Q x = 0 ↔ x = 0 ∨ x = masterEquilibrium σ Q := by
  have h : σ - 1 ≠ 0 := by linarith
  rw [masterField_eq, mul_eq_zero, masterEquilibrium, eq_div_iff h]
  constructor <;> rintro (h1 | h1) <;> [left; right; left; right] <;> linarith

/-- The mutant frequency at the interior equilibrium is `1 - x* = σ (1 - Q)/(σ - 1)`. -/
theorem one_sub_masterEquilibrium {σ : ℝ} (hσ : 1 < σ) (Q : ℝ) :
    1 - masterEquilibrium σ Q = σ * (1 - Q) / (σ - 1) := by
  have h : σ - 1 ≠ 0 := by linarith
  rw [masterEquilibrium]; field_simp; ring

/-- **Error threshold.** For `σ > 1`, the interior equilibrium is positive iff `σ Q > 1`. -/
theorem masterEquilibrium_pos_iff {σ : ℝ} (hσ : 1 < σ) (Q : ℝ) :
    0 < masterEquilibrium σ Q ↔ 1 < σ * Q := by
  rw [masterEquilibrium, div_pos_iff_of_pos_right (by linarith)]
  constructor <;> intro h <;> linarith

/-- For `σ > 1` and `Q ≤ 1` the interior equilibrium is at most `1`. -/
theorem masterEquilibrium_le_one {σ Q : ℝ} (hσ : 1 < σ) (hQ : Q ≤ 1) :
    masterEquilibrium σ Q ≤ 1 := by
  rw [masterEquilibrium, div_le_one (by linarith)]
  nlinarith

/-- **Maximal genome length.** For per-site fidelity `0 < q < 1` and `σ > 0`,
`σ q ^ L > 1` iff `L < log σ / (-log q)`. -/
theorem one_lt_mul_pow_iff {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q < 1) (L : ℕ) :
    1 < σ * q ^ L ↔ (L : ℝ) < log σ / (-log q) := by
  have hlq : log q < 0 := log_neg hq0 hq1
  have hpos : 0 < σ * q ^ L := mul_pos hσ (pow_pos hq0 L)
  rw [lt_div_iff₀ (by linarith), ← log_lt_log_iff one_pos hpos, log_one,
    log_mul hσ.ne' (pow_pos hq0 L).ne', log_pow]
  constructor <;> intro h <;> nlinarith

/-- The interior equilibrium depends continuously on `Q`, so any sequence of fidelities with
`Q_L → Qlim` has `x*(Q_L) → x*(Qlim)`. -/
theorem tendsto_masterEquilibrium {σ : ℝ} {Q : ℕ → ℝ} {Qlim : ℝ}
    (hQ : Tendsto Q atTop (𝓝 Qlim)) :
    Tendsto (fun L ↦ masterEquilibrium σ (Q L)) atTop (𝓝 (masterEquilibrium σ Qlim)) :=
  ((hQ.const_mul σ).sub_const 1).div_const (σ - 1)

/-- **Fixed-`q_L` limit.** With per-site fidelity `q_L = 1 - μ / L`, so that the expected number
of mutations per genome copy is `μ`, the error-free probability is `q_L ^ L → e^{-μ}` and the
master equilibrium converges to `(σ e^{-μ} - 1)/(σ - 1)`. -/
theorem tendsto_masterEquilibrium_fidelity (σ μ : ℝ) :
    Tendsto (fun L : ℕ ↦ masterEquilibrium σ ((1 - μ / L) ^ L)) atTop
      (𝓝 (masterEquilibrium σ (exp (-μ)))) := by
  refine tendsto_masterEquilibrium ?_
  simpa [sub_eq_add_neg, neg_div] using Real.tendsto_one_add_div_pow_exp (-μ)

/-- In the fixed-`q_L` limit the master sequence persists iff `μ < log σ`. -/
theorem masterEquilibrium_exp_pos_iff {σ : ℝ} (hσ : 1 < σ) (μ : ℝ) :
    0 < masterEquilibrium σ (exp (-μ)) ↔ μ < log σ := by
  rw [masterEquilibrium_pos_iff hσ, ← exp_log (by linarith : (0 : ℝ) < σ), ← exp_add,
    one_lt_exp_iff, exp_log (by linarith)]
  constructor <;> intro h <;> linarith

private theorem const_on_nonneg {f : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f 0 t) {t : ℝ} (ht : 0 ≤ t) : f t = f 0 := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ ↦ (0 : ℝ)) (C := 0)
    (fun (u : ℝ) (hu : u ∈ Set.Ici 0) ↦ (hf u hu).hasDerivWithinAt)
    (fun _ _ ↦ by simp only [norm_zero]; exact le_rfl)
    (show (0 : ℝ) ∈ Set.Ici 0 from le_rfl) ht
  have hz : f t - f 0 = 0 := norm_le_zero_iff.mp (by simpa using h)
  exact sub_eq_zero.mp hz

private theorem logistic_pos {r a : ℝ} {x : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (x t * (r - a * x t)) t)
    (h0 : 0 < x 0) {t : ℝ} (ht : 0 ≤ t) : 0 < x t := by
  let c : ℝ → ℝ := fun u ↦ r - a * x (max u 0)
  have hxc : ContinuousOn x (Set.Ici 0) :=
    fun u hu ↦ (hx u hu).continuousAt.continuousWithinAt
  have hc : Continuous c := continuous_const.sub (continuous_const.mul
    (hxc.comp_continuous (continuous_id.max continuous_const) (fun u ↦ le_max_right u 0)))
  let I : ℝ → ℝ := fun u ↦ ∫ v in 0..u, c v
  have hI (u : ℝ) : HasDerivAt I (c u) u :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hF : ∀ u, 0 ≤ u → HasDerivAt (fun v ↦ x v * exp (-I v)) 0 u := by
    intro u hu
    convert (hx u hu).mul (hI u).neg.exp using 1
    dsimp [c]
    rw [max_eq_left hu]
    ring
  have heq := const_on_nonneg hF ht
  have hp : 0 < x t * exp (-I t) := by
    rw [heq]
    simpa [I] using h0
  exact (mul_pos_iff_of_pos_right (exp_pos _)).mp hp

private theorem logistic_inv_eq {r a : ℝ} (hr : r ≠ 0) {x : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (x t * (r - a * x t)) t)
    (h0 : 0 < x 0) {t : ℝ} (ht : 0 ≤ t) :
    (x t)⁻¹ = a / r + ((x 0)⁻¹ - a / r) * exp (-(r * t)) := by
  have hF : ∀ u, 0 ≤ u →
      HasDerivAt (fun v ↦ exp (r * v) * ((x v)⁻¹ - a / r)) 0 u := by
    intro u hu
    have hp := (logistic_pos hx h0 hu).ne'
    convert (((hasDerivAt_id u).const_mul r).exp).mul
      (((hx u hu).inv hp).sub_const (a / r)) using 1
    · rfl
    · simp only [id_eq, Pi.inv_apply, mul_one]
      field_simp [hp, hr]
      ring
  have heq := const_on_nonneg hF ht
  simp only [mul_zero, exp_zero, one_mul] at heq
  have he : exp (r * t) * exp (-(r * t)) = 1 := by
    rw [← exp_add]; simp
  have hm := congrArg (fun z : ℝ ↦ z * exp (-(r * t))) heq
  rw [mul_right_comm, he, one_mul] at hm
  linarith

private theorem logistic_inv_eq_zero {a : ℝ} {x : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (x t * (0 - a * x t)) t)
    (h0 : 0 < x 0) {t : ℝ} (ht : 0 ≤ t) : (x t)⁻¹ = (x 0)⁻¹ + a * t := by
  have hF : ∀ u, 0 ≤ u → HasDerivAt (fun v ↦ (x v)⁻¹ - a * v) 0 u := by
    intro u hu
    have hp := (logistic_pos hx h0 hu).ne'
    convert ((hx u hu).inv hp).sub ((hasDerivAt_id u).const_mul a) using 1
    · rfl
    · simp only [mul_one]
      field_simp [hp]
      ring
  have heq := const_on_nonneg hF ht
  simp only [mul_zero, sub_zero] at heq
  linarith

/-- **Convergence above the threshold.** If `σ > 1`, `σ Q > 1` and `x` solves the master
equation on `[0, ∞)` from a positive master frequency, then `x t → x*`. -/
theorem tendsto_master_of_one_lt {σ Q : ℝ} (hσ : 1 < σ) (hth : 1 < σ * Q) {x : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (masterField σ Q (x t)) t) (h0 : 0 < x 0) :
    Tendsto x atTop (𝓝 (masterEquilibrium σ Q)) := by
  let r := σ * Q - 1
  let a := σ - 1
  have hr : 0 < r := by dsimp [r]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hd : ∀ t, 0 ≤ t → HasDerivAt x (x t * (r - a * x t)) t := by
    intro t ht
    simpa only [masterField_eq] using hx t ht
  have heq : (fun t ↦ (x t)⁻¹) =ᶠ[atTop]
      (fun t ↦ a / r + ((x 0)⁻¹ - a / r) * exp (-(r * t))) :=
    eventually_atTop.2 ⟨0, fun t ht ↦ logistic_inv_eq hr.ne' hd h0 ht⟩
  have he : Tendsto (fun t : ℝ ↦ exp (-(r * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
  have hi : Tendsto (fun t ↦ (x t)⁻¹) atTop (𝓝 (a / r)) := by
    have hf := (he.const_mul ((x 0)⁻¹ - a / r)).const_add (a / r)
    simp only [mul_zero, add_zero] at hf
    exact hf.congr' heq.symm
  simpa only [inv_inv, inv_div, masterEquilibrium] using
    hi.inv₀ (div_ne_zero ha.ne' hr.ne')

/-- **Loss of the master at or below the threshold.** If `σ > 1`, `σ Q ≤ 1` and `x` solves the
master equation on `[0, ∞)` from a positive master frequency, then `x t → 0`. -/
theorem tendsto_master_zero_of_le_one {σ Q : ℝ} (hσ : 1 < σ) (hth : σ * Q ≤ 1) {x : ℝ → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (masterField σ Q (x t)) t) (h0 : 0 < x 0) :
    Tendsto x atTop (𝓝 0) := by
  let r := σ * Q - 1
  let a := σ - 1
  have hr : r ≤ 0 := by dsimp [r]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hd : ∀ t, 0 ≤ t → HasDerivAt x (x t * (r - a * x t)) t := by
    intro t ht
    simpa only [masterField_eq] using hx t ht
  have hi : Tendsto (fun t ↦ (x t)⁻¹) atTop atTop := by
    rcases eq_or_lt_of_le hr with hz | hn
    · have hd0 : ∀ t, 0 ≤ t → HasDerivAt x (x t * (0 - a * x t)) t := by
        simpa only [hz] using hd
      have heq : (fun t ↦ (x t)⁻¹) =ᶠ[atTop] (fun t ↦ (x 0)⁻¹ + a * t) :=
        eventually_atTop.2 ⟨0, fun t ht ↦ logistic_inv_eq_zero hd0 h0 ht⟩
      exact (tendsto_atTop_add_const_left atTop (x 0)⁻¹
        (tendsto_id.const_mul_atTop ha)).congr' heq.symm
    · have hc : 0 < (x 0)⁻¹ - a / r := by
        have hdiv : a / r < 0 := div_neg_of_pos_of_neg ha hn
        have hpos : 0 < (x 0)⁻¹ := inv_pos.mpr h0
        linarith
      have heq : (fun t ↦ (x t)⁻¹) =ᶠ[atTop]
          (fun t ↦ a / r + ((x 0)⁻¹ - a / r) * exp (-(r * t))) :=
        eventually_atTop.2 ⟨0, fun t ht ↦ logistic_inv_eq hn.ne hd h0 ht⟩
      have he : Tendsto (fun t : ℝ ↦ exp (-(r * t))) atTop atTop := by
        simpa only [neg_mul, Function.comp_def, id_eq] using
          tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (neg_pos.mpr hn))
      exact (tendsto_atTop_add_const_left atTop (a / r) (he.const_mul_atTop hc)).congr' heq.symm
  simpa only [Pi.inv_def, inv_inv] using hi.inv_tendsto_atTop

end MathlibExt.Biology.Dynamics.Quasispecies
