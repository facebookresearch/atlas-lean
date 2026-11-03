/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Process-level fixation probability and absorption time of the Wright–Fisher diffusion

`MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher` proves the analytic half of
Kimura's theory: Kimura's formula `kimuraFixation σ` solves the backward equation
`L_σ u = 0`, `u 0 = 0`, `u 1 = 1`, and the Kimura–Ohta function `meanAbsorptionTime` solves
`L_0 T = -1`, `T 0 = T 1 = 0`. This file proves the probabilistic half: these functions are
the fixation probability and the mean absorption time of the diffusion process itself.

The process is specified by the martingale problem of Stroock and Varadhan (Ethier–Kurtz
1986, ch. 4 and 8; ch. 10 for Wright–Fisher, where the problem is shown to be well posed): a
continuous `[0, 1]`-valued process `X`, adapted to a filtration `ℱ` indexed by time
`t : ℝ≥0` (units of `2N` generations), such that for every `C²` test function `f`,
`f (X t) - f (X 0) - ∫₀ᵗ (L_σ f) (X s) ds` is an `ℱ`-martingale, where
`L_σ f = x (1 - x) / 2 · f'' + σ x (1 - x) · f'` is `Diffusion.generator σ f` and
`σ = 2Ns` is the scaled genic selection coefficient (`IsWrightFisherSolution`).

## Main results

* `IsWrightFisherSolution`, `absorptionTime`: the martingale problem and the first time the
  path is at `0` or `1`.
* `Diffusion.contDiff_kimuraFixation`, `Diffusion.kimuraSlope_pos`,
  `Diffusion.strictMono_kimuraFixation`: regularity and monotonicity of Kimura's formula.
* `ae_exists_absorbed`: a solution is almost surely absorbed in finite time.
* `measureReal_fixation`: it is eventually fixed with probability `kimuraFixation σ x`.
* `integral_absorptionTime`: in the neutral case the expected absorption time is
  `meanAbsorptionTime x`.

## Method

No stochastic calculus or continuous-time optional stopping is used; only the martingale
property at fixed times. With `u = kimuraFixation σ` and the polynomials
`p_n(y) = -2 ∑_{k < n} (y ^ (k + 2) + (1 - y) ^ (k + 2)) / ((k + 1) (k + 2))`, one has
`L_σ (p_n ∘ u)(x) = -x (1 - x) u'(x)² q_n(u x)` with `q_n(y) = ∑_{k < n} (y ^ k + (1 - y) ^ k)`
and `y (1 - y) q_n(y) = 1 - y ^ (n + 1) - (1 - y) ^ (n + 1)`. Since `p_n ∘ u` is bounded on
`[0, 1]` uniformly in `n`, the expected time spent in any `[a, 1 - a]` is bounded uniformly,
which forces a.s. hitting of `{0, 1}`. The nonnegative martingales `u (X t)` and
`1 - u (X t)` cannot leave `0` once they hit it (a finite-grid argument along a dense
sequence of times), so the boundary absorbs; dominated convergence then gives
`P(fixation) = u x`. In the neutral case
`p_n (y) - p_n 0 → T(y)` and `L_0 p_n = -(1 - y ^ (n + 1) - (1 - y) ^ (n + 1))`, which yields
`E[min(t, τ)] = T(x) - E[T(X t)]` and, letting `t → ∞`, `E[τ] = T(x)`.

## References

* M. Kimura, *On the probability of fixation of mutant genes in a population*,
  Genetics 47 (1962) 713–719.
* M. Kimura and T. Ohta, *The average number of generations until fixation of a mutant gene in
  a finite population*, Genetics 61 (1969) 763–771.
* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 4, 8 and 10.
* S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981),
  ch. 15.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), ch. 4.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

open MathlibExt.Biology.PopulationGenetics.Diffusion (generator kimuraFixation
  meanAbsorptionTime kimuraSlope)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `X` solves the **martingale problem for the Wright–Fisher diffusion** with scaled genic
selection coefficient `σ = 2Ns` (time in units of `2N` generations) with respect to the
filtration `ℱ` and the measure `μ`: `X` takes values in `[0, 1]`, has continuous paths, is
adapted to `ℱ`, and for every `C²` function `f` the process
`f (X t) - f (X 0) - ∫₀ᵗ generator σ f (X s) ds` is an `ℱ`-martingale. -/
def IsWrightFisherSolution (σ : ℝ) (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t ω, X t ω ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ ω, Continuous fun t => X t ω) ∧
    StronglyAdapted ℱ X ∧
    ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
      Martingale (fun t ω => f (X t ω) - f (X 0 ω) -
        ∫ s in (0 : ℝ)..(t : ℝ), generator σ f (X (Real.toNNReal s) ω)) ℱ μ

/-- The absorption time of a `[0, 1]`-valued path: the first time it is at `0` or `1`
(the infimum of the empty set is `0` in `ℝ≥0`; the path is absorbed almost surely, see
`ae_exists_absorbed`). -/
noncomputable def absorptionTime (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t | X t ω = 0 ∨ X t ω = 1}

/-! ### Analytic lemmas -/

/-- Kimura's fixation probability is a `C²` function of the initial frequency on all of `ℝ`. -/
theorem _root_.MathlibExt.Biology.PopulationGenetics.Diffusion.contDiff_kimuraFixation
    (σ : ℝ) : ContDiff ℝ 2 (kimuraFixation σ) := by
  by_cases h : σ = 0
  · subst h
    have hk : kimuraFixation 0 = id := funext Diffusion.kimuraFixation_neutral
    rw [hk]
    exact contDiff_id
  · have hk : kimuraFixation σ = fun y => (1 - Real.exp (-2 * σ * y)) / (1 - Real.exp (-2 * σ)) :=
      funext fun y => by simp [kimuraFixation, h]
    rw [hk]
    exact (contDiff_const.sub ((contDiff_const.mul contDiff_id).exp)).div_const _

/-- The slope constant of Kimura's formula is positive. -/
theorem _root_.MathlibExt.Biology.PopulationGenetics.Diffusion.kimuraSlope_pos (σ : ℝ) :
    0 < kimuraSlope σ := by
  unfold kimuraSlope
  split_ifs with h
  · exact one_pos
  rcases lt_or_gt_of_ne h with hσ | hσ
  · have : 1 < Real.exp (-2 * σ) := Real.one_lt_exp_iff.2 (by linarith)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · have : Real.exp (-2 * σ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    exact div_pos (by linarith) (by linarith)

/-- Kimura's fixation probability is strictly increasing in the initial frequency. -/
theorem _root_.MathlibExt.Biology.PopulationGenetics.Diffusion.strictMono_kimuraFixation
    (σ : ℝ) : StrictMono (kimuraFixation σ) :=
  strictMono_of_deriv_pos fun x => by
    rw [Diffusion.deriv_kimuraFixation]
    exact mul_pos (kimuraSlope_pos σ) (Real.exp_pos _)

/-- The polynomial `p_n(y) = -2 ∑_{k < n} (y ^ (k + 2) + (1 - y) ^ (k + 2)) / ((k + 1) (k + 2))`,
with `p_n'' = -2 ∑_{k < n} (y ^ k + (1 - y) ^ k)`. -/
private noncomputable def occPoly (n : ℕ) (y : ℝ) : ℝ :=
  -2 * ∑ k ∈ Finset.range n, (y ^ (k + 2) + (1 - y) ^ (k + 2)) / ((k + 1) * (k + 2))

/-- `1 - y ^ (n + 1) - (1 - y) ^ (n + 1)`, which tends to the indicator of `(0, 1)` on
`[0, 1]`. -/
private def occRate (n : ℕ) (y : ℝ) : ℝ := 1 - y ^ (n + 1) - (1 - y) ^ (n + 1)

private theorem contDiff_occPoly (n : ℕ) : ContDiff ℝ 2 (occPoly n) := by
  unfold occPoly
  fun_prop

private theorem contDiff_occPoly_comp (σ : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (fun y => occPoly n (kimuraFixation σ y)) :=
  (contDiff_occPoly n).comp (contDiff_kimuraFixation σ)

private theorem sum_inv_mul_succ (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1) * (k + 2)) = 1 - 1 / (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

private theorem occPoly_mem_Icc (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    occPoly n y ∈ Icc (-4 : ℝ) 0 := by
  have h1y : 0 ≤ 1 - y := sub_nonneg.2 hy.2
  have hterm : ∀ k : ℕ, 0 ≤ (y ^ (k + 2) + (1 - y) ^ (k + 2)) / ((k + 1) * (k + 2)) ∧
      (y ^ (k + 2) + (1 - y) ^ (k + 2)) / ((k + 1) * (k + 2)) ≤ 1 / ((k + 1) * (k + 2)) := by
    intro k
    have hpos : (0 : ℝ) < (k + 1) * (k + 2) := by positivity
    refine ⟨div_nonneg (add_nonneg (pow_nonneg hy.1 _) (pow_nonneg h1y _)) hpos.le,
      div_le_div_of_nonneg_right ?_ hpos.le⟩
    have := pow_le_of_le_one hy.1 hy.2 (by omega : k + 2 ≠ 0)
    have := pow_le_of_le_one h1y (by linarith [hy.1]) (by omega : k + 2 ≠ 0)
    linarith
  have hS0 := Finset.sum_nonneg fun k (_ : k ∈ Finset.range n) => (hterm k).1
  have hS1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => (hterm k).2
  rw [sum_inv_mul_succ] at hS1
  have : (0 : ℝ) ≤ 1 / (n + 1) := by positivity
  unfold occPoly
  constructor <;> nlinarith

/-- `q_n(y) = ∑_{k < n} (y ^ k + (1 - y) ^ k)`, so that `p_n'' = -2 q_n`. -/
private noncomputable def occQ (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (y ^ k + (1 - y) ^ k)

/-- `p_n' = -2 ∑_{k < n} (y ^ (k + 1) - (1 - y) ^ (k + 1)) / (k + 1)`. -/
private noncomputable def occPoly' (n : ℕ) (y : ℝ) : ℝ :=
  -2 * ∑ k ∈ Finset.range n, (y ^ (k + 1) - (1 - y) ^ (k + 1)) / (k + 1)

private theorem hasDerivAt_occPoly (n : ℕ) (y : ℝ) :
    HasDerivAt (occPoly n) (occPoly' n y) y := by
  unfold occPoly occPoly'
  refine HasDerivAt.const_mul _ ?_
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have := ((hasDerivAt_pow (k + 2) y).add (h1.pow (k + 2))).div_const
    (((k : ℝ) + 1) * (k + 2))
  convert this using 1
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  simp only [show k + 2 - 1 = k + 1 by omega]
  field_simp
  push_cast
  ring

private theorem hasDerivAt_occPoly' (n : ℕ) (y : ℝ) :
    HasDerivAt (occPoly' n) (-2 * occQ n y) y := by
  unfold occPoly' occQ
  refine HasDerivAt.const_mul _ ?_
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have := ((hasDerivAt_pow (k + 1) y).sub (h1.pow (k + 1))).div_const ((k : ℝ) + 1)
  convert this using 1
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel]
  field_simp
  push_cast
  ring

private theorem mul_occQ (n : ℕ) (y : ℝ) : y * (1 - y) * occQ n y = occRate n y := by
  induction n with
  | zero => simp [occQ, occRate]
  | succ n ih =>
    rw [occQ, Finset.sum_range_succ, mul_add, ← occQ, ih]
    simp only [occRate]
    ring

private theorem occQ_nonneg (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ occQ n y :=
  Finset.sum_nonneg fun _ _ => add_nonneg (pow_nonneg hy.1 _) (pow_nonneg (sub_nonneg.2 hy.2) _)

/-- Chain rule for the generator: `L_σ (p_n ∘ u) = -x (1 - x) u'² q_n(u)` (`u'' + 2σu' = 0`). -/
private theorem generator_occPoly_comp (σ : ℝ) (n : ℕ) (x : ℝ) :
    generator σ (fun y => occPoly n (kimuraFixation σ y)) x =
      -(x * (1 - x) * (kimuraSlope σ * Real.exp (-2 * σ * x)) ^ 2 *
        occQ n (kimuraFixation σ x)) := by
  have hD : deriv (fun y => occPoly n (kimuraFixation σ y)) =
      fun y => occPoly' n (kimuraFixation σ y) * (kimuraSlope σ * Real.exp (-2 * σ * y)) :=
    funext fun y => ((hasDerivAt_occPoly n _).comp y
      (Diffusion.hasDerivAt_kimuraFixation σ y)).deriv
  have hE : HasDerivAt (fun y => kimuraSlope σ * Real.exp (-2 * σ * y))
      (kimuraSlope σ * (Real.exp (-2 * σ * x) * (-2 * σ))) x := by
    refine HasDerivAt.const_mul _ ?_
    simpa using ((hasDerivAt_id x).const_mul (-2 * σ)).exp
  have hDD : HasDerivAt (fun y => occPoly' n (kimuraFixation σ y) *
      (kimuraSlope σ * Real.exp (-2 * σ * y))) _ x :=
    ((hasDerivAt_occPoly' n _).comp x (Diffusion.hasDerivAt_kimuraFixation σ x)).mul hE
  rw [generator, hD, hDD.deriv]
  simp only [Function.comp_apply]
  ring

private theorem generator_occPoly_comp_nonpos (σ : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    generator σ (fun y => occPoly n (kimuraFixation σ y)) x ≤ 0 := by
  rw [generator_occPoly_comp, neg_nonpos]
  have := occQ_nonneg n (Diffusion.kimuraFixation_mem_Icc σ hx)
  have : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.2 hx.2)
  positivity

private theorem exists_le_neg_generator_occPoly_comp (σ : ℝ) :
    ∃ ε > 0, ∀ a ∈ Ioo (0 : ℝ) (1 / 2), ∃ n : ℕ, ∀ x ∈ Icc a (1 - a),
      ε ≤ -generator σ (fun y => occPoly n (kimuraFixation σ y)) x := by
  have hK := kimuraSlope_pos σ
  set m₀ := min 1 (Real.exp (-2 * σ)) with hm₀def
  set M₀ := max 1 (Real.exp (-2 * σ)) with hM₀def
  have hm₀ : 0 < m₀ := lt_min one_pos (Real.exp_pos _)
  have hM₀ : 0 < M₀ := lt_max_of_lt_left one_pos
  have hexp : ∀ y ∈ Icc (0 : ℝ) 1,
      m₀ ≤ Real.exp (-2 * σ * y) ∧ Real.exp (-2 * σ * y) ≤ M₀ := by
    intro y hy
    rcases le_total 0 σ with hσ | hσ
    · have h1 : Real.exp (-2 * σ) ≤ Real.exp (-2 * σ * y) :=
        Real.exp_le_exp.2 (by nlinarith [hy.2])
      have h2 : Real.exp (-2 * σ * y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hy.1])
      exact ⟨(min_le_right _ _).trans h1, h2.trans (le_max_left _ _)⟩
    · have h1 : 1 ≤ Real.exp (-2 * σ * y) := Real.one_le_exp (by nlinarith [hy.1])
      have h2 : Real.exp (-2 * σ * y) ≤ Real.exp (-2 * σ) :=
        Real.exp_le_exp.2 (by nlinarith [hy.2])
      exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩
  have hdiff : Differentiable ℝ (kimuraFixation σ) := fun y =>
    (Diffusion.hasDerivAt_kimuraFixation σ y).differentiableAt
  have hmvt : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      kimuraFixation σ b - kimuraFixation σ a ≤ kimuraSlope σ * M₀ * (b - a) := by
    intro a ha b hb hab
    refine (convex_Icc 0 1).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
      hdiff.differentiableOn (fun y hy => ?_) a ha b hb hab
    rw [interior_Icc] at hy
    rw [Diffusion.deriv_kimuraFixation]
    exact mul_le_mul_of_nonneg_left (hexp y (Ioo_subset_Icc_self hy)).2 hK.le
  set c := (m₀ / M₀) ^ 2 with hcdef
  have hc : 0 < c := by positivity
  have hkey : ∀ x ∈ Icc (0 : ℝ) 1, c * (kimuraFixation σ x * (1 - kimuraFixation σ x)) ≤
      x * (1 - x) * (kimuraSlope σ * Real.exp (-2 * σ * x)) ^ 2 := by
    intro x hx
    have h1 : kimuraFixation σ x ≤ kimuraSlope σ * M₀ * x := by
      simpa using hmvt 0 ⟨le_rfl, zero_le_one⟩ x hx hx.1
    have h2 : 1 - kimuraFixation σ x ≤ kimuraSlope σ * M₀ * (1 - x) := by
      simpa using hmvt x hx 1 ⟨zero_le_one, le_rfl⟩ hx.2
    have hu01 := Diffusion.kimuraFixation_mem_Icc σ hx
    have h3 : kimuraSlope σ * m₀ ≤ kimuraSlope σ * Real.exp (-2 * σ * x) :=
      mul_le_mul_of_nonneg_left (hexp x hx).1 hK.le
    have hx0 : 0 ≤ kimuraSlope σ * M₀ * x := by have := hx.1; positivity
    have h4 : kimuraFixation σ x * (1 - kimuraFixation σ x) ≤
        (kimuraSlope σ * M₀) ^ 2 * (x * (1 - x)) := by
      calc kimuraFixation σ x * (1 - kimuraFixation σ x)
          ≤ (kimuraSlope σ * M₀ * x) * (kimuraSlope σ * M₀ * (1 - x)) :=
            mul_le_mul h1 h2 (sub_nonneg.2 hu01.2) hx0
        _ = _ := by ring
    have h5 : (kimuraSlope σ * m₀) ^ 2 ≤ (kimuraSlope σ * Real.exp (-2 * σ * x)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h3 2
    have hx1 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.2 hx.2)
    calc c * (kimuraFixation σ x * (1 - kimuraFixation σ x))
        ≤ c * ((kimuraSlope σ * M₀) ^ 2 * (x * (1 - x))) := mul_le_mul_of_nonneg_left h4 hc.le
      _ = (kimuraSlope σ * m₀) ^ 2 * (x * (1 - x)) := by
          rw [hcdef]
          field_simp
      _ ≤ (kimuraSlope σ * Real.exp (-2 * σ * x)) ^ 2 * (x * (1 - x)) :=
          mul_le_mul_of_nonneg_right h5 hx1
      _ = _ := by ring
  refine ⟨c / 2, by positivity, fun a ha => ?_⟩
  have hsm := strictMono_kimuraFixation σ
  have hua : 0 < kimuraFixation σ a := by
    simpa using hsm ha.1
  have hu1a : kimuraFixation σ (1 - a) < 1 := by
    simpa using hsm (by linarith [ha.1] : 1 - a < 1)
  have huaa : kimuraFixation σ a < kimuraFixation σ (1 - a) := hsm (by linarith [ha.2])
  set b := max (kimuraFixation σ (1 - a)) (1 - kimuraFixation σ a) with hbdef
  have hb0 : 0 ≤ b := le_max_of_le_left (by linarith)
  have hb1 : b < 1 := max_lt hu1a (by linarith)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 4) hb1
  refine ⟨n, fun x hx => ?_⟩
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ha.1, hx.1], by linarith [ha.1, hx.2]⟩
  have hux := Diffusion.kimuraFixation_mem_Icc σ hx01
  rw [generator_occPoly_comp, neg_neg]
  have hz1 : kimuraFixation σ x ≤ b := (hsm.monotone hx.2).trans (le_max_left _ _)
  have hz2 : 1 - kimuraFixation σ x ≤ b :=
    (by linarith [hsm.monotone hx.1] : 1 - kimuraFixation σ x ≤ 1 - kimuraFixation σ a).trans
      (le_max_right _ _)
  have hbn : b ^ (n + 1) ≤ b ^ n := pow_le_pow_of_le_one hb0 hb1.le (Nat.le_succ n)
  have hp1 : kimuraFixation σ x ^ (n + 1) ≤ b ^ n :=
    (pow_le_pow_left₀ hux.1 hz1 _).trans hbn
  have hp2 : (1 - kimuraFixation σ x) ^ (n + 1) ≤ b ^ n :=
    (pow_le_pow_left₀ (sub_nonneg.2 hux.2) hz2 _).trans hbn
  have hrate : 1 / 2 ≤ occRate n (kimuraFixation σ x) := by
    unfold occRate
    linarith
  have hq := occQ_nonneg n hux
  calc c / 2 ≤ c * occRate n (kimuraFixation σ x) := by nlinarith
    _ = c * (kimuraFixation σ x * (1 - kimuraFixation σ x)) * occQ n (kimuraFixation σ x) := by
        rw [← mul_occQ]
        ring
    _ ≤ x * (1 - x) * (kimuraSlope σ * Real.exp (-2 * σ * x)) ^ 2 *
          occQ n (kimuraFixation σ x) :=
        mul_le_mul_of_nonneg_right (hkey x hx01) hq

private theorem generator_occPoly (n : ℕ) (x : ℝ) :
    generator 0 (occPoly n) x = -occRate n x := by
  have h := generator_occPoly_comp 0 n x
  simp only [Diffusion.kimuraFixation_neutral, kimuraSlope, ↓reduceIte, mul_zero, zero_mul,
    Real.exp_zero, one_pow, mul_one] at h
  rw [h, ← mul_occQ]

private theorem occRate_mem_Icc (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    occRate n y ∈ Icc (0 : ℝ) 1 := by
  have h1y : 0 ≤ 1 - y := sub_nonneg.2 hy.2
  have h1 := pow_le_of_le_one hy.1 hy.2 (by omega : n + 1 ≠ 0)
  have h2 := pow_le_of_le_one h1y (by linarith [hy.1]) (by omega : n + 1 ≠ 0)
  have h3 : 0 ≤ y ^ (n + 1) := pow_nonneg hy.1 _
  have h4 : 0 ≤ (1 - y) ^ (n + 1) := pow_nonneg h1y _
  unfold occRate
  constructor <;> linarith

private theorem tendsto_occRate {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => occRate n y) atTop (𝓝 1) := by
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hy.1.le hy.2).comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.2 hy.2.le)
    (by linarith [hy.1] : 1 - y < 1)).comp (tendsto_add_atTop_nat 1)
  simpa [occRate, Function.comp_def] using (tendsto_const_nhds (x := (1 : ℝ))).sub h1 |>.sub h2

private theorem occRate_zero (n : ℕ) : occRate n 0 = 0 := by
  simp [occRate]

private theorem occRate_one (n : ℕ) : occRate n 1 = 0 := by
  simp [occRate]

private theorem occPoly_one (n : ℕ) : occPoly n 1 = occPoly n 0 := by
  simp [occPoly, add_comm]

private theorem tendsto_occPoly_sub {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => occPoly n x - occPoly n 0) atTop (𝓝 (meanAbsorptionTime x)) := by
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · subst h0
    simp
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst h1
    simp [occPoly_one]
  have hc : HasSum (fun k : ℕ => (1 : ℝ) / ((k + 1) * (k + 2))) 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
    simp only [sum_inv_mul_succ]
    have : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have h1x : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hsum : ∀ y ∈ Ioo (0 : ℝ) 1, HasSum (fun k : ℕ => y ^ (k + 2) / ((k + 1) * (k + 2)))
      ((1 - y) * Real.log (1 - y) + y) := by
    intro y hy
    have hy1 : |y| < 1 := by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
    have h := Real.hasSum_pow_div_log_of_abs_lt_one hy1
    have hA := h.mul_left y
    have hB := (hasSum_nat_add_iff' 1).2 h
    convert hA.sub hB using 1
    · funext k
      push_cast
      field_simp
      ring
    · simp
      ring
  have hS := (((hsum x hx').add (hsum (1 - x) h1x)).sub hc).mul_left (-2)
  have hT := hS.tendsto_sum_nat
  convert hT using 1
  · funext n
    simp only [occPoly, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  · simp only [meanAbsorptionTime, sub_sub_cancel]
    ring_nf

/-! ### Two facts about continuous processes -/

/-- For a martingale and finitely many times `r ≤ t`, the integral of `Y t` over the event that
`Y r ≤ δ` for one of them is at most that of the constant `δ`. -/
private theorem finite_hit_bound {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℝ≥0 → Ω → ℝ} (hY : Martingale Y ℱ μ) (t : ℝ≥0) (δ : ℝ)
    (S : Finset ℝ≥0) (ht : ∀ r ∈ S, r ≤ t) :
    (∫ ω in {ω | ∃ r ∈ S, Y r ω ≤ δ}, Y t ω ∂μ) ≤
      ∫ _ in {ω | ∃ r ∈ S, Y r ω ≤ δ}, δ ∂μ := by
  classical
  revert ht
  induction S using Finset.induction_on_max with
  | empty => simp
  | @insert a S hmax ih =>
    intro ht
    let E : Set Ω := {ω | ∃ r ∈ S, Y r ω ≤ δ}
    let A : Set Ω := {ω | Y a ω ≤ δ} \ E
    have hE : MeasurableSet[ℱ a] E := by
      have heq : E = ⋃ r ∈ S, {ω | Y r ω ≤ δ} := by ext; simp [E]
      rw [heq]
      exact Finset.measurableSet_biUnion S fun r hr =>
        measurableSet_le ((hY.stronglyMeasurable r).mono
          (ℱ.mono (hmax r hr).le)).measurable measurable_const
    have hA : MeasurableSet[ℱ a] A :=
      (measurableSet_le (hY.stronglyMeasurable a).measurable measurable_const).diff hE
    have hA0 : MeasurableSet A := ℱ.le a A hA
    have hdis : Disjoint E A := by
      apply Set.disjoint_left.mpr
      intro ω hω hAω
      exact hAω.2 hω
    have heq : {ω | ∃ r ∈ insert a S, Y r ω ≤ δ} = E ∪ A := by
      ext ω
      simp only [Finset.mem_insert, or_and_right, exists_or, exists_eq_left]
      change (Y a ω ≤ δ ∨ ω ∈ E) ↔ ω ∈ E ∨ (Y a ω ≤ δ ∧ ω ∉ E)
      tauto
    rw [heq, setIntegral_union hdis hA0 (hY.integrable t).integrableOn
      (hY.integrable t).integrableOn,
      setIntegral_union hdis hA0 (integrable_const δ).integrableOn
        (integrable_const δ).integrableOn]
    refine add_le_add (ih (fun r hr => ht r (Finset.mem_insert_of_mem hr))) ?_
    rw [← hY.setIntegral_eq (ht a (Finset.mem_insert_self a S)) hA]
    exact setIntegral_mono_on (hY.integrable a).integrableOn
      (integrable_const δ).integrableOn hA0 fun ω hω => hω.1

/-- The countable version of `finite_hit_bound` along `min (u k) t`, for `0 ≤ δ`. -/
private theorem countable_hit_bound {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℝ≥0 → Ω → ℝ} (hY : Martingale Y ℱ μ)
    (t : ℝ≥0) (δ : ℝ) (hδ : 0 ≤ δ) (u : ℕ → ℝ≥0) :
    (∫ ω in {ω | ∃ k, Y (min (u k) t) ω ≤ δ}, Y t ω ∂μ) ≤ δ := by
  classical
  let S : ℕ → Finset ℝ≥0 := fun n => (Finset.range n).image (fun k => min (u k) t)
  let E : ℕ → Set Ω := fun n => {ω | ∃ r ∈ S n, Y r ω ≤ δ}
  have hE : ∀ n, MeasurableSet (E n) := by
    intro n
    have heq : E n = ⋃ r ∈ S n, {ω | Y r ω ≤ δ} := by ext; simp [E]
    rw [heq]
    exact Finset.measurableSet_biUnion (S n) fun r _ =>
      measurableSet_le ((hY.stronglyMeasurable r).mono (ℱ.le r)).measurable
        measurable_const
  have hmono : Monotone E := by
    intro n m hnm ω hω
    rcases hω with ⟨r, hr, hYω⟩
    refine ⟨r, ?_, hYω⟩
    exact Finset.image_subset_image (Finset.range_mono hnm) hr
  have heq : (⋃ n, E n) = {ω | ∃ k, Y (min (u k) t) ω ≤ δ} := by
    ext ω
    simp only [mem_iUnion, E, mem_ofPred_eq, S, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨n, r, ⟨k, _, rfl⟩, hω⟩
      exact ⟨k, hω⟩
    · rintro ⟨k, hω⟩
      exact ⟨k + 1, min (u k) t, ⟨k, Nat.lt_succ_self k, rfl⟩, hω⟩
  rw [← heq]
  apply le_of_tendsto (tendsto_setIntegral_of_monotone hE hmono
    (hY.integrable t).integrableOn)
  exact Eventually.of_forall fun n => (finite_hit_bound hY t δ (S n) (by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨k, _, rfl⟩
    exact min_le_right _ _)).trans (by
      calc (∫ _ in E n, δ ∂μ) ≤ ∫ _, δ ∂μ :=
             setIntegral_le_integral (integrable_const δ) (Eventually.of_forall fun _ => hδ)
           _ = δ := by simp)

/-- For a fixed time `t`, a.s. a continuous nonnegative martingale that is `0` before `t` is `0`
at `t`. -/
private theorem fixed_time_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℝ≥0 → Ω → ℝ} (hY : Martingale Y ℱ μ) (hnn : ∀ t ω, 0 ≤ Y t ω)
    (hc : ∀ ω, Continuous fun t => Y t ω) (u : ℕ → ℝ≥0) (hu : DenseRange u)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ s, s < t → Y s ω = 0 → Y t ω = 0 := by
  let E : ℕ → Set Ω := fun m =>
    {ω | ∃ k, Y (min (u k) t) ω ≤ 1 / ((m : ℝ) + 1)}
  let D : Set Ω := ⋂ m, E m
  have hE : ∀ m, MeasurableSet (E m) := by
    intro m
    have heq : E m = ⋃ k, {ω | Y (min (u k) t) ω ≤ 1 / ((m : ℝ) + 1)} := by
      ext; simp [E]
    rw [heq]
    exact MeasurableSet.iUnion fun k =>
      measurableSet_le ((hY.stronglyMeasurable (min (u k) t)).mono
        (ℱ.le _)).measurable measurable_const
  have hD : MeasurableSet D := MeasurableSet.iInter hE
  have hbound : ∀ m : ℕ, (∫ ω in D, Y t ω ∂μ) ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    refine (setIntegral_mono_set (hY.integrable t).integrableOn
      (Eventually.of_forall fun ω => hnn t ω) ?_).trans
        (countable_hit_bound hY t _ (by positivity) u)
    exact Eventually.of_forall fun ω hω => mem_iInter.mp hω m
  have hzero : (∫ ω in D, Y t ω ∂μ) = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
        (Eventually.of_forall hbound)
    · exact integral_nonneg (hnn t)
  have hae : ∀ᵐ ω ∂μ, ω ∈ D → Y t ω = 0 := by
    apply (ae_restrict_iff' hD).mp
    exact (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun ω => hnn t ω) (hY.integrable t).integrableOn).mp hzero
  filter_upwards [hae] with ω hω
  intro s hst hs
  apply hω
  apply mem_iInter.mpr
  intro m
  have hδ : 0 < 1 / ((m : ℝ) + 1) := by positivity
  obtain ⟨k, hr⟩ := hu.exists_mem_open
    ((isOpen_lt (hc ω) continuous_const).inter isOpen_Iio)
    (show ({r | Y r ω < 1 / ((m : ℝ) + 1)} ∩ Iio t).Nonempty from
      ⟨s, by simpa [hs] using hδ, hst⟩)
  refine ⟨k, ?_⟩
  rw [min_eq_left (show u k ≤ t from hr.2.le)]
  exact hr.1.le

/-- A nonnegative martingale with continuous paths stays at `0` once it hits `0`. -/
private theorem ae_stay_zero_of_martingale {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : ℝ≥0 → Ω → ℝ} (hY : Martingale Y ℱ μ)
    (hnn : ∀ t ω, 0 ≤ Y t ω) (hc : ∀ ω, Continuous fun t => Y t ω) :
    ∀ᵐ ω ∂μ, ∀ s t, s ≤ t → Y s ω = 0 → Y t ω = 0 := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ s, s < u k → Y s ω = 0 → Y (u k) ω = 0 :=
    ae_all_iff.mpr fun k => fixed_time_zero hY hnn hc u hu (u k)
  filter_upwards [hall] with ω hω
  intro s t hst hs
  rcases hst.eq_or_lt with rfl | hst
  · exact hs
  · by_contra ht
    obtain ⟨k, hr⟩ := hu.exists_mem_open
      ((isOpen_ne_fun (hc ω) continuous_const).inter isOpen_Ioi)
      (show ({r | Y r ω ≠ 0} ∩ Ioi s).Nonempty from ⟨t, ht, hst⟩)
    exact hr.1 (hω k s hr.2 hs)

/-- A `[0, 1]`-valued process with continuous paths whose expected occupation time of every
`[a, 1 - a]` is bounded uniformly in time hits `{0, 1}` almost surely. -/
private theorem ae_exists_hit_of_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => X t ω)
    (hmem : ∀ t ω, X t ω ∈ Icc (0 : ℝ) 1) (g : ℕ → ℝ → ℝ) (hgc : ∀ n, Continuous (g n))
    (hg0 : ∀ n, ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ g n y) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ a ∈ Ioo (0 : ℝ) (1 / 2), ∃ n, ∀ y ∈ Icc a (1 - a), ε ≤ g n y) {C : ℝ}
    (hint : ∀ n (t : ℝ≥0),
      Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), g n (X (Real.toNNReal s) ω)) μ)
    (hbound : ∀ n (t : ℝ≥0),
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ), g n (X (Real.toNNReal s) ω)) ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, ∃ t, X t ω = 0 ∨ X t ω = 1 := by
  set Bad := {ω | ¬∃ t, X t ω = 0 ∨ X t ω = 1} with hBad
  have hT : ∀ T : ℕ, μ Bad ≤ ENNReal.ofReal (C / (ε * (T + 1))) := by
    intro T
    set T' : ℝ≥0 := ((T + 1 : ℕ) : ℝ≥0) with hT'
    have hT'r : (T' : ℝ) = T + 1 := by simp [hT']
    have hT'pos : (0 : ℝ) < T' := by rw [hT'r]; positivity
    set E : ℕ → Set Ω := fun m => {ω | ∀ s : ℝ≥0, s ≤ T' →
      X s ω ∈ Icc (1 / ((m : ℝ) + 3)) (1 - 1 / ((m : ℝ) + 3))} with hEdef
    have hEmono : Monotone E := by
      intro m m' hmm' ω hω s hs
      have h1 : 1 / ((m' : ℝ) + 3) ≤ 1 / ((m : ℝ) + 3) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : m + 3 ≤ m' + 3))
      exact ⟨h1.trans (hω s hs).1, (hω s hs).2.trans (by linarith)⟩
    have hsub : Bad ⊆ ⋃ m, E m := by
      intro ω hω
      simp only [hBad, mem_ofPred_eq, not_exists, not_or] at hω
      have hK : IsCompact (Icc (0 : ℝ≥0) T') := isCompact_Icc
      have hne : (Icc (0 : ℝ≥0) T').Nonempty := ⟨0, le_rfl, zero_le⟩
      obtain ⟨s₀, -, hs₀⟩ := hK.exists_isMinOn hne (hc ω).continuousOn
      obtain ⟨s₁, -, hs₁⟩ := hK.exists_isMaxOn hne (hc ω).continuousOn
      have hlo : 0 < X s₀ ω := lt_of_le_of_ne (hmem s₀ ω).1 (fun h => (hω s₀).1 h.symm)
      have hhi : X s₁ ω < 1 := lt_of_le_of_ne (hmem s₁ ω).2 (hω s₁).2
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min hlo (sub_pos.2 hhi))
      have hm3 : 1 / ((m : ℝ) + 3) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      refine mem_iUnion.2 ⟨m, fun s hs => ⟨?_, ?_⟩⟩
      · exact (hm3.trans (hm.le.trans (min_le_left _ _))).trans (hs₀ ⟨zero_le, hs⟩)
      · have := hs₁ (show s ∈ Icc (0 : ℝ≥0) T' from ⟨zero_le, hs⟩)
        have := hm3.trans (hm.le.trans (min_le_right _ _))
        simp only [mem_ofPred_eq] at *
        linarith
    have hEm : ∀ m, μ (E m) ≤ ENNReal.ofReal (C / (ε * (T + 1))) := by
      intro m
      have ha : 1 / ((m : ℝ) + 3) ∈ Ioo (0 : ℝ) (1 / 2) :=
        ⟨by positivity, one_div_lt_one_div_of_lt (by norm_num)
          (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])⟩
      obtain ⟨n, hn⟩ := hg _ ha
      set F : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..(T' : ℝ), g n (X (Real.toNNReal s) ω)
      have hFc : ∀ ω, Continuous fun s : ℝ => g n (X (Real.toNNReal s) ω) := fun ω =>
        (hgc n).comp ((hc ω).comp continuous_real_toNNReal)
      have hsubF : E m ⊆ {ω | ε * T' ≤ F ω} := by
        intro ω hω
        have := intervalIntegral.integral_mono_on (μ := volume) hT'pos.le intervalIntegrable_const
          ((hFc ω).intervalIntegrable _ _) (fun s hs => hn _ (hω _ (by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
            exact hs.2)))
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
        simp only [mem_ofPred_eq, F]
        linarith
      have hF0 : 0 ≤ᵐ[μ] F := ae_of_all _ fun ω =>
        intervalIntegral.integral_nonneg hT'pos.le fun s _ => hg0 n _ (hmem _ ω)
      have hmk := mul_meas_ge_le_integral_of_nonneg hF0 (hint n T') (ε * T')
      have hb := hbound n T'
      have hreal : μ.real {ω | ε * T' ≤ F ω} ≤ C / (ε * (T + 1)) := by
        rw [le_div_iff₀ (by positivity), mul_comm, ← hT'r]
        exact hmk.trans hb
      calc μ (E m) ≤ μ {ω | ε * T' ≤ F ω} := measure_mono hsubF
        _ = ENNReal.ofReal (μ.real {ω | ε * T' ≤ F ω}) := (ofReal_measureReal).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    calc μ Bad ≤ μ (⋃ m, E m) := measure_mono hsub
      _ = ⨆ m, μ (E m) := hEmono.measure_iUnion
      _ ≤ _ := iSup_le hEm
  have hlim : Tendsto (fun T : ℕ => ENNReal.ofReal (C / (ε * (T + 1)))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop ?_)
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hε
  rw [ae_iff]
  exact le_antisymm (ge_of_tendsto' hlim hT) bot_le

/-- Along a continuous `[0, 1]`-valued path that is in `(0, 1)` before `τ` and at `0` or `1`
from `τ` on, `∫₀ᵗ occRate n (Y s) ds → min t τ`. -/
private theorem tendsto_integral_occRate {Y : ℝ≥0 → ℝ} (hY : Continuous Y)
    (hmem : ∀ s, Y s ∈ Icc (0 : ℝ) 1) {τ : ℝ≥0}
    (hbefore : ∀ s < τ, Y s ∈ Ioo (0 : ℝ) 1) (hafter : ∀ s, τ ≤ s → Y s = 0 ∨ Y s = 1)
    (t : ℝ≥0) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..(t : ℝ), occRate n (Y (Real.toNNReal s))) atTop
      (𝓝 (min (t : ℝ) τ)) := by
  have hYc : Continuous fun s : ℝ => Y (Real.toNNReal s) := hY.comp continuous_real_toNNReal
  have hcont : ∀ n, Continuous fun s : ℝ => occRate n (Y (Real.toNNReal s)) := fun n => by
    unfold occRate
    fun_prop
  set m : ℝ := min (t : ℝ) τ with hmdef
  have hm0 : 0 ≤ m := le_min t.2 τ.2
  have hlim1 : Tendsto (fun n => ∫ s in (0 : ℝ)..m, occRate n (Y (Real.toNNReal s))) atTop
      (𝓝 m) := by
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ m := by
      rw [ae_iff]
      simp
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := 0) (b := m) (l := atTop) (F := fun n s => occRate n (Y (Real.toNNReal s)))
      (f := fun _ => (1 : ℝ)) (fun _ => 1)
      (Eventually.of_forall fun n => (hcont n).aestronglyMeasurable)
      (Eventually.of_forall fun n => ae_of_all _ fun s _ => by
        have := occRate_mem_Icc n (hmem (Real.toNNReal s))
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [this.1, this.2])
      intervalIntegrable_const ?_
    · simpa using this
    · filter_upwards [hne] with s hs hsI
      rw [uIoc_of_le hm0] at hsI
      have hlt : Real.toNNReal s < τ := by
        rw [Real.toNNReal_lt_iff_lt_coe hsI.1.le]
        exact lt_of_lt_of_le (lt_of_le_of_ne hsI.2 hs) (min_le_right _ _)
      exact tendsto_occRate (hbefore _ hlt)
  have hzero : ∀ n, ∫ s in m..(t : ℝ), occRate n (Y (Real.toNNReal s)) = 0 := by
    intro n
    rcases le_total (t : ℝ) τ with h | h
    · simp [hmdef, min_eq_left h]
    · have hm : m = τ := min_eq_right h
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      intro s hs
      rw [uIcc_of_le (by rw [hm]; exact h)] at hs
      have hτs : τ ≤ Real.toNNReal s := by
        rw [Real.le_toNNReal_iff_coe_le (hm0.trans hs.1)]
        exact hm ▸ hs.1
      rcases hafter _ hτs with h0 | h1
      · simp [h0, occRate_zero]
      · simp [h1, occRate_one]
  have hsplit : ∀ n, ∫ s in (0 : ℝ)..(t : ℝ), occRate n (Y (Real.toNNReal s)) =
      (∫ s in (0 : ℝ)..m, occRate n (Y (Real.toNNReal s))) +
        ∫ s in m..(t : ℝ), occRate n (Y (Real.toNNReal s)) := fun n =>
    (intervalIntegral.integral_add_adjacent_intervals ((hcont n).intervalIntegrable _ _)
      ((hcont n).intervalIntegrable _ _)).symm
  simpa [hsplit, hzero] using hlim1

/-! ### Consequences of the martingale problem -/

/-- The generator of a `C²` function is continuous. -/
private theorem continuous_generator (σ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (generator σ f) := by
  have h1 : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv (n := 1)).1 hf |>.2.2
  have hd : Continuous (deriv f) := h1.continuous
  have hdd : Continuous (deriv (deriv f)) := h1.continuous_deriv le_rfl
  unfold generator
  fun_prop

namespace IsWrightFisherSolution

variable {σ : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

private theorem measurable (hX : IsWrightFisherSolution σ ℱ μ X) (t : ℝ≥0) :
    Measurable (X t) :=
  ((hX.2.2.1 t).mono (ℱ.le t)).measurable

private theorem integrable_comp [IsFiniteMeasure μ] (hX : IsWrightFisherSolution σ ℱ μ X)
    {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ≥0) : Integrable (fun ω => f (X t ω)) μ := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc 0 1))
  exact Integrable.of_bound (hf.measurable.comp (hX.measurable t)).aestronglyMeasurable B
    (ae_of_all _ fun ω => hB _ (hX.1 t ω))

/-- **Dynkin's formula at a fixed time.** -/
private theorem integral_generator [IsFiniteMeasure μ] (hX : IsWrightFisherSolution σ ℱ μ X)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ≥0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), generator σ f (X (Real.toNNReal s) ω)) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ), generator σ f (X (Real.toNNReal s) ω)) ∂μ =
        ∫ ω, f (X t ω) ∂μ - ∫ ω, f (X 0 ω) ∂μ := by
  have hM := hX.2.2.2 f hf
  have h0 := hM.setIntegral_eq (zero_le (a := t)) MeasurableSet.univ
  simp only [setIntegral_univ, NNReal.coe_zero, intervalIntegral.integral_same, sub_self,
    integral_zero] at h0
  have hft := hX.integrable_comp hf.continuous t
  have hf0 := hX.integrable_comp hf.continuous 0
  have heq : (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), generator σ f (X (Real.toNNReal s) ω)) =
      fun ω => (f (X t ω) - f (X 0 ω)) - (f (X t ω) - f (X 0 ω) -
        ∫ s in (0 : ℝ)..(t : ℝ), generator σ f (X (Real.toNNReal s) ω)) := by
    funext ω; ring
  have hd : Integrable (fun ω => f (X t ω) - f (X 0 ω)) μ := hft.sub hf0
  have hMt : Integrable (fun ω => f (X t ω) - f (X 0 ω) -
      ∫ s in (0 : ℝ)..(t : ℝ), generator σ f (X (Real.toNNReal s) ω)) μ := hM.integrable t
  rw [heq]
  refine ⟨hd.sub hMt, ?_⟩
  rw [integral_sub hd hMt, integral_sub hft hf0, ← h0, sub_zero]

/-- `u (X t)` is a martingale for Kimura's formula `u`. -/
private theorem martingale_kimuraFixation [IsFiniteMeasure μ]
    (hX : IsWrightFisherSolution σ ℱ μ X) :
    Martingale (fun t ω => kimuraFixation σ (X t ω)) ℱ μ := by
  have hM := hX.2.2.2 _ (contDiff_kimuraFixation σ)
  simp only [Diffusion.generator_kimuraFixation, intervalIntegral.integral_zero,
    sub_zero] at hM
  have hm0 : StronglyMeasurable[ℱ ⊥] fun ω => kimuraFixation σ (X 0 ω) :=
    (continuous_kimuraFixation σ).comp_stronglyMeasurable (hX.2.2.1 0)
  have hc := martingale_const_fun ℱ μ hm0 (hX.integrable_comp (continuous_kimuraFixation σ) 0)
  refine (hM.add hc).congr ?_ (fun t => ae_of_all _ fun ω => ?_)
  · exact fun t => (continuous_kimuraFixation σ).comp_stronglyMeasurable (hX.2.2.1 t)
  · simp

private theorem ae_stay_zero [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution σ ℱ μ X) :
    ∀ᵐ ω ∂μ, ∀ s t, s ≤ t → X s ω = 0 → X t ω = 0 := by
  filter_upwards [ae_stay_zero_of_martingale hX.martingale_kimuraFixation
    (fun t ω => (Diffusion.kimuraFixation_mem_Icc σ (hX.1 t ω)).1)
    (fun ω => (continuous_kimuraFixation σ).comp (hX.2.1 ω))] with ω h s t hst hs
  have := h s t hst (by simp [hs])
  exact (strictMono_kimuraFixation σ).injective (by simpa using this)

private theorem ae_stay_one [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution σ ℱ μ X) :
    ∀ᵐ ω ∂μ, ∀ s t, s ≤ t → X s ω = 1 → X t ω = 1 := by
  filter_upwards [ae_stay_zero_of_martingale
    ((martingale_const ℱ μ (1 : ℝ)).sub hX.martingale_kimuraFixation)
    (fun t ω => sub_nonneg.2 (Diffusion.kimuraFixation_mem_Icc σ (hX.1 t ω)).2)
    (fun ω => continuous_const.sub ((continuous_kimuraFixation σ).comp (hX.2.1 ω)))]
    with ω h s t hst hs
  have := h s t hst (by simp [hs])
  exact (strictMono_kimuraFixation σ).injective (by simp at this ⊢; linarith)

private theorem ae_exists_hit [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution σ ℱ μ X) :
    ∀ᵐ ω ∂μ, ∃ t, X t ω = 0 ∨ X t ω = 1 := by
  obtain ⟨ε, hε, hg⟩ := exists_le_neg_generator_occPoly_comp σ
  refine ae_exists_hit_of_bound hX.2.1 hX.1
    (fun n y => -generator σ (fun z => occPoly n (kimuraFixation σ z)) y)
    (fun n => (continuous_generator σ (contDiff_occPoly_comp σ n)).neg)
    (fun n y hy => neg_nonneg.2 (generator_occPoly_comp_nonpos σ n hy)) hε hg (C := 4)
    (fun n t => ?_) (fun n t => ?_)
  · refine ((hX.integral_generator (contDiff_occPoly_comp σ n) t).1.neg).congr
      (ae_of_all _ fun ω => ?_)
    simp [intervalIntegral.integral_neg]
  · simp only [intervalIntegral.integral_neg, integral_neg,
      (hX.integral_generator (contDiff_occPoly_comp σ n) t).2]
    have h1 : ∫ ω, (-4 : ℝ) ∂μ ≤ ∫ ω, occPoly n (kimuraFixation σ (X t ω)) ∂μ :=
      integral_mono (integrable_const _)
        (hX.integrable_comp ((contDiff_occPoly_comp σ n).continuous) t)
        fun ω => (occPoly_mem_Icc n (Diffusion.kimuraFixation_mem_Icc σ (hX.1 t ω))).1
    have h2 : ∫ ω, occPoly n (kimuraFixation σ (X 0 ω)) ∂μ ≤ 0 :=
      integral_nonpos fun ω => (occPoly_mem_Icc n (Diffusion.kimuraFixation_mem_Icc σ
        (hX.1 0 ω))).2
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
    linarith

end IsWrightFisherSolution

/-! ### Main results -/

/-- **Absorption in finite time.** A solution of the Wright–Fisher martingale problem is
almost surely absorbed: from some time on it is constantly `0` or constantly `1`.

Source: Ethier & Kurtz (1986), ch. 10; Karlin & Taylor (1981), ch. 15. Proves the deferred
entry `ae_exists_absorbed`. -/
theorem ae_exists_absorbed {σ : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution σ ℱ μ X) :
    ∀ᵐ ω ∂μ, ∃ t₀ : ℝ≥0, (∀ t ≥ t₀, X t ω = 0) ∨ (∀ t ≥ t₀, X t ω = 1) := by
  filter_upwards [hX.ae_exists_hit, hX.ae_stay_zero, hX.ae_stay_one] with ω ⟨t₁, h₁⟩ h0 h1
  refine ⟨t₁, ?_⟩
  rcases h₁ with h | h
  · exact Or.inl fun t ht => h0 t₁ t ht h
  · exact Or.inr fun t ht => h1 t₁ t ht h

/-- **Kimura's fixation probability, process form.** For a solution of the Wright–Fisher
martingale problem with scaled selection coefficient `σ = 2Ns` started at frequency `x`, the
probability that the allele is eventually fixed is `(1 - e^{-2σx}) / (1 - e^{-2σ})` (`x` when
`σ = 0`).

Source: Kimura (1962); Ewens (2004), ch. 4. Proves the deferred entry
`measureReal_fixation`. -/
theorem measureReal_fixation {σ x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution σ ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 1} = kimuraFixation σ x := by
  have hU := hX.martingale_kimuraFixation
  have hE : ∀ t : ℝ≥0, ∫ ω, kimuraFixation σ (X t ω) ∂μ = kimuraFixation σ x := by
    intro t
    have h := hU.setIntegral_eq (zero_le (a := t)) MeasurableSet.univ
    simp only [setIntegral_univ] at h
    rw [← h, integral_congr_ae (g := fun _ => kimuraFixation σ x)
      (hX0.mono fun ω hω => by simp only [hω])]
    simp
  set S' : Set Ω := ⋃ N : ℕ, ⋂ k ≥ N, {ω | X (k : ℝ≥0) ω = 1} with hS'def
  have hS' : MeasurableSet S' :=
    MeasurableSet.iUnion fun N => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun (hX.measurable _) measurable_const
  have hgood := ae_exists_absorbed hX
  have hset : ∀ᵐ ω ∂μ, (ω ∈ {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 1} ↔ ω ∈ S') := by
    filter_upwards [hgood] with ω ⟨t₀, h⟩
    simp only [mem_ofPred_eq, hS'def, mem_iUnion, mem_iInter]
    constructor
    · rintro ⟨t₁, ht₁⟩
      refine ⟨⌈(t₁ : ℝ)⌉₊, fun k hk => ht₁ _ ?_⟩
      change t₁ ≤ (k : ℝ≥0)
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
    · rintro ⟨N, hN⟩
      rcases h with h | h
      · exfalso
        set k := max N ⌈(t₀ : ℝ)⌉₊
        have h1 := hN k (le_max_left _ _)
        have h2 := h (k : ℝ≥0) (by
          change t₀ ≤ (k : ℝ≥0)
          rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
          exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _))
        rw [h2] at h1
        exact zero_ne_one h1
      · exact ⟨t₀, h⟩
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => kimuraFixation σ (X (n : ℝ≥0) ω)) atTop
      (𝓝 (S'.indicator 1 ω)) := by
    filter_upwards [hgood, hset] with ω ⟨t₀, h⟩ hiff
    have hev : ∀ᶠ n : ℕ in atTop, t₀ ≤ (n : ℝ≥0) := by
      filter_upwards [eventually_ge_atTop ⌈(t₀ : ℝ)⌉₊] with n hn
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rcases h with h | h
    · have hn : ω ∉ S' := fun hω => by
        obtain ⟨t₁, ht₁⟩ := hiff.2 hω
        have := ht₁ (max t₀ t₁) (le_max_right _ _)
        rw [h _ (le_max_left _ _)] at this
        exact zero_ne_one this
      rw [indicator_of_notMem hn]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      simp [h _ hn]
    · rw [indicator_of_mem (hiff.1 ⟨t₀, h⟩)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      simp [h _ hn]
  have hdct := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => ((continuous_kimuraFixation σ).measurable.comp
      (hX.measurable _)).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ fun ω => by
      have := Diffusion.kimuraFixation_mem_Icc σ (hX.1 (n : ℝ≥0) ω)
      simp only [Function.comp_apply, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [this.1, this.2]) hlim
  rw [show (fun n : ℕ => ∫ ω, (kimuraFixation σ ∘ X (n : ℝ≥0)) ω ∂μ) =
      fun _ => kimuraFixation σ x from funext fun n => hE n] at hdct
  rw [measureReal_congr (eventuallyEqSet_iff.2 hset), ← integral_indicator_one hS']
  exact tendsto_nhds_unique hdct tendsto_const_nhds

/-- **Kimura–Ohta mean absorption time, process form.** For a solution of the neutral
Wright–Fisher martingale problem started at frequency `x`, the expected time to loss or
fixation, in units of `2N` generations, is `-2 (x log x + (1 - x) log (1 - x))`.

Source: Kimura & Ohta (1969); Ewens (2004), ch. 4. Proves the deferred entry
`integral_absorptionTime`. -/
theorem integral_absorptionTime {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    Integrable (fun ω => (absorptionTime X ω : ℝ)) μ ∧
      ∫ ω, (absorptionTime X ω : ℝ) ∂μ = meanAbsorptionTime x := by
  set T := meanAbsorptionTime
  have hx : x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨ω, hω⟩ := hX0.exists
    exact hω ▸ hX.1 0 ω
  -- path facts
  have hbefore : ∀ ω (s : ℝ≥0), s < absorptionTime X ω → X s ω ∈ Ioo (0 : ℝ) 1 := by
    intro ω s hs
    have hm := hX.1 s ω
    have key : ¬ (X s ω = 0 ∨ X s ω = 1) := fun h =>
      not_le.2 hs (csInf_le (OrderBot.bddBelow {t | X t ω = 0 ∨ X t ω = 1}) h)
    exact ⟨lt_of_le_of_ne hm.1 fun h => key (Or.inl h.symm),
      lt_of_le_of_ne hm.2 fun h => key (Or.inr h)⟩
  have hafter : ∀ᵐ ω ∂μ, ∀ s : ℝ≥0, absorptionTime X ω ≤ s → X s ω = 0 ∨ X s ω = 1 := by
    filter_upwards [hX.ae_exists_hit, hX.ae_stay_zero, hX.ae_stay_one] with ω ⟨t₁, h₁⟩ h0 h1
    have hcl : IsClosed {t | X t ω = 0 ∨ X t ω = 1} :=
      (isClosed_eq (hX.2.1 ω) continuous_const).union (isClosed_eq (hX.2.1 ω) continuous_const)
    have hmem := hcl.csInf_mem ⟨t₁, h₁⟩ (OrderBot.bddBelow _)
    intro s hs
    rcases hmem with h | h
    · exact Or.inl (h0 _ s hs h)
    · exact Or.inr (h1 _ s hs h)
  have habs := ae_exists_absorbed hX
  -- Dynkin's formula for the neutral occupation polynomials
  have hcd : ∀ n, ContDiff ℝ 2 (occPoly n) := fun n => by
    simpa using contDiff_occPoly_comp 0 n
  have hE0 : ∀ {g : ℝ → ℝ}, ∫ ω, g (X 0 ω) ∂μ = g x := fun {g} => by
    rw [integral_congr_ae (g := fun _ => g x) (hX0.mono fun ω hω => by simp only [hω])]
    simp
  have hD : ∀ n (t : ℝ≥0),
      Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), occRate n (X (Real.toNNReal s) ω)) μ ∧
        ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ), occRate n (X (Real.toNNReal s) ω)) ∂μ =
          occPoly n x - ∫ ω, occPoly n (X t ω) ∂μ := by
    intro n t
    obtain ⟨h1, h2⟩ := hX.integral_generator (hcd n) t
    simp only [generator_occPoly, intervalIntegral.integral_neg, integral_neg] at h1 h2
    rw [hE0] at h2
    exact ⟨by simpa using h1.neg, by linarith⟩
  have hocc : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, Tendsto
      (fun n => ∫ s in (0 : ℝ)..(t : ℝ), occRate n (X (Real.toNNReal s) ω)) atTop
      (𝓝 (min (t : ℝ) (absorptionTime X ω))) := by
    filter_upwards [hafter] with ω hω t
    exact tendsto_integral_occRate (hX.2.1 ω) (fun s => hX.1 s ω) (hbefore ω) hω t
  -- bounds on `T`
  have hTlim : ∀ y ∈ Icc (0 : ℝ) 1, Tendsto (fun n => occPoly n y - occPoly n 0) atTop
      (𝓝 (T y)) := fun y hy => tendsto_occPoly_sub hy
  have hdiff : ∀ n, ∀ y ∈ Icc (0 : ℝ) 1, |occPoly n y - occPoly n 0| ≤ 4 := by
    intro n y hy
    have h1 := occPoly_mem_Icc n hy
    have h2 := occPoly_mem_Icc n (left_mem_Icc.2 zero_le_one)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hTb : ∀ y ∈ Icc (0 : ℝ) 1, |T y| ≤ 4 := fun y hy =>
    le_of_tendsto' ((hTlim y hy).abs) fun n => hdiff n y hy
  have hTc : Continuous T := by
    change Continuous fun y => -2 * (y * Real.log y + (1 - y) * Real.log (1 - y))
    exact continuous_const.mul (Real.continuous_mul_log.add
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)))
  have hTX : ∀ t : ℝ≥0, Integrable (fun ω => T (X t ω)) μ := fun t =>
    hX.integrable_comp hTc t
  -- `E[min(t, τ)] = T(x) - E[T(X t)]`
  have hstar : ∀ t : ℝ≥0, Tendsto (fun n => ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ),
      occRate n (X (Real.toNNReal s) ω)) ∂μ) atTop
      (𝓝 (∫ ω, min (t : ℝ) (absorptionTime X ω) ∂μ)) := by
    intro t
    refine tendsto_integral_of_dominated_convergence (fun _ => (t : ℝ))
      (fun n => (hD n t).1.aestronglyMeasurable) (integrable_const _) (fun n => ae_of_all _
        fun ω => ?_) (by filter_upwards [hocc] with ω hω using hω t)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) fun s _ => ?_).trans
      (by simp)
    have := occRate_mem_Icc n (hX.1 (Real.toNNReal s) ω)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hstar' : ∀ t : ℝ≥0, Tendsto (fun n => occPoly n x - ∫ ω, occPoly n (X t ω) ∂μ) atTop
      (𝓝 (T x - ∫ ω, T (X t ω) ∂μ)) := by
    intro t
    have hrw : ∀ n, occPoly n x - ∫ ω, occPoly n (X t ω) ∂μ =
        (occPoly n x - occPoly n 0) - ∫ ω, (occPoly n (X t ω) - occPoly n 0) ∂μ := by
      intro n
      rw [integral_sub (hX.integrable_comp (hcd n).continuous t) (integrable_const _)]
      simp
    simp only [hrw]
    refine (hTlim x hx).sub (tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ))
      (fun n => (((hcd n).continuous.sub continuous_const).measurable.comp
        (hX.measurable t)).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun ω => hdiff n _ (hX.1 t ω))
      (ae_of_all _ fun ω => hTlim _ (hX.1 t ω)))
  have hmin : ∀ t : ℝ≥0, ∫ ω, min (t : ℝ) (absorptionTime X ω) ∂μ =
      T x - ∫ ω, T (X t ω) ∂μ := fun t =>
    tendsto_nhds_unique (hstar t) ((hstar' t).congr fun n => ((hD n t).2).symm)
  -- measurability
  have hmk : ∀ k : ℕ, AEStronglyMeasurable (fun ω => min (k : ℝ) (absorptionTime X ω)) μ :=
    fun k => aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hD n (k : ℝ≥0)).1.aestronglyMeasurable)
      (by filter_upwards [hocc] with ω hω using by simpa using hω (k : ℝ≥0))
  have hτlim : ∀ ω, Tendsto (fun k : ℕ => min (k : ℝ) (absorptionTime X ω)) atTop
      (𝓝 (absorptionTime X ω : ℝ)) := by
    intro ω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈(absorptionTime X ω : ℝ)⌉₊] with k hk
    exact (min_eq_right ((Nat.le_ceil _).trans (by exact_mod_cast hk))).symm
  have hτm : AEStronglyMeasurable (fun ω => (absorptionTime X ω : ℝ)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hmk (ae_of_all _ hτlim)
  have hmint : ∀ k : ℕ, Integrable (fun ω => min (k : ℝ) (absorptionTime X ω)) μ := fun k =>
    Integrable.of_bound (hmk k) k (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min k.cast_nonneg (NNReal.coe_nonneg _))]
      exact min_le_left _ _)
  -- integrability of `τ` by Fatou
  have hτint : Integrable (fun ω => (absorptionTime X ω : ℝ)) μ := by
    refine ⟨hτm, ?_⟩
    have hfat := lintegral_liminf_le' (μ := μ) (u := atTop)
      (f := fun k : ℕ => fun ω => ‖min (k : ℝ) (absorptionTime X ω)‖ₑ)
      (fun k => (hmk k).aemeasurable.enorm)
    have heq : ∫⁻ ω, ‖(absorptionTime X ω : ℝ)‖ₑ ∂μ =
        ∫⁻ ω, liminf (fun k : ℕ => ‖min (k : ℝ) (absorptionTime X ω)‖ₑ) atTop ∂μ :=
      lintegral_congr fun ω => ((hτlim ω).enorm.liminf_eq).symm
    have hle : ∀ k : ℕ, ∫⁻ ω, ‖min (k : ℝ) (absorptionTime X ω)‖ₑ ∂μ ≤ ENNReal.ofReal 8 := by
      intro k
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hmint k)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hnn : ∀ ω, 0 ≤ min (k : ℝ) (absorptionTime X ω) := fun ω =>
        le_min k.cast_nonneg (NNReal.coe_nonneg _)
      simp only [Real.norm_eq_abs, abs_of_nonneg (hnn _)]
      have hk := hmin (k : ℝ≥0)
      simp only [NNReal.coe_natCast] at hk
      rw [hk]
      have h1 : |∫ ω, T (X (k : ℝ≥0) ω) ∂μ| ≤ 4 := by
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ ω, |T (X (k : ℝ≥0) ω)| ∂μ ≤ ∫ _ω, (4 : ℝ) ∂μ :=
              integral_mono (hTX _).abs (integrable_const _) fun ω => hTb _ (hX.1 _ ω)
          _ = 4 := by simp
      have h2 := hTb x hx
      rw [abs_le] at h1 h2
      linarith [h1.1, h2.2]
    refine lt_of_le_of_lt (heq ▸ hfat) ?_
    exact lt_of_le_of_lt (liminf_le_of_frequently_le' (Frequently.of_forall hle))
      ENNReal.ofReal_lt_top
  refine ⟨hτint, ?_⟩
  -- monotone convergence and `E[T(X k)] → 0`
  have hmono := integral_tendsto_of_tendsto_of_monotone hmint hτint
    (ae_of_all _ fun ω a b hab => min_le_min_right _ (by exact_mod_cast hab))
    (ae_of_all _ hτlim)
  have hT0 : Tendsto (fun k : ℕ => ∫ ω, T (X (k : ℝ≥0) ω) ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ))
      (fun k => (hTX (k : ℝ≥0)).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hTb _ (hX.1 _ ω)) (f := fun _ => (0 : ℝ)) ?_
    · simpa using this
    filter_upwards [habs] with ω ⟨t₀, h⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈(t₀ : ℝ)⌉₊] with k hk
    have hk' : t₀ ≤ (k : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rcases h with h | h
    · simp [h _ hk', T]
    · simp [h _ hk', T]
  have hlim2 : Tendsto (fun k : ℕ => ∫ ω, min (k : ℝ) (absorptionTime X ω) ∂μ) atTop
      (𝓝 (T x)) := by
    have h := (tendsto_const_nhds (x := T x)).sub hT0
    rw [sub_zero] at h
    refine h.congr fun k => ?_
    have hk := hmin (k : ℝ≥0)
    simp only [NNReal.coe_natCast] at hk
    exact hk.symm
  exact tendsto_nhds_unique hmono hlim2

end MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
