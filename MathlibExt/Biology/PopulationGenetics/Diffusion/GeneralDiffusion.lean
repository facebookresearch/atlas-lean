/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.Sojourn
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Selection duality and general one-dimensional diffusions

This file continues the analytic (ordinary-differential-equation) treatment of diffusion
approximations in population genetics started in `WrightFisher.lean` and `Sojourn.lean`. Time is
in units of `2N` generations. As there, the diffusion processes themselves are **not**
formalized (Mathlib has no stochastic differential equations); every statement is a fact about
generators, boundary-value problems and series.

## Ancestral selection graph duality

For the Wright–Fisher generator with genic selection
`L_σ u = x (1 - x) / 2 · u'' + σ x (1 - x) · u'`, the functions `x ↦ (1 - x) ^ n` (the
probability that `n` sampled genes all carry the unfavoured allele) satisfy

  `L_σ[(1 - x)^n] = C(n, 2) ((1 - x)^(n-1) - (1 - x)^n) + n σ ((1 - x)^(n+1) - (1 - x)^n)`,

which is the generator of the line-counting process of the ancestral selection graph
(coalescence `n → n - 1` at rate `C(n, 2)`, branching `n → n + 1` at rate `n σ`) applied to
`n ↦ (1 - x)^n`. For `σ > 0` this birth–death chain has the stationary law
`π_k = (2σ)^k / k! / (e^{2σ} - 1)` on `k ≥ 1` (a Poisson`(2σ)` law conditioned to be positive),
and its probability generating function at `1 - x` is the loss probability
`1 - kimuraFixation σ x`.

## General one-dimensional diffusions

For drift `b` and infinitesimal variance `a > 0` on `(0, 1)`, with backward generator
`L u = a / 2 · u'' + b · u'`, the scale density is `ψ(y) = exp (-∫₀^y 2 b / a)`, the scale
function is `S(p) = ∫₀^p ψ`, the analytic Dirichlet ratio is `S(p) / S(1)` and the Green's function
of `-L` with Dirichlet conditions at `0` and `1` is

  `G(p, x) = 2 S(min p x) (S(1) - S(max p x)) / (S(1) a(x) ψ(x))`.

`fixationProb` and `greenFunction` are these analytic Dirichlet constructions. They are the
hitting probability / expected sojourn time of the diffusion only when both boundaries are
Feller-accessible (the scale–speed integrals `∫ (S(1) - S) / (ψ a)` and `∫ S / (ψ a)` are finite
near `1` and `0`); `IsRegularDiffusion` does **not** imply accessibility. Counterexample:
`b = 0`, `a x = x² (1 - x)²` satisfies all four fields and gives `S(x) = x`, so
`fixationProb` returns `p`, but both Feller accessibility integrals diverge, so neither
endpoint is hit in finite time.

Genic selection (`b = σ x (1 - x)`, `a = x (1 - x)`) recovers Kimura's formula and the neutral
Green's function of `Sojourn.lean`; Kimura's dominance formula is the case
`b = 2 c x (1 - x) (h + (1 - 2h) x)`.

## Conditional fixation and loss times

Conditioning on fixation is the Doob `h`-transform by the fixation probability `u`, with
sojourn density `G(p, x) u(x) / u(p)`. In the neutral case the conditional mean times are
`t̄₁(p) = -2 (1 - p) log (1 - p) / p` (given fixation) and `t̄₀(p) = -2 p log p / (1 - p)`
(given loss), with `t̄₁(0⁺) = 2`.

## Main results

* `generator_one_sub_pow`: the selection duality at generator level.
* `asgStationary`, `asgStationary_detailed_balance`, `asgStationary_global_balance`,
  `hasSum_asgStationary`, `hasSum_asgStationary_mul_one_sub_pow`.
* `diffusionGenerator`, `scaleDensity`, `scaleFunction`, `fixationProb`, `greenFunction`,
  `IsRegularDiffusion`.
* `diffusionGenerator_fixationProb`, `eq_fixationProb_of_diffusionGenerator_eq_zero`: the
  scale-function ratio is the unique solution of `L u = 0`, `u(0) = 0`, `u(1) = 1`.
* `diffusionGenerator_integral_greenFunction`, `integral_greenFunction_zero_left`,
  `integral_greenFunction_one_left`, `eq_of_diffusionGenerator_eq`: `G` inverts `-L` with
  Dirichlet conditions, and that problem has at most one regular solution.
* `fixationProb_wrightFisher`, `greenFunction_neutral`, `fixationProb_dominance`.
* `conditionalGreen`, `diffusionGenerator_mul_integral_conditionalGreen`: the `h`-transform and
  the backward equation `L (u t̄₁) = -u`.
* `neutralFixationTime`, `neutralLossTime`, `integral_neutralGreen_mul_div`,
  `integral_conditionalGreen_neutral`, `tendsto_neutralFixationTime_zero`,
  `mul_neutralFixationTime_add_mul_neutralLossTime`.

## References

* S. M. Krone and C. Neuhauser, *Ancestral processes with selection*, Theoret. Population Biol.
  51 (1997) 210–237.
* S. Mano, *Duality, ancestral and diffusion processes in models with selection*, Theoret.
  Population Biol. 75 (2009) 164–175.
* M. Kimura, *On the probability of fixation of mutant genes in a population*, Genetics 47
  (1962) 713–719.
* M. Kimura and T. Ohta, *The average number of generations until fixation of a mutant gene in
  a finite population*, Genetics 61 (1969) 763–771.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), Chapter 4.
* S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981),
  Chapter 15.
-/

@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology Nat

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-! ### Ancestral selection graph duality -/

/-- The generator of the line-counting process of the ancestral selection graph with scaled
selection coefficient `σ` (time in units of `2N` generations, the scaling of `generator`):
from `n` lines, branching `n → n + 1` at rate `n σ` and coalescence `n → n - 1` at rate
`C(n, 2)`. -/
noncomputable def asgGenerator (σ : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  n * σ * (f (n + 1) - f n) + (n.choose 2 : ℝ) * (f (n - 1) - f n)

private theorem hasDerivAt_one_sub_pow (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 - y) ^ n) (-(n : ℝ) * (1 - x) ^ (n - 1)) x := by
  convert ((hasDerivAt_id x).const_sub 1).pow n using 1
  · funext y
    rfl
  · simp only [id_eq]
    ring

/-- **Selection duality (Mano 2009)** at generator level, with the line-counting process of the
ancestral selection graph (Krone–Neuhauser 1997) as the dual: the
Wright–Fisher generator with genic selection maps `y ↦ (1 - y) ^ n` to
`C(n, 2) ((1 - x)^(n-1) - (1 - x)^n) + n σ ((1 - x)^(n+1) - (1 - x)^n)`. This identity holds for
every real `σ`; the dual is a Markov chain only for `σ ≥ 0`. -/
theorem generator_one_sub_pow (σ : ℝ) (n : ℕ) (x : ℝ) :
    generator σ (fun y => (1 - y) ^ n) x =
      (n.choose 2 : ℝ) * ((1 - x) ^ (n - 1) - (1 - x) ^ n) +
        n * σ * ((1 - x) ^ (n + 1) - (1 - x) ^ n) := by
  rcases n with _ | (_ | k)
  · simp [generator]
  · simp [generator, deriv_const_sub_id']
    ring
  · have hd : deriv (fun y : ℝ => (1 - y) ^ (k + 2)) =
        fun y => -((k + 2 : ℕ) : ℝ) * (1 - y) ^ (k + 1) := by
      funext y
      convert (hasDerivAt_one_sub_pow (k + 2) y).deriv using 1
      congr 2
    have hdd := (hasDerivAt_one_sub_pow (k + 1) x).const_mul (-((k + 2 : ℕ) : ℝ))
    have hk : k + 1 - 1 = k := by omega
    rw [generator, hd, hdd.deriv, Nat.cast_choose_two]
    simp only [hk, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, pow_succ]
    ring

/-- The selection duality in operator form: `L_σ` applied to `y ↦ (1 - y) ^ n` equals the
ancestral-selection-graph generator applied to `k ↦ (1 - x) ^ k` at `n`. -/
theorem generator_one_sub_pow_eq_asgGenerator (σ : ℝ) (n : ℕ) (x : ℝ) :
    generator σ (fun y => (1 - y) ^ n) x = asgGenerator σ (fun k => (1 - x) ^ k) n := by
  rw [generator_one_sub_pow, asgGenerator]
  ring

/-- The stationary law of the ancestral-selection-graph line-counting process with `σ > 0`:
`π_k = (2σ)^k / k! / (e^{2σ} - 1)` for `k ≥ 1` and `π_0 = 0`, a Poisson`(2σ)` law conditioned
to be positive. For `σ = 0` the formula divides by `0` and every value is the junk value `0`
(there is no stationary law: lines only coalesce). -/
noncomputable def asgStationary (σ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (2 * σ) ^ k / k ! / (exp (2 * σ) - 1)

/-- **Detailed balance** of the ancestral-selection-graph chain:
`π_k · (k σ) = π_{k+1} · C(k + 1, 2)` for every `k` (the flux `k → k + 1` equals the flux
`k + 1 → k`). This is an identity for every real `σ`. -/
theorem asgStationary_detailed_balance (σ : ℝ) (k : ℕ) :
    asgStationary σ k * (k * σ) = asgStationary σ (k + 1) * ((k + 1).choose 2 : ℝ) := by
  cases k with
  | zero => simp [asgStationary]
  | succ k =>
    simp only [asgStationary, Nat.succ_ne_zero, ↓reduceIte]
    rw [Nat.cast_choose_two]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hk2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
    by_cases he : exp (2 * σ) - 1 = 0
    · simp [he]
    · field_simp
      ring

/-- **Global balance** (stationarity `π Q = 0`) of the ancestral-selection-graph chain at
state `k + 1`: the outflow `π_{k+1} ((k + 1) σ + C(k + 1, 2))` equals the inflow
`π_k (k σ) + π_{k+2} C(k + 2, 2)` (for `k = 0` the inflow from the unreachable state `0`
vanishes). -/
theorem asgStationary_global_balance (σ : ℝ) (k : ℕ) :
    asgStationary σ (k + 1) * ((k + 1 : ℕ) * σ + ((k + 1).choose 2 : ℝ)) =
      asgStationary σ k * (k * σ) + asgStationary σ (k + 2) * ((k + 2).choose 2 : ℝ) := by
  rw [mul_add, asgStationary_detailed_balance σ k,
    ← asgStationary_detailed_balance σ (k + 1)]
  ring

/-- For `σ > 0` the stationary weights are nonnegative. -/
theorem asgStationary_nonneg {σ : ℝ} (hσ : 0 < σ) (k : ℕ) : 0 ≤ asgStationary σ k := by
  unfold asgStationary
  split_ifs
  · exact le_rfl
  · apply div_nonneg (div_nonneg (by positivity) (by positivity))
    exact sub_nonneg.mpr (le_of_lt (Real.one_lt_exp_iff.mpr (by positivity)))

/-- The probability generating function of the stationary law: for `σ > 0` and every real `y`,
`∑ₖ π_k y^k = (e^{2σy} - 1) / (e^{2σ} - 1)`. -/
theorem hasSum_asgStationary_mul_pow {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    HasSum (fun k => asgStationary σ k * y ^ k) ((exp (2 * σ * y) - 1) / (exp (2 * σ) - 1)) := by
  have hd : exp (2 * σ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
  have he : HasSum (fun k : ℕ => (2 * σ * y) ^ k / k !) (exp (2 * σ * y)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (2 * σ * y)
  have hz : HasSum (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq 0 1
  convert (he.sub hz).div_const (exp (2 * σ) - 1) using 1
  ext k
  cases k with
  | zero => simp [asgStationary]
  | succ k =>
    simp only [asgStationary, Nat.succ_ne_zero, ↓reduceIte, sub_zero, mul_pow]
    field_simp [hd]

/-- For `σ > 0` the stationary weights sum to `1`. -/
theorem hasSum_asgStationary {σ : ℝ} (hσ : 0 < σ) : HasSum (asgStationary σ) 1 := by
  have hd : exp (2 * σ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
  simpa only [one_pow, mul_one, div_self hd] using
    hasSum_asgStationary_mul_pow hσ 1

/-- The loss probability in Kimura's formula, written with positive exponents: for `σ ≠ 0`,
`1 - kimuraFixation σ x = (e^{2σ(1 - x)} - 1) / (e^{2σ} - 1)`. -/
theorem one_sub_kimuraFixation {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    1 - kimuraFixation σ x = (exp (2 * σ * (1 - x)) - 1) / (exp (2 * σ) - 1) := by
  have h2 : 2 * σ ≠ 0 := mul_ne_zero (by norm_num) hσ
  have hd : exp (2 * σ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (fun h => h2 ((Real.exp_eq_one_iff _).mp h))
  have hn : 1 - exp (-2 * σ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hz := (Real.exp_eq_one_iff _).mp h.symm
    exact hσ (by linarith)
  have he : exp (-2 * σ) = (exp (2 * σ))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hx : exp (2 * σ * (1 - x)) = exp (2 * σ) * exp (-2 * σ * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [kimuraFixation, ite_eq_right hσ, hx, he]
  have hi : 1 - (exp (2 * σ))⁻¹ ≠ 0 := by rwa [← he]
  field_simp [hd, hi, Real.exp_ne_zero]
  ring

/-- **Loss probability from the stationary ancestral selection graph** (Mano 2009): for
`σ > 0`, `∑ₖ π_k (1 - x)^k = 1 - kimuraFixation σ x`, i.e. the loss
probability of the favoured allele at frequency `x` is the probability that all lines of the
stationary ancestral selection graph carry the unfavoured allele. Only the series identity is
formalized; the sampling interpretation is not. -/
theorem hasSum_asgStationary_mul_one_sub_pow {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    HasSum (fun k => asgStationary σ k * (1 - x) ^ k) (1 - kimuraFixation σ x) := by
  rw [one_sub_kimuraFixation (ne_of_gt hσ)]
  exact hasSum_asgStationary_mul_pow hσ (1 - x)

/-! ### General one-dimensional diffusions -/

/-- The backward generator of a one-dimensional diffusion with drift `b` and infinitesimal
variance `a`: `(L u)(x) = a(x) / 2 · u''(x) + b(x) · u'(x)`. -/
noncomputable def diffusionGenerator (b a u : ℝ → ℝ) (x : ℝ) : ℝ :=
  a x / 2 * deriv (deriv u) x + b x * deriv u x

/-- The scale density `ψ(y) = exp (-∫₀^y 2 b(z) / a(z) dz)` of the diffusion with drift `b`
and variance `a` (Karlin–Taylor 1981, Chapter 15). -/
noncomputable def scaleDensity (b a : ℝ → ℝ) (y : ℝ) : ℝ :=
  exp (-∫ z in (0 : ℝ)..y, 2 * b z / a z)

/-- The scale function `S(p) = ∫₀^p ψ(y) dy`, normalized by `S(0) = 0`. -/
noncomputable def scaleFunction (b a : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..p, scaleDensity b a y

/-- The analytic Dirichlet ratio `S(p) / S(1)` for drift `b` and variance `a` (Kimura 1962;
Ewens 2004, Chapter 4). This is the solution of the backward boundary-value problem
`L u = 0`, `u(0) = 0`, `u(1) = 1` (see `eq_fixationProb_of_diffusionGenerator_eq_zero`).
It is the hitting probability `P_p(hit 1 before 0)` only when both boundaries are
Feller-accessible; that is not implied by `IsRegularDiffusion` (see the module docstring for
the `a x = x² (1 - x)²` counterexample). -/
noncomputable def fixationProb (b a : ℝ → ℝ) (p : ℝ) : ℝ :=
  scaleFunction b a p / scaleFunction b a 1

/-- The Green's function (analytic Green kernel) of `-L` with Dirichlet conditions at `0` and `1`
(Ewens 2004, Chapter 4; Karlin–Taylor 1981, Chapter 15):
`G(p, x) = 2 S(min p x) (S(1) - S(max p x)) / (S(1) a(x) ψ(x))`. In the diffusion reading (not
formalized, and requiring Feller-accessible boundaries), `G(p, x) dx` is the expected time
spent in `(x, x + dx)` before absorption. -/
noncomputable def greenFunction (b a : ℝ → ℝ) (p x : ℝ) : ℝ :=
  2 * scaleFunction b a (min p x) * (scaleFunction b a 1 - scaleFunction b a (max p x)) /
    (scaleFunction b a 1 * a x * scaleDensity b a x)

/-- Regularity hypotheses for a diffusion on `(0, 1)` with drift `b` and variance `a`: `a` is
positive and continuous on `(0, 1)`, `b / a` is continuous on `(0, 1)` and integrable on
`[0, 1]` (so the scale function is finite up to both boundaries). The values of `b` and `a` at
`0` and `1` are irrelevant. These are standing hypotheses for this file, not Feller's
classification of regular boundaries: they do **not** imply that either endpoint is
accessible (finite scale–speed integrals), so the hitting-probability reading of
`fixationProb` needs that extra hypothesis. -/
structure IsRegularDiffusion (b a : ℝ → ℝ) : Prop where
  /-- The variance is positive inside the interval. -/
  pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x
  /-- The variance is continuous inside the interval. -/
  continuousOn : ContinuousOn a (Ioo 0 1)
  /-- The drift-to-variance ratio is continuous inside the interval. -/
  continuousOn_div : ContinuousOn (fun x => b x / a x) (Ioo 0 1)
  /-- The drift-to-variance ratio is integrable on `[0, 1]`. -/
  intervalIntegrable_div : IntervalIntegrable (fun x => b x / a x) volume 0 1

/-- The scale density is positive. -/
theorem scaleDensity_pos (b a : ℝ → ℝ) (y : ℝ) : 0 < scaleDensity b a y :=
  exp_pos _

/-- The scale function vanishes at `0`. -/
@[simp]
theorem scaleFunction_zero (b a : ℝ → ℝ) : scaleFunction b a 0 = 0 := by
  simp [scaleFunction]

/-- A function continuous on `[a, b]` with zero derivative on `(a, b)` is constant on `[a, b]`. -/
private theorem eq_left_of_hasDerivAt_zero' {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · rfl
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hax (hf.mono (Icc_subset_Icc_right hx.2))
    fun y hy => (hd y ⟨hy.1, hy.2.trans_le hx.2⟩).differentiableAt.differentiableWithinAt
  rw [(hd c ⟨hc.1, hc.2.trans_le hx.2⟩).deriv, eq_comm, div_eq_zero_iff] at hcd
  rcases hcd with h | h <;> linarith

/-- A function with zero derivative on `(0, 1)` is constant there. -/
private theorem eq_half_of_hasDerivAt_zero {f : ℝ → ℝ}
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f 0 x) : ∀ x ∈ Ioo (0 : ℝ) 1, f x = f (1 / 2) := by
  intro x hx
  have hsub : Icc (min x (1 / 2)) (max x (1 / 2)) ⊆ Ioo (0 : ℝ) 1 := fun y hy =>
    ⟨lt_of_lt_of_le (lt_min hx.1 (by norm_num)) hy.1,
      lt_of_le_of_lt hy.2 (max_lt hx.2 (by norm_num))⟩
  have hc : ContinuousOn f (Icc (min x (1 / 2)) (max x (1 / 2))) := fun y hy =>
    (hd y (hsub hy)).continuousAt.continuousWithinAt
  have hd' : ∀ y ∈ Ioo (min x (1 / 2)) (max x (1 / 2)), HasDerivAt f 0 y := fun y hy =>
    hd y (hsub (Ioo_subset_Icc_self hy))
  rw [eq_left_of_hasDerivAt_zero' hc hd' x ⟨min_le_left _ _, le_max_left _ _⟩,
    eq_left_of_hasDerivAt_zero' hc hd' (1 / 2) ⟨min_le_right _ _, le_max_right _ _⟩]

/-- Interval integrability on `[0, 1]` only depends on the values on `(0, 1)`. -/
private theorem intervalIntegrable_of_eqOn_Ioo {f g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1) (h : EqOn f g (Ioo 0 1)) :
    IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hg ⊢
  exact hg.congr_fun h.symm measurableSet_Ioo

/-- Integrals over `[0, y] ⊆ [0, 1]` only depend on the values on `(0, 1)`. -/
private theorem integral_congr_Ioo {f g : ℝ → ℝ} {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (h : EqOn f g (Ioo 0 1)) : ∫ x in (0 : ℝ)..y, f x = ∫ x in (0 : ℝ)..y, g x := by
  rw [intervalIntegral.integral_of_le hy.1, intervalIntegral.integral_of_le hy.1,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo (h.mono (Ioo_subset_Ioo_right hy.2))

/-- The generator at `x` only depends on `u` near `x`. -/
private theorem diffusionGenerator_congr {b a u v : ℝ → ℝ} {x : ℝ} (h : u =ᶠ[𝓝 x] v) :
    diffusionGenerator b a u x = diffusionGenerator b a v x := by
  simp only [diffusionGenerator, h.deriv.deriv_eq, h.deriv_eq]

namespace IsRegularDiffusion

variable {b a : ℝ → ℝ}

private theorem intervalIntegrable_two_mul_div (h : IsRegularDiffusion b a) :
    IntervalIntegrable (fun z => 2 * b z / a z) volume 0 1 := by
  simpa only [mul_div_assoc] using h.intervalIntegrable_div.const_mul 2

private theorem continuousOn_two_mul_div (h : IsRegularDiffusion b a) :
    ContinuousOn (fun z => 2 * b z / a z) (Ioo 0 1) := by
  have : ContinuousOn (fun z => 2 * (b z / a z)) (Ioo 0 1) :=
    continuousOn_const.mul h.continuousOn_div
  simpa only [mul_div_assoc] using this

/-- The scale density is continuous on `[0, 1]`. -/
theorem continuousOn_scaleDensity (h : IsRegularDiffusion b a) :
    ContinuousOn (scaleDensity b a) (Icc 0 1) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' h.intervalIntegrable_two_mul_div
    (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
  rw [uIcc_of_le zero_le_one] at hc
  exact hc.neg.rexp

/-- `ψ' = -(2 b / a) ψ` inside the interval. -/
theorem hasDerivAt_scaleDensity (h : IsRegularDiffusion b a) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (scaleDensity b a) (-(2 * b x / a x) * scaleDensity b a x) x := by
  have hI : HasDerivAt (fun y => ∫ z in (0 : ℝ)..y, 2 * b z / a z) (2 * b x / a x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (h.intervalIntegrable_two_mul_div.mono_set (by
        rw [uIcc_of_le hx.1.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc_right hx.2.le))
      (h.continuousOn_two_mul_div.stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (h.continuousOn_two_mul_div.continuousAt (Ioo_mem_nhds hx.1 hx.2))
  convert hI.neg.exp using 1 <;> first | rfl | (rw [mul_comm]; rfl)

/-- `S' = ψ` inside the interval. -/
theorem hasDerivAt_scaleFunction (h : IsRegularDiffusion b a) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt (scaleFunction b a) (scaleDensity b a x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((h.continuousOn_scaleDensity.mono (Icc_subset_Icc_right hx.2.le)).intervalIntegrable_of_Icc
      hx.1.le)
    ((h.continuousOn_scaleDensity.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter
      isOpen_Ioo x hx)
    (h.continuousOn_scaleDensity.continuousAt (Icc_mem_nhds hx.1 hx.2))

/-- The scale function is continuous on `[0, 1]`. -/
theorem continuousOn_scaleFunction (h : IsRegularDiffusion b a) :
    ContinuousOn (scaleFunction b a) (Icc 0 1) := by
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (h.continuousOn_scaleDensity.intervalIntegrable_of_Icc (μ := volume) zero_le_one)
    (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
  rwa [uIcc_of_le zero_le_one] at hc

/-- The scale function is strictly increasing on `[0, 1]`. -/
theorem strictMonoOn_scaleFunction (h : IsRegularDiffusion b a) :
    StrictMonoOn (scaleFunction b a) (Icc 0 1) := by
  intro x hx y hy hxy
  have hi : ∀ z ∈ Icc (0 : ℝ) 1, IntervalIntegrable (scaleDensity b a) volume 0 z := fun z hz =>
    (h.continuousOn_scaleDensity.mono (Icc_subset_Icc_right hz.2)).intervalIntegrable_of_Icc hz.1
  have hxy' : 0 < ∫ t in x..y, scaleDensity b a t :=
    intervalIntegral.intervalIntegral_pos_of_pos
      (((hi y hy).symm.trans (hi x hx)).symm) (scaleDensity_pos b a) hxy
  have := intervalIntegral.integral_interval_sub_left (hi y hy) (hi x hx)
  simp only [scaleFunction] at this ⊢
  linarith

/-- `S(1) > 0`, so the scale-function ratio and the Green's function have a positive
denominator. -/
theorem scaleFunction_one_pos (h : IsRegularDiffusion b a) : 0 < scaleFunction b a 1 := by
  simpa using h.strictMonoOn_scaleFunction ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ one_pos

/-- A fixed allele stays fixed. -/
theorem fixationProb_one (h : IsRegularDiffusion b a) : fixationProb b a 1 = 1 := by
  exact div_self h.scaleFunction_one_pos.ne'

/-- The scale-function ratio lies in `[0, 1]`. -/
theorem fixationProb_mem_Icc (h : IsRegularDiffusion b a) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb b a p ∈ Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ scaleFunction b a p := by
    simpa using h.strictMonoOn_scaleFunction.monotoneOn ⟨le_rfl, zero_le_one⟩ hp hp.1
  have h1 : scaleFunction b a p ≤ scaleFunction b a 1 :=
    h.strictMonoOn_scaleFunction.monotoneOn hp ⟨zero_le_one, le_rfl⟩ hp.2
  exact ⟨div_nonneg h0 h.scaleFunction_one_pos.le, (div_le_one h.scaleFunction_one_pos).2 h1⟩

end IsRegularDiffusion

/-- An absent allele is never fixed (for every `b`, `a`). -/
@[simp]
theorem fixationProb_zero (b a : ℝ → ℝ) : fixationProb b a 0 = 0 := by
  simp [fixationProb]

/-- **Kimura (1962).** The scale-function ratio `S / S(1)` solves the backward equation
`a / 2 · u'' + b · u' = 0` on `(0, 1)`. -/
theorem diffusionGenerator_fixationProb {b a : ℝ → ℝ} (h : IsRegularDiffusion b a) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : diffusionGenerator b a (fixationProb b a) x = 0 := by
  have hD : deriv (fixationProb b a) =ᶠ[𝓝 x] fun y => scaleDensity b a y / scaleFunction b a 1 :=
    eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun y hy =>
      ((h.hasDerivAt_scaleFunction hy).div_const _).deriv
  have ha : a x ≠ 0 := (h.pos x hx).ne'
  have hS := h.scaleFunction_one_pos.ne'
  rw [diffusionGenerator, hD.deriv_eq, ((h.hasDerivAt_scaleDensity hx).div_const _).deriv,
    hD.eq_of_nhds]
  field_simp
  ring

/-- **Solutions of `L u = 0`.** If `u` is continuous on `[0, 1]`, differentiable on `(0, 1)`
with derivative differentiable on `(0, 1)`, and `L u = 0` on `(0, 1)`, then
`u = u(0) + (u(1) - u(0)) · S / S(1)` on `[0, 1]`. -/
theorem eq_of_diffusionGenerator_eq_zero {b a u : ℝ → ℝ} (h : IsRegularDiffusion b a)
    (hcont : ContinuousOn u (Icc 0 1)) (hdiff : DifferentiableOn ℝ u (Ioo 0 1))
    (hdiff' : DifferentiableOn ℝ (deriv u) (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, diffusionGenerator b a u x = 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, u x = u 0 + (u 1 - u 0) * fixationProb b a x := by
  -- `u' / ψ` has zero derivative on `(0, 1)`.
  have hgd : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y => deriv u y / scaleDensity b a y) 0 x := by
    intro x hx
    have hu' : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
      (hdiff'.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    have ha : a x ≠ 0 := (h.pos x hx).ne'
    have hψ := (scaleDensity_pos b a x).ne'
    convert hu'.div (h.hasDerivAt_scaleDensity hx) hψ using 1
    have hg := hgen x hx
    rw [diffusionGenerator] at hg
    field_simp
    linear_combination (-2) * hg
  -- so `u' = m ψ` on `(0, 1)`.
  set m : ℝ := deriv u (1 / 2) / scaleDensity b a (1 / 2) with hm
  have hu' : ∀ x ∈ Ioo (0 : ℝ) 1, deriv u x = m * scaleDensity b a x := by
    intro x hx
    have := eq_half_of_hasDerivAt_zero hgd x hx
    have hψ := (scaleDensity_pos b a x).ne'
    rw [hm, ← this]
    field_simp
  -- `u - m S` is constant on `[0, 1]`.
  have hh : ∀ x ∈ Icc (0 : ℝ) 1, u x - m * scaleFunction b a x = u 0 := by
    have hc : ContinuousOn (fun y => u y - m * scaleFunction b a y) (Icc 0 1) :=
      hcont.sub (h.continuousOn_scaleFunction.const_smul m)
    have hd : ∀ y ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun y => u y - m * scaleFunction b a y) 0 y := by
      intro y hy
      have hu : HasDerivAt u (deriv u y) y :=
        (hdiff.differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
      convert hu.sub ((h.hasDerivAt_scaleFunction hy).const_mul m) using 1
      rw [hu' y hy, sub_self]
    intro x hx
    rw [eq_left_of_hasDerivAt_zero' hc hd x hx, scaleFunction_zero, mul_zero, sub_zero]
  have hm1 : m * scaleFunction b a 1 = u 1 - u 0 := by
    have := hh 1 ⟨zero_le_one, le_rfl⟩
    linarith
  intro x hx
  have hS := h.scaleFunction_one_pos.ne'
  have := hh x hx
  rw [fixationProb, ← hm1]
  field_simp
  linarith

/-- **Uniqueness of the scale-function ratio (Kimura 1962).** A function continuous on
`[0, 1]`, differentiable on `(0, 1)` with derivative differentiable on `(0, 1)`, solving
`L u = 0` on `(0, 1)` with `u(0) = 0` and `u(1) = 1` equals `S / S(1)` on `[0, 1]`. -/
theorem eq_fixationProb_of_diffusionGenerator_eq_zero {b a u : ℝ → ℝ}
    (h : IsRegularDiffusion b a) (hcont : ContinuousOn u (Icc 0 1))
    (hdiff : DifferentiableOn ℝ u (Ioo 0 1)) (hdiff' : DifferentiableOn ℝ (deriv u) (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, diffusionGenerator b a u x = 0) (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ x ∈ Icc (0 : ℝ) 1, u x = fixationProb b a x := by
  intro x hx
  rw [eq_of_diffusionGenerator_eq_zero h hcont hdiff hdiff' hgen x hx, h0, h1]
  ring

/-- **Uniqueness for the Dirichlet problem.** Two functions continuous on `[0, 1]`,
differentiable on `(0, 1)` with derivatives differentiable on `(0, 1)`, with `L u = L v` on
`(0, 1)` and the same values at `0` and `1`, agree on `[0, 1]`. Together with
`diffusionGenerator_integral_greenFunction` this identifies the Green integral as the solution
of `L v = -g`, `v(0) = v(1) = 0` whenever it has this regularity. -/
theorem eq_of_diffusionGenerator_eq {b a u v : ℝ → ℝ} (h : IsRegularDiffusion b a)
    (hu : ContinuousOn u (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hu' : DifferentiableOn ℝ u (Ioo 0 1)) (hv' : DifferentiableOn ℝ v (Ioo 0 1))
    (hu'' : DifferentiableOn ℝ (deriv u) (Ioo 0 1))
    (hv'' : DifferentiableOn ℝ (deriv v) (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, diffusionGenerator b a u x = diffusionGenerator b a v x)
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) : ∀ x ∈ Icc (0 : ℝ) 1, u x = v x := by
  have hD : ∀ x ∈ Ioo (0 : ℝ) 1, deriv (fun y => u y - v y) =ᶠ[𝓝 x]
      fun y => deriv u y - deriv v y := fun x hx =>
    eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun y hy =>
      deriv_sub (hu'.differentiableAt (Ioo_mem_nhds hy.1 hy.2))
        (hv'.differentiableAt (Ioo_mem_nhds hy.1 hy.2))
  have hw := eq_of_diffusionGenerator_eq_zero (u := fun y => u y - v y) h (hu.sub hv)
    (hu'.sub hv') (by
      intro x hx
      refine (DifferentiableAt.differentiableWithinAt ?_)
      rw [(hD x hx).differentiableAt_iff]
      exact (hu''.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).sub
        (hv''.differentiableAt (Ioo_mem_nhds hx.1 hx.2)))
    (by
      intro x hx
      have hux := hu''.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
      have hvx := hv''.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
      have hg := hgen x hx
      simp only [diffusionGenerator] at hg ⊢
      rw [(hD x hx).deriv_eq, deriv_fun_sub hux hvx, (hD x hx).eq_of_nhds]
      linear_combination hg)
  intro x hx
  have := hw x hx
  simp only [h0, h1, sub_self, zero_mul, add_zero] at this
  linarith

/-- The Green integral split at `q ∈ (0, 1)`: `∫₀¹ G(q, x) g(x) dx` equals
`(2 / S(1)) ((S(1) - S(q)) ∫₀^q S g / (a ψ) + S(q) ∫_q^1 (S(1) - S) g / (a ψ))`. -/
private theorem integral_greenFunction_mul {b a g : ℝ → ℝ}
    (hL : ∀ q ∈ Ioo (0 : ℝ) 1, IntervalIntegrable
      (fun x => scaleFunction b a x * g x / (a x * scaleDensity b a x)) volume 0 q)
    (hR : ∀ q ∈ Ioo (0 : ℝ) 1, IntervalIntegrable
      (fun x => (scaleFunction b a 1 - scaleFunction b a x) * g x / (a x * scaleDensity b a x))
      volume q 1)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, greenFunction b a q x * g x =
      2 / scaleFunction b a 1 * ((scaleFunction b a 1 - scaleFunction b a q) *
        (∫ x in (0 : ℝ)..q, scaleFunction b a x * g x / (a x * scaleDensity b a x)) +
        scaleFunction b a q * ∫ x in q..1, (scaleFunction b a 1 - scaleFunction b a x) * g x /
          (a x * scaleDensity b a x)) := by
  set S := scaleFunction b a
  set ψ := scaleDensity b a
  have hEL : EqOn (fun x => greenFunction b a q x * g x)
      (fun x => 2 / S 1 * (S 1 - S q) * (S x * g x / (a x * ψ x))) (uIcc 0 q) := by
    intro x hx
    rw [uIcc_of_le hq.1.le] at hx
    simp only [greenFunction, min_eq_right hx.2, max_eq_left hx.2]
    ring
  have hER : EqOn (fun x => greenFunction b a q x * g x)
      (fun x => 2 / S 1 * S q * ((S 1 - S x) * g x / (a x * ψ x))) (uIcc q 1) := by
    intro x hx
    rw [uIcc_of_le hq.2.le] at hx
    simp only [greenFunction, min_eq_left hx.1, max_eq_right hx.1]
    ring
  have iL : IntervalIntegrable (fun x => greenFunction b a q x * g x) volume 0 q :=
    (intervalIntegrable_congr (hEL.symm.mono uIoc_subset_uIcc)).1 ((hL q hq).const_mul _)
  have iR : IntervalIntegrable (fun x => greenFunction b a q x * g x) volume q 1 :=
    (intervalIntegrable_congr (hER.symm.mono uIoc_subset_uIcc)).1 ((hR q hq).const_mul _)
  rw [← intervalIntegral.integral_add_adjacent_intervals iL iR,
    intervalIntegral.integral_congr hEL, intervalIntegral.integral_congr hER,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- **Green's representation (Ewens 2004, Chapter 4; Karlin–Taylor 1981, Chapter 15).** Let `g` be
continuous on `(0, 1)` and assume the two halves of the Green integral are integrable away from
the opposite boundary: `S g / (a ψ)` on `[0, q]` and `(S(1) - S) g / (a ψ)` on `[q, 1]` for every
`q ∈ (0, 1)` (true for every `g` continuous on `[0, 1]` under genic selection, where
`S / (a ψ)` is bounded near `0` and `(S(1) - S) / (a ψ)` near `1`). Then
`v(q) = ∫₀¹ G(q, x) g(x) dx` solves `L v = -g` on `(0, 1)`. -/
theorem diffusionGenerator_integral_greenFunction {b a g : ℝ → ℝ} (h : IsRegularDiffusion b a)
    (hg : ContinuousOn g (Ioo 0 1))
    (hL : ∀ q ∈ Ioo (0 : ℝ) 1, IntervalIntegrable
      (fun x => scaleFunction b a x * g x / (a x * scaleDensity b a x)) volume 0 q)
    (hR : ∀ q ∈ Ioo (0 : ℝ) 1, IntervalIntegrable
      (fun x => (scaleFunction b a 1 - scaleFunction b a x) * g x / (a x * scaleDensity b a x))
      volume q 1)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    diffusionGenerator b a (fun q => ∫ x in (0 : ℝ)..1, greenFunction b a q x * g x) p = -g p := by
  set S := scaleFunction b a with hSdef
  set ψ := scaleDensity b a with hψdef
  set fL : ℝ → ℝ := fun x => S x * g x / (a x * ψ x) with hfL
  set fR : ℝ → ℝ := fun x => (S 1 - S x) * g x / (a x * ψ x) with hfR
  have hS1 : S 1 ≠ 0 := h.scaleFunction_one_pos.ne'
  have hSc : ContinuousOn S (Ioo 0 1) := h.continuousOn_scaleFunction.mono Ioo_subset_Icc_self
  have hψc : ContinuousOn ψ (Ioo 0 1) := h.continuousOn_scaleDensity.mono Ioo_subset_Icc_self
  have haψ : ∀ x ∈ Ioo (0 : ℝ) 1, a x * ψ x ≠ 0 := fun x hx =>
    (mul_pos (h.pos x hx) (scaleDensity_pos b a x)).ne'
  have hcL : ContinuousOn fL (Ioo 0 1) :=
    (hSc.mul hg).div (h.continuousOn.mul hψc) haψ
  have hcR : ContinuousOn fR (Ioo 0 1) :=
    ((continuousOn_const.sub hSc).mul hg).div (h.continuousOn.mul hψc) haψ
  -- FTC for the two halves.
  have hA : ∀ q ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => ∫ x in (0 : ℝ)..t, fL x) (fL q) q :=
    fun q hq => intervalIntegral.integral_hasDerivAt_right (hL q hq)
      (hcL.stronglyMeasurableAtFilter isOpen_Ioo q hq) (hcL.continuousAt (Ioo_mem_nhds hq.1 hq.2))
  have hB : ∀ q ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => ∫ x in t..1, fR x) (-fR q) q :=
    fun q hq => intervalIntegral.integral_hasDerivAt_left (hR q hq)
      (hcR.stronglyMeasurableAtFilter isOpen_Ioo q hq) (hcR.continuousAt (Ioo_mem_nhds hq.1 hq.2))
  -- The first derivative: boundary terms cancel.
  set D : ℝ → ℝ := fun t => 2 / S 1 * ψ t * ((∫ x in t..1, fR x) - ∫ x in (0 : ℝ)..t, fL x)
    with hD
  have hv : ∀ q ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun t => 2 / S 1 * ((S 1 - S t) * (∫ x in (0 : ℝ)..t, fL x) + S t * ∫ x in t..1, fR x))
      (D q) q := by
    intro q hq
    have hSq := h.hasDerivAt_scaleFunction hq
    have hd := ((((hSq.const_sub (S 1)).mul (hA q hq)).add (hSq.mul (hB q hq))).const_mul
      (2 / S 1))
    convert hd using 1
    have := haψ q hq
    simp only [hD, hfL, hfR]
    field_simp
    ring
  have hderiv : deriv (fun q => ∫ x in (0 : ℝ)..1, greenFunction b a q x * g x) =ᶠ[𝓝 p] D := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
    rw [Filter.EventuallyEq.deriv_eq (f := fun t => 2 / S 1 * ((S 1 - S t) *
      (∫ x in (0 : ℝ)..t, fL x) + S t * ∫ x in t..1, fR x)) ?_]
    · exact (hv q hq).deriv
    · filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
      exact integral_greenFunction_mul hL hR ht
  -- The second derivative.
  have hD' : HasDerivAt D (2 / S 1 * (-(2 * b p / a p) * ψ p) *
      ((∫ x in p..1, fR x) - ∫ x in (0 : ℝ)..p, fL x) +
      2 / S 1 * ψ p * (-fR p - fL p)) p :=
    (((h.hasDerivAt_scaleDensity hp).const_mul (2 / S 1)).mul ((hB p hp).sub (hA p hp)))
  have ha : a p ≠ 0 := (h.pos p hp).ne'
  have hψp : ψ p ≠ 0 := (scaleDensity_pos b a p).ne'
  rw [diffusionGenerator, hderiv.deriv_eq, hD'.deriv, hderiv.eq_of_nhds]
  simp only [hD, hfL, hfR]
  field_simp
  ring

/-- Dirichlet condition at `0`: `∫₀¹ G(0, x) g(x) dx = 0` (for every `b`, `a`, `g`). -/
theorem integral_greenFunction_zero_left (b a g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, greenFunction b a 0 x * g x = 0 := by
  refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
    (ae_of_all _ fun x hx => ?_)).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hx
  simp [greenFunction, min_eq_left hx.1.le]

/-- Dirichlet condition at `1`: `∫₀¹ G(1, x) g(x) dx = 0` (for every `b`, `a`, `g`). -/
theorem integral_greenFunction_one_left (b a g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, greenFunction b a 1 x * g x = 0 := by
  refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
    (ae_of_all _ fun x hx => ?_)).trans (by simp)
  rw [uIoc_of_le zero_le_one] at hx
  simp [greenFunction, max_eq_left hx.2]

/-! ### Genic selection and dominance -/

/-- The general generator with drift `σ x (1 - x)` and variance `x (1 - x)` is the Wright–Fisher
generator with genic selection. -/
theorem diffusionGenerator_wrightFisher (σ : ℝ) (u : ℝ → ℝ) :
    diffusionGenerator (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) u = generator σ u := by
  rfl

/-- The Wright–Fisher diffusion with genic selection is regular. -/
theorem isRegularDiffusion_wrightFisher (σ : ℝ) :
    IsRegularDiffusion (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) := by
  have hEq : EqOn (fun x => σ * x * (1 - x) / (x * (1 - x))) (fun _ => σ) (Ioo 0 1) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
    simp only
    field_simp
  exact
    { pos := fun x hx => mul_pos hx.1 (sub_pos.2 hx.2)
      continuousOn := by fun_prop
      continuousOn_div := continuousOn_const.congr hEq
      intervalIntegrable_div := intervalIntegrable_of_eqOn_Ioo intervalIntegrable_const hEq }

/-- The scale density of the Wright–Fisher diffusion with genic selection is `e^{-2σy}` on
`[0, 1]`. -/
theorem scaleDensity_wrightFisher (σ : ℝ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    scaleDensity (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) y = exp (-2 * σ * y) := by
  have hEq : EqOn (fun z => 2 * (σ * z * (1 - z)) / (z * (1 - z))) (fun _ => 2 * σ)
      (Ioo 0 1) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
    simp only
    field_simp
  rw [scaleDensity, integral_congr_Ioo hy hEq, intervalIntegral.integral_const, smul_eq_mul]
  ring_nf

/-- **Kimura's formula as a corollary.** For genic selection the general scale-function ratio
is `kimuraFixation σ p` on `[0, 1]`. -/
theorem fixationProb_wrightFisher (σ : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) p = kimuraFixation σ p := by
  have hd : ∀ y, HasDerivAt (kimuraFixation σ) (kimuraSlope σ * exp (-2 * σ * y)) y :=
    hasDerivAt_kimuraFixation σ
  have hD : deriv (kimuraFixation σ) = fun y => kimuraSlope σ * exp (-2 * σ * y) :=
    deriv_kimuraFixation σ
  refine (eq_fixationProb_of_diffusionGenerator_eq_zero (isRegularDiffusion_wrightFisher σ)
    (continuous_kimuraFixation σ).continuousOn
    (fun y _ => (hd y).differentiableAt.differentiableWithinAt) ?_ ?_
    (kimuraFixation_zero_right σ) (kimuraFixation_one_right σ) p hp).symm
  · rw [hD]
    fun_prop
  · intro x _
    rw [diffusionGenerator_wrightFisher, generator_kimuraFixation]

/-- The general Green's function of the neutral Wright–Fisher diffusion (`b = 0`,
`a = x (1 - x)`) is the neutral Green's function of `Sojourn.lean` for `x ∈ (0, 1)`. -/
theorem greenFunction_neutral (p : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    greenFunction (fun _ => 0) (fun x => x * (1 - x)) p x = neutralGreen p x := by
  have hψ : ∀ y, scaleDensity (fun _ => 0) (fun x => x * (1 - x)) y = 1 := fun y => by
    simp [scaleDensity]
  have hS : ∀ y, scaleFunction (fun _ => 0) (fun x => x * (1 - x)) y = y := fun y => by
    simp [scaleFunction, hψ]
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  simp only [greenFunction, hS, hψ, neutralGreen]
  split_ifs with hxp
  · rw [min_eq_right hxp, max_eq_left hxp]
    field_simp
  · push Not at hxp
    rw [min_eq_left hxp.le, max_eq_right hxp.le]
    field_simp

/-- The drift `2 c x (1 - x) (h + (1 - 2h) x)` of an allele at frequency `x` with genotype
fitnesses `1`, `1 + h s`, `1 + s` (for zero, one and two copies), `c = N s`, time in units of
`2N` generations (Kimura 1962). For `h = 1/2` it is genic selection with `σ = c`. -/
noncomputable def dominanceDrift (c h x : ℝ) : ℝ :=
  2 * c * x * (1 - x) * (h + (1 - 2 * h) * x)

/-- The diffusion with dominance is regular. -/
theorem isRegularDiffusion_dominance (c h : ℝ) :
    IsRegularDiffusion (dominanceDrift c h) (fun x => x * (1 - x)) := by
  have hEq : EqOn (fun x => dominanceDrift c h x / (x * (1 - x)))
      (fun x => 2 * c * (h + (1 - 2 * h) * x)) (Ioo 0 1) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
    simp only [dominanceDrift]
    field_simp
  exact
    { pos := fun x hx => mul_pos hx.1 (sub_pos.2 hx.2)
      continuousOn := by fun_prop
      continuousOn_div := (by fun_prop : Continuous fun x : ℝ =>
        2 * c * (h + (1 - 2 * h) * x)).continuousOn.congr hEq
      intervalIntegrable_div := intervalIntegrable_of_eqOn_Ioo
        ((by fun_prop : Continuous fun x : ℝ =>
          2 * c * (h + (1 - 2 * h) * x)).intervalIntegrable 0 1) hEq }

/-- **Kimura's scale-function ratio with dominance (Kimura 1962).** With `D = 2h - 1`, for
`p ∈ [0, 1]`,
`u(p) = ∫₀^p e^{-2cDx(1-x) - 2cx} dx / ∫₀¹ e^{-2cDx(1-x) - 2cx} dx`. -/
theorem fixationProb_dominance (c h : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb (dominanceDrift c h) (fun x => x * (1 - x)) p =
      (∫ x in (0 : ℝ)..p, exp (-2 * c * (2 * h - 1) * x * (1 - x) - 2 * c * x)) /
        ∫ x in (0 : ℝ)..1, exp (-2 * c * (2 * h - 1) * x * (1 - x) - 2 * c * x) := by
  have hEq : EqOn (fun z => 2 * dominanceDrift c h z / (z * (1 - z)))
      (fun z => 4 * c * (h + (1 - 2 * h) * z)) (Ioo 0 1) := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
    simp only [dominanceDrift]
    field_simp
    ring
  have hψ : ∀ y ∈ Icc (0 : ℝ) 1, scaleDensity (dominanceDrift c h) (fun x => x * (1 - x)) y =
      exp (-2 * c * (2 * h - 1) * y * (1 - y) - 2 * c * y) := by
    intro y hy
    have hF : ∀ z ∈ uIcc (0 : ℝ) y, HasDerivAt
        (fun z => 4 * c * h * z + 2 * c * (1 - 2 * h) * z ^ 2)
        (4 * c * (h + (1 - 2 * h) * z)) z := fun z _ => by
      refine (((hasDerivAt_id' z).const_mul (4 * c * h)).fun_add
        ((hasDerivAt_pow 2 z).const_mul (2 * c * (1 - 2 * h)))).congr_deriv ?_
      push_cast
      ring
    rw [scaleDensity, integral_congr_Ioo hy hEq,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        ((by fun_prop : Continuous fun z : ℝ => 4 * c * (h + (1 - 2 * h) * z)).intervalIntegrable
          0 y)]
    congr 1
    ring
  have hI : ∀ q ∈ Icc (0 : ℝ) 1, scaleFunction (dominanceDrift c h) (fun x => x * (1 - x)) q =
      ∫ x in (0 : ℝ)..q, exp (-2 * c * (2 * h - 1) * x * (1 - x) - 2 * c * x) := by
    intro q hq
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hq.1] at hy
    exact hψ y ⟨hy.1, hy.2.trans hq.2⟩
  rw [fixationProb, hI p hp, hI 1 ⟨zero_le_one, le_rfl⟩]

/-! ### Conditional fixation and loss times -/

/-- The sojourn density conditioned on fixation, the Doob `h`-transform of the Green's function
by the fixation probability `u`: `G(p, x) u(x) / u(p)` (Kimura–Ohta 1969; Ewens 2004, Chapter 4).
At `p = 0` it is the junk value `0`. -/
noncomputable def conditionalGreen (b a : ℝ → ℝ) (p x : ℝ) : ℝ :=
  greenFunction b a p x * fixationProb b a x / fixationProb b a p

/-- **Conditional mean time to fixation, backward equation.** Under the hypotheses of
`diffusionGenerator_integral_greenFunction` for `g = u` (the fixation probability), the
function `w(q) = u(q) · ∫₀¹ G*(q, x) dx`, with `G*` the conditional sojourn density, solves
`L w = -u` on `(0, 1)` (Ewens 2004, Chapter 4). -/
theorem diffusionGenerator_mul_integral_conditionalGreen {b a : ℝ → ℝ}
    (h : IsRegularDiffusion b a)
    (hL : ∀ q ∈ Ioo (0 : ℝ) 1, IntervalIntegrable (fun x => scaleFunction b a x *
      fixationProb b a x / (a x * scaleDensity b a x)) volume 0 q)
    (hR : ∀ q ∈ Ioo (0 : ℝ) 1, IntervalIntegrable (fun x =>
      (scaleFunction b a 1 - scaleFunction b a x) * fixationProb b a x /
        (a x * scaleDensity b a x)) volume q 1)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    diffusionGenerator b a
      (fun q => fixationProb b a q * ∫ x in (0 : ℝ)..1, conditionalGreen b a q x) p =
      -fixationProb b a p := by
  have hg : ContinuousOn (fixationProb b a) (Ioo 0 1) :=
    (h.continuousOn_scaleFunction.mono Ioo_subset_Icc_self).div_const _
  rw [← diffusionGenerator_integral_greenFunction h hg hL hR hp]
  refine diffusionGenerator_congr (eventually_of_mem (Ioo_mem_nhds hp.1 hp.2) fun q hq => ?_)
  have hu : fixationProb b a q ≠ 0 := by
    have hS : 0 < scaleFunction b a q := by
      simpa using h.strictMonoOn_scaleFunction ⟨le_rfl, zero_le_one⟩
        (Ioo_subset_Icc_self hq) hq.1
    exact (div_pos hS h.scaleFunction_one_pos).ne'
  simp only [conditionalGreen, intervalIntegral.integral_div]
  field_simp

/-- The neutral conditional mean time to fixation `t̄₁(p) = -2 (1 - p) log (1 - p) / p`, in
units of `2N` generations (Kimura–Ohta 1969). It is meaningful for `p ∈ (0, 1)`; at `p = 0`
the division gives the junk value `0` (the limit is `2`, see
`tendsto_neutralFixationTime_zero`). -/
noncomputable def neutralFixationTime (p : ℝ) : ℝ :=
  -2 * (1 - p) * log (1 - p) / p

/-- The neutral conditional mean time to loss `t̄₀(p) = -2 p log p / (1 - p)`, in units of
`2N` generations (Kimura–Ohta 1969). It is meaningful for `p ∈ (0, 1)`. -/
noncomputable def neutralLossTime (p : ℝ) : ℝ :=
  -2 * p * log p / (1 - p)

/-- Loss of an allele at frequency `p` is fixation of the other allele at `1 - p`. -/
theorem neutralLossTime_eq (p : ℝ) : neutralLossTime p = neutralFixationTime (1 - p) := by
  unfold neutralLossTime neutralFixationTime
  rw [sub_sub_cancel]

/-- **Neutral conditional fixation time as an `h`-transformed sojourn integral.** For
`p ∈ (0, 1)`, `∫₀¹ G(p, x) · x / p dx = -2 (1 - p) log (1 - p) / p`, with `G` the neutral
Green's function and `u(x) = x` the neutral fixation probability. -/
theorem integral_neutralGreen_mul_div {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, neutralGreen p x * (x / p) = neutralFixationTime p := by
  have h0 : p ≠ 0 := ne_of_gt hp.1
  have h1 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  have hn : ∀ x ∈ uIcc (0 : ℝ) p, 1 - x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le (le_of_lt hp.1)] at hx
    exact ne_of_gt (by linarith [hx.2, hp.2])
  have hi : IntervalIntegrable (fun x : ℝ => 1 / (1 - x)) volume 0 p :=
    by
      have hc : ContinuousOn (fun x : ℝ => 1 / (1 - x)) (uIcc 0 p) :=
        continuousOn_const.div (continuous_const.sub continuous_id).continuousOn hn
      exact hc.intervalIntegrable
  have hl : EqOn (fun x => neutralGreen p x * (x / p))
      (fun x => (2 * (1 - p) / p) * (1 / (1 - x) - 1)) (uIcc 0 p) := by
    intro x hx
    have hx' := hx
    rw [uIcc_of_le (le_of_lt hp.1)] at hx'
    change neutralGreen p x * (x / p) = _
    rw [neutralGreen, ite_eq_left hx'.2]
    field_simp [hn x hx]
    ring
  have hr : EqOn (fun x => neutralGreen p x * (x / p))
      (fun _ => (2 : ℝ)) (uIcc p 1) := by
    intro x hx
    rw [uIcc_of_le (le_of_lt hp.2)] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hp.1 hx.1)
    change neutralGreen p x * (x / p) = 2
    unfold neutralGreen
    split_ifs with hxp
    · have hxp' : x = p := le_antisymm hxp hx.1
      subst x
      field_simp
    · field_simp
  have hli : IntervalIntegrable (fun x => neutralGreen p x * (x / p)) volume 0 p :=
    IntervalIntegrable.congr (hl.symm.mono uIoc_subset_uIcc)
      ((hi.sub intervalIntegrable_const).const_mul (2 * (1 - p) / p))
  have hri : IntervalIntegrable (fun x => neutralGreen p x * (x / p)) volume p 1 :=
    IntervalIntegrable.congr (hr.symm.mono uIoc_subset_uIcc) intervalIntegrable_const
  rw [← intervalIntegral.integral_add_adjacent_intervals hli hri,
    intervalIntegral.integral_congr hl, intervalIntegral.integral_congr hr,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi
      intervalIntegrable_const, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  have hj : (∫ x : ℝ in (0 : ℝ)..p, 1 / (1 - x)) = -log (1 - p) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => 1 / x) 1]
    rw [integral_one_div_of_pos (sub_pos.mpr hp.2) (by norm_num)]
    simp only [sub_zero, one_div, Real.log_inv]
  rw [hj]
  unfold neutralFixationTime
  simp only [smul_eq_mul, sub_zero, mul_one]
  field_simp
  ring

private theorem neutralGreen_reflect (p x : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    neutralGreen (1 - p) (1 - x) = neutralGreen p x := by
  have h0 : p ≠ 0 := ne_of_gt hp.1
  have h1 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  unfold neutralGreen
  rw [sub_sub_cancel, sub_sub_cancel]
  split_ifs with h h'
  · have hxp : x = p := by linarith
    subst x
    field_simp
  · rfl
  · rfl
  · exfalso
    linarith

/-- **Neutral conditional loss time.** For `p ∈ (0, 1)`,
`∫₀¹ G(p, x) · (1 - x) / (1 - p) dx = -2 p log p / (1 - p)`. -/
theorem integral_neutralGreen_mul_one_sub_div {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, neutralGreen p x * ((1 - x) / (1 - p)) = neutralLossTime p := by
  have hp' : 1 - p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  rw [neutralLossTime_eq]
  rw [← integral_neutralGreen_mul_div hp']
  have he := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1)
    (fun x => neutralGreen (1 - p) x * (x / (1 - p))) 1
  simp only [sub_self, sub_zero] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro x _
  change neutralGreen p x * _ = neutralGreen (1 - p) (1 - x) * _
  rw [neutralGreen_reflect p x hp]

/-- **The general `h`-transform specializes to Kimura–Ohta.** For the neutral Wright–Fisher
diffusion (`b = 0`, `a = x (1 - x)`) and `p ∈ (0, 1)`, the total conditional sojourn time
`∫₀¹ G(p, x) u(x) / u(p) dx` is `-2 (1 - p) log (1 - p) / p`. -/
theorem integral_conditionalGreen_neutral {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, conditionalGreen (fun _ => 0) (fun x => x * (1 - x)) p x =
      neutralFixationTime p := by
  have hψ : ∀ y, scaleDensity (fun _ => 0) (fun x => x * (1 - x)) y = 1 := fun y => by
    simp [scaleDensity]
  have hu : ∀ y, fixationProb (fun _ => 0) (fun x => x * (1 - x)) y = y := fun y => by
    simp [fixationProb, scaleFunction, hψ]
  rw [← integral_neutralGreen_mul_div hp, integral_congr_Ioo ⟨zero_le_one, le_rfl⟩]
  intro x hx
  simp only [conditionalGreen, hu, greenFunction_neutral p hx]
  ring

private theorem hasDerivAt_neutral_product (p : ℝ) (hp : 1 - p ≠ 0) :
    HasDerivAt (fun q : ℝ => -2 * (1 - q) * log (1 - q))
      (2 * (log (1 - p) + 1)) p := by
  have hd : HasDerivAt (fun q : ℝ => 1 - q) (-1) p := by
    simpa only [id_eq] using (hasDerivAt_id p).const_sub 1
  convert (hd.mul (hd.log hp)).const_mul (-2) using 1
  · ext q
    simp only [Pi.mul_apply]
    ring
  · field_simp
    ring

/-- The neutral conditional fixation time satisfies the conditioned backward equation
`L_0 (p · t̄₁(p)) = -p` on `(0, 1)`. -/
theorem generator_mul_neutralFixationTime {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    generator 0 (fun q => q * neutralFixationTime q) p = -p := by
  have h0 : p ≠ 0 := ne_of_gt hp.1
  have h1 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  have he : (fun q => q * neutralFixationTime q) =ᶠ[𝓝 p]
      (fun q => -2 * (1 - q) * log (1 - q)) := by
    filter_upwards [eventually_ne_nhds h0] with q hq
    unfold neutralFixationTime
    field_simp
  have hd : deriv (fun q : ℝ => -2 * (1 - q) * log (1 - q)) =ᶠ[𝓝 p]
      (fun q => 2 * (log (1 - q) + 1)) := by
    filter_upwards [eventually_ne_nhds (show p ≠ 1 by linarith [hp.2])] with q hq
    exact (hasDerivAt_neutral_product q (sub_ne_zero.mpr hq.symm)).deriv
  have hdd : HasDerivAt (fun q : ℝ => 2 * (log (1 - q) + 1))
      (2 * (-1 / (1 - p))) p := by
    simpa only [id_eq] using
      ((((hasDerivAt_id p).const_sub 1).log h1).add_const 1).const_mul 2
  rw [generator, he.deriv.deriv_eq, hd.deriv_eq, hdd.deriv]
  simp only [zero_mul, add_zero]
  field_simp

/-- **`t̄₁(0⁺) = 2`.** A new neutral mutation that is destined to fix takes on average `2`
units (`4N` generations) to do so (Kimura–Ohta 1969). -/
theorem tendsto_neutralFixationTime_zero :
    Tendsto neutralFixationTime (𝓝[>] 0) (𝓝 2) := by
  have hd : HasDerivAt (fun p : ℝ => log (1 - p)) (-1) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num) using 1 <;> norm_num
  have hl : Tendsto (fun p : ℝ => log (1 - p) / p) (𝓝[>] 0) (𝓝 (-1)) := by
    simpa only [zero_add, sub_zero, log_one, smul_eq_mul, ← div_eq_inv_mul] using
      hd.tendsto_slope_zero_right
  have hc : Tendsto (fun p : ℝ => -2 * (1 - p)) (𝓝[>] 0) (𝓝 (-2)) := by
    have h : Continuous (fun p : ℝ => -2 * (1 - p)) := by fun_prop
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  convert hc.mul hl using 1
  · ext p
    unfold neutralFixationTime
    ring
  · norm_num

/-- **Total expectation.** For `p ∈ (0, 1)`,
`p · t̄₁(p) + (1 - p) · t̄₀(p) = -2 (p log p + (1 - p) log (1 - p))`, the unconditional mean
absorption time. -/
theorem mul_neutralFixationTime_add_mul_neutralLossTime {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    p * neutralFixationTime p + (1 - p) * neutralLossTime p = meanAbsorptionTime p := by
  have h0 : p ≠ 0 := ne_of_gt hp.1
  have h1 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  unfold neutralFixationTime neutralLossTime meanAbsorptionTime
  field_simp
  ring

end MathlibExt.Biology.PopulationGenetics.Diffusion
