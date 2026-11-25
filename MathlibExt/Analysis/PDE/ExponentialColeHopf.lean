/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Classical exponential-sum Cole–Hopf solutions

For a finite family of real weights `cᵢ` and frequencies `kᵢ`, put
`Hₙ(t,x) = ∑ᵢ cᵢ kᵢⁿ exp(ν kᵢ² t + kᵢ x)`. The moment identities
`∂ₓ Hₙ = Hₙ₊₁` and `∂ₜ Hₙ = ν Hₙ₊₂` imply the heat equation for `H₀`.
The Cole–Hopf transform `u = -2ν H₁/H₀` satisfies the classical Burgers equation
`uₜ + u uₓ = ν uₓₓ` wherever `H₀ ≠ 0`. Derivatives here are real `deriv` and
`iteratedDeriv`, not formal coefficient identities.

Nonnegative weights with one strictly positive weight give a positive denominator
on the whole real time-space plane. Signed weights are allowed in the local
theorem. The identities hold for every real `ν`; positive `ν` is the usual
viscous interpretation. No arbitrary-data existence or uniqueness is claimed.

## References

* Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
  Lemma 3.1, equations (3.1)–(3.2), https://arxiv.org/abs/solv-int/9812025.
* Zarmi, *Generation of shock waves from localized sources: The case of the
  Burgers equation*, equations (3)–(5), https://arxiv.org/abs/1908.01315.
  Those equations use `vₜ = 2 v vₓ + vₓₓ` and positive exponential weights;
  rescaling time by `ν` and setting `u = -2ν v` gives the convention here.
  Arbitrary signed weights on the nonzero locus and the derivative-moment API
  are elementary consequences of finite linearity and the quotient rule.
-/

@[expose] public section

open scoped ContDiff Topology

namespace ColeHopf

variable {ι : Type*} (s : Finset ι) (c k : ι → ℝ) (ν : ℝ)

/-- Exponential heat moments; order zero is the heat profile. -/
noncomputable def heatMoment (n : ℕ) (t x : ℝ) : ℝ :=
  ∑ i ∈ s, c i * k i ^ n * Real.exp (ν * k i ^ 2 * t + k i * x)

/-- Every heat moment is jointly smooth in time and space. -/
theorem heatMoment_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => heatMoment s c k ν n p.1 p.2) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (((contDiff_const.mul contDiff_fst).add
    (contDiff_const.mul contDiff_snd)).exp)

/-- The spatial derivative raises the moment order by one. -/
theorem heatMoment_hasDerivAt_x (n : ℕ) (t x : ℝ) :
    HasDerivAt (heatMoment s c k ν n t) (heatMoment s c k ν (n + 1) t x) x := by
  unfold heatMoment
  apply HasDerivAt.fun_sum
  intro i _
  have h := (((hasDerivAt_id x).const_mul (k i)).const_add
    (ν * k i ^ 2 * t)).exp.const_mul (c i * k i ^ n)
  convert h using 1 <;> simp only [id_eq, mul_one, pow_succ]; ring

/-- The time derivative raises the moment order by two and multiplies by `ν`. -/
theorem heatMoment_hasDerivAt_t (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun t => heatMoment s c k ν n t x)
      (ν * heatMoment s c k ν (n + 2) t x) t := by
  unfold heatMoment
  rw [Finset.mul_sum]
  apply HasDerivAt.fun_sum
  intro i _
  have h := (((hasDerivAt_id t).const_mul (ν * k i ^ 2)).add_const
    (k i * x)).exp.const_mul (c i * k i ^ n)
  convert h using 1 <;> simp only [id_eq, mul_one, pow_add]; ring

/-- The exponential sum solves the heat equation on the whole real plane. -/
theorem heatMoment_heat (t x : ℝ) :
    deriv (fun t => heatMoment s c k ν 0 t x) t =
      ν * iteratedDeriv 2 (heatMoment s c k ν 0 t) x := by
  rw [(heatMoment_hasDerivAt_t s c k ν 0 t x).deriv,
    iteratedDeriv_succ, iteratedDeriv_one,
    funext (fun y => (heatMoment_hasDerivAt_x s c k ν 0 t y).deriv),
    (heatMoment_hasDerivAt_x s c k ν 1 t x).deriv]

/-- Cole–Hopf transform of a finite exponential-sum heat profile.
At denominator zeros this is Lean's total division; PDE assertions below
explicitly require a nonzero denominator. -/
noncomputable def exponentialSolution (t x : ℝ) : ℝ :=
  -2 * ν * (heatMoment s c k ν 1 t x / heatMoment s c k ν 0 t x)

/-- Joint smoothness of the solution on the nonzero locus of its denominator. -/
theorem exponentialSolution_contDiffAt (p : ℝ × ℝ)
    (h : heatMoment s c k ν 0 p.1 p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => exponentialSolution s c k ν q.1 q.2) p :=
  contDiffAt_const.mul (((heatMoment_contDiff s c k ν 1).contDiffAt).div
    (heatMoment_contDiff s c k ν 0).contDiffAt h)

/-- Spatial derivative of the Cole–Hopf solution at a nonsingular point. -/
theorem exponentialSolution_hasDerivAt_x (t x : ℝ)
    (h : heatMoment s c k ν 0 t x ≠ 0) :
    HasDerivAt (exponentialSolution s c k ν t)
      (-2 * ν * ((heatMoment s c k ν 2 t x * heatMoment s c k ν 0 t x -
        heatMoment s c k ν 1 t x * heatMoment s c k ν 1 t x) /
          heatMoment s c k ν 0 t x ^ 2)) x :=
  ((heatMoment_hasDerivAt_x s c k ν 1 t x).div
    (heatMoment_hasDerivAt_x s c k ν 0 t x) h).const_mul (-2 * ν)

/-- Time derivative of the Cole–Hopf solution at a nonsingular point. -/
theorem exponentialSolution_hasDerivAt_t (t x : ℝ)
    (h : heatMoment s c k ν 0 t x ≠ 0) :
    HasDerivAt (fun t => exponentialSolution s c k ν t x)
      (-2 * ν * ((ν * heatMoment s c k ν 3 t x * heatMoment s c k ν 0 t x -
        heatMoment s c k ν 1 t x * (ν * heatMoment s c k ν 2 t x)) /
          heatMoment s c k ν 0 t x ^ 2)) t :=
  ((heatMoment_hasDerivAt_t s c k ν 1 t x).div
    (heatMoment_hasDerivAt_t s c k ν 0 t x) h).const_mul (-2 * ν)

/-- The second spatial derivative is computed locally on the nonzero locus. -/
theorem exponentialSolution_iteratedDeriv_two (t x : ℝ)
    (h : heatMoment s c k ν 0 t x ≠ 0) :
    iteratedDeriv 2 (exponentialSolution s c k ν t) x =
      -2 * ν * (heatMoment s c k ν 3 t x / heatMoment s c k ν 0 t x -
        3 * heatMoment s c k ν 1 t x * heatMoment s c k ν 2 t x /
          heatMoment s c k ν 0 t x ^ 2 +
        2 * heatMoment s c k ν 1 t x ^ 3 / heatMoment s c k ν 0 t x ^ 3) := by
  let H := fun n => heatMoment s c k ν n t
  have h0 := heatMoment_hasDerivAt_x s c k ν 0 t x
  have h1 := heatMoment_hasDerivAt_x s c k ν 1 t x
  have h2 := heatMoment_hasDerivAt_x s c k ν 2 t x
  have hd := (((h2.mul h0).sub (h1.mul h1)).div (h0.pow 2) (pow_ne_zero 2 h)).const_mul
    (-2 * ν)
  have heq : deriv (exponentialSolution s c k ν t) =ᶠ[𝓝 x]
      (fun y => -2 * ν * ((H 2 y * H 0 y - H 1 y * H 1 y) / H 0 y ^ 2)) := by
    filter_upwards [h0.continuousAt.eventually_ne h] with y hy
    exact (exponentialSolution_hasDerivAt_x s c k ν t y hy).deriv
  have hd' := hd.congr_of_eventuallyEq heq
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd'.deriv]
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

/-- Classical Burgers equation at every point with nonzero heat denominator. -/
theorem exponentialSolution_burgers (t x : ℝ)
    (h : heatMoment s c k ν 0 t x ≠ 0) :
    deriv (fun t => exponentialSolution s c k ν t x) t +
      exponentialSolution s c k ν t x * deriv (exponentialSolution s c k ν t) x =
        ν * iteratedDeriv 2 (exponentialSolution s c k ν t) x := by
  rw [(exponentialSolution_hasDerivAt_t s c k ν t x h).deriv,
    (exponentialSolution_hasDerivAt_x s c k ν t x h).deriv,
    exponentialSolution_iteratedDeriv_two s c k ν t x h]
  unfold exponentialSolution
  field_simp
  ring

/-- Nonnegative weights with one positive member give a globally positive profile. -/
theorem heatMoment_zero_pos (hc : ∀ i ∈ s, 0 ≤ c i)
    (hp : ∃ i ∈ s, 0 < c i) (t x : ℝ) : 0 < heatMoment s c k ν 0 t x := by
  obtain ⟨i, hi, hci⟩ := hp
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (mul_nonneg (hc j hj) (by simp)) (Real.exp_pos _).le
  · exact ⟨i, hi, mul_pos (by simpa using hci) (Real.exp_pos _)⟩

/-- With nonnegative weights and positive mass, Burgers holds everywhere. -/
theorem exponentialSolution_burgers_of_nonneg (hc : ∀ i ∈ s, 0 ≤ c i)
    (hp : ∃ i ∈ s, 0 < c i) (t x : ℝ) :
    deriv (fun t => exponentialSolution s c k ν t x) t +
      exponentialSolution s c k ν t x * deriv (exponentialSolution s c k ν t) x =
        ν * iteratedDeriv 2 (exponentialSolution s c k ν t) x :=
  exponentialSolution_burgers s c k ν t x (ne_of_gt (heatMoment_zero_pos s c k ν hc hp t x))

/-- Initial data of the heat profile. -/
theorem heatMoment_zero_time (x : ℝ) :
    heatMoment s c k ν 0 0 x = ∑ i ∈ s, c i * Real.exp (k i * x) := by
  simp [heatMoment]

/-- Initial data of the transformed Burgers solution. -/
theorem exponentialSolution_zero_time (x : ℝ) :
    exponentialSolution s c k ν 0 x =
      -2 * ν * ((∑ i ∈ s, c i * k i * Real.exp (k i * x)) /
        ∑ i ∈ s, c i * Real.exp (k i * x)) := by
  simp [exponentialSolution, heatMoment]

end ColeHopf
