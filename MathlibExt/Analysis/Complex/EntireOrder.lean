/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization/Order.lean`
(PrimeNumberTheoremAnd):
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Matteo Cipollina
-/

module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Bound

/-!
# The order of growth of an entire function

An entire function `f : ℂ → ℂ` has *order at most `ρ`*
(`Complex.Hadamard.EntireOfOrderAtMost ρ f`, the definition of PrimeNumberTheoremAnd) if for
every `ε > 0` there is `C > 0` with `‖f z‖ ≤ exp (C * (1 + ‖z‖) ^ (ρ + ε))` for all `z`.
Differentiability is part of the definition. It has *order `ρ`* (`Complex.HasGrowthOrder f ρ`) if
moreover `ρ ≥ 0` and it has order at most no smaller nonnegative exponent. For a nonzero entire
function this is the classical order `limsup_{r → ∞} log log M(r) / log r`, where `M(r)` is the
maximum of `‖f‖` on the circle of radius `r`; in particular constants and polynomials have order
`0`.

For `ρ ≥ 0` the bound is equivalent to `f = O(exp (‖z‖ ^ (ρ + ε)))` at infinity for every
`ε > 0` (`Complex.Hadamard.entireOfOrderAtMost_iff`). For `ρ < 0` it is much stronger: it forces
`f` to be a constant of norm at most `1`, so for instance the constant `5` has order at most no
negative exponent. Several closure properties therefore assume `0 ≤ ρ`.

This is not Mathlib's `analyticOrderAt` or `meromorphicOrderAt`, which measure the order of
vanishing at a point.

The two growth statements about zeros proved here are the inputs of Hadamard's factorization
theorem: for `f` entire of order at most `ρ ≥ 0`, the number of zeros in the closed disc of
radius `r`, counted with multiplicity, is `O(r ^ (ρ + ε))`, and the zeros `z_n` (again with
multiplicity) satisfy `∑ ‖z_n‖ ^ (-ρ - ε) < ∞`. Both follow from Jensen's inequality.

## Main definitions

* `Complex.Hadamard.EntireOfOrderAtMost ρ f`: `f` is entire of order at most `ρ`.
* `Complex.HasGrowthOrder f ρ`: `f` is entire of order exactly `ρ`.

## Main statements

* `Complex.Hadamard.entireOfOrderAtMost_iff`: for `ρ ≥ 0`, order at most `ρ` is
  differentiability together with `f = O(exp (‖z‖ ^ (ρ + ε)))` at infinity for every `ε > 0`.
* `Complex.Hadamard.EntireOfOrderAtMost.isBigO_exp_rpow`: order at most `ρ` gives
  `f = O(exp (‖z‖ ^ τ))` at infinity for every `τ > max ρ 0`.
* `Complex.Hadamard.EntireOfOrderAtMost.mono`, `Complex.Hadamard.EntireOfOrderAtMost.trans_isBigO`,
  `Complex.Hadamard.EntireOfOrderAtMost.add`, `Complex.Hadamard.EntireOfOrderAtMost.mul`,
  `Complex.Hadamard.entireOfOrderAtMost_of_isBigO_one`,
  `Complex.Hadamard.entireOfOrderAtMost_one_of_isBigO_exp_mul_norm`: basic closure properties;
  in particular entire functions of exponential type have order at most `1`.
* `Complex.HasGrowthOrder.nonneg`, `Complex.HasGrowthOrder.unique`: the order is a well-defined
  nonnegative real number.
* `Complex.hasGrowthOrder_zero_iff`, `Complex.hasGrowthOrder_zero_of_isBigO_one`: order `0` is
  order at most `0`; in particular bounded entire functions and constants have order `0`.
* `Complex.Hadamard.EntireOfOrderAtMost.isBigO_sum_divisor_closedBall`: the zero-counting function
  of an entire function of order at most `ρ` is `O(r ^ (ρ + ε))`.
* `Complex.Hadamard.EntireOfOrderAtMost.summable_norm_rpow_neg`: the zeros `z_n` of an entire
  function of order at most `ρ` with `f 0 ≠ 0` satisfy `∑ ‖z_n‖ ^ (-ρ - ε) < ∞` (the exponent of
  convergence is at most the order).
-/

@[expose] public section

open Filter Asymptotics Bornology Metric Topology

namespace Complex.Hadamard

/-- An entire function has order at most `ρ` if it satisfies the `ε`-family growth bound used in
this formalization.

For every `ε > 0`, the norm is bounded by an exponential of order `ρ + ε`. This formulation is
the convenient finite-order input for the Jensen/counting estimates used in the Hadamard
factorization pipeline. -/
def EntireOfOrderAtMost (ρ : ℝ) (f : ℂ → ℂ) : Prop :=
    Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε →
  ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))

/-- For `0 ≤ p < q` and any `C`, eventually `C * (1 + ‖z‖) ^ p ≤ ‖z‖ ^ q` at infinity. -/
private lemma eventually_mul_one_add_rpow_le {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) (C : ℝ) :
    ∀ᶠ z in cobounded ℂ, C * (1 + ‖z‖) ^ p ≤ ‖z‖ ^ q := by
  have hK : ∀ᶠ r : ℝ in atTop, |C| * 2 ^ p ≤ r ^ (q - p) :=
    (tendsto_rpow_atTop (sub_pos.2 hpq)).eventually_ge_atTop _
  filter_upwards [tendsto_norm_cobounded_atTop.eventually hK,
    tendsto_norm_cobounded_atTop.eventually_ge_atTop 1] with z hz hz1
  have h0 : (0 : ℝ) < ‖z‖ := by linarith
  calc C * (1 + ‖z‖) ^ p ≤ |C| * (2 * ‖z‖) ^ p :=
        (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hp)
            (abs_nonneg C))
    _ = |C| * 2 ^ p * ‖z‖ ^ p := by rw [Real.mul_rpow (by norm_num) h0.le]; ring
    _ ≤ ‖z‖ ^ (q - p) * ‖z‖ ^ p := by gcongr
    _ = ‖z‖ ^ q := by rw [← Real.rpow_add h0]; ring_nf

namespace EntireOfOrderAtMost

variable {ρ ρ' ε : ℝ} {f g : ℂ → ℂ}

/-- An entire function of finite order is differentiable. -/
theorem differentiable (h : EntireOfOrderAtMost ρ f) : Differentiable ℂ f :=
  h.1

/-- The growth bound at a given `ε > 0`. -/
theorem exists_bound (h : EntireOfOrderAtMost ρ f) (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε)) :=
  h.2 ε hε

/-- For `ρ ≥ 0`, an entire function of order at most `ρ` is `O(exp (‖z‖ ^ (ρ + ε)))` at
infinity for every `ε > 0`. -/
theorem isBigO (h : EntireOfOrderAtMost ρ f) (hρ : 0 ≤ ρ) (hε : 0 < ε) :
    f =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ (ρ + ε)) := by
  obtain ⟨C, -, hC⟩ := h.exists_bound (half_pos hε)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_mul_one_add_rpow_le (by linarith : 0 ≤ ρ + ε / 2)
    (by linarith : ρ + ε / 2 < ρ + ε) C] with z hz
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (hC z).trans (Real.exp_le_exp.mpr hz)

/-- For `ρ ≥ 0`, an entire function which is `O(exp (‖z‖ ^ (ρ + ε)))` at infinity for every
`ε > 0` has order at most `ρ`. -/
theorem of_isBigO (hf : Differentiable ℂ f) (hρ : 0 ≤ ρ)
    (h : ∀ ε > 0, f =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ (ρ + ε))) :
    EntireOfOrderAtMost ρ f := by
  refine ⟨hf, fun ε hε => ?_⟩
  set p := ρ + ε with hp_def
  have hp : 0 < p := by positivity
  obtain ⟨K, hK⟩ := (h ε hε).bound
  rw [← comap_norm_atTop, eventually_comap, eventually_atTop] at hK
  obtain ⟨R, hR⟩ := hK
  rw [← hp_def] at hR
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hlK : 0 ≤ Real.log (1 + |K|) := Real.log_nonneg (by linarith [abs_nonneg K])
  have hlM : 0 ≤ Real.log (1 + |M|) := Real.log_nonneg (by linarith [abs_nonneg M])
  set C := 1 + Real.log (1 + |K|) + Real.log (1 + |M|) with hC
  refine ⟨C, by positivity, fun z => ?_⟩
  have hx1 : 1 ≤ (1 + ‖z‖) ^ p := Real.one_le_rpow (by linarith [norm_nonneg z]) hp.le
  have hxz : ‖z‖ ^ p ≤ (1 + ‖z‖) ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) (by linarith) hp.le
  have hexp : (1 + |K|) * (1 + |M|) * Real.exp (‖z‖ ^ p) ≤ Real.exp (C * (1 + ‖z‖) ^ p) := by
    rw [← Real.exp_log (by positivity : 0 < (1 + |K|) * (1 + |M|)), ← Real.exp_add,
      Real.exp_le_exp, Real.log_mul (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ C - 1) (by linarith : 0 ≤ (1 + ‖z‖) ^ p - 1)]
  have he1 : 1 ≤ Real.exp (‖z‖ ^ p) := Real.one_le_exp (Real.rpow_nonneg (norm_nonneg _) _)
  refine le_trans ?_ hexp
  have hKe : 1 ≤ (1 + |K|) * Real.exp (‖z‖ ^ p) :=
    one_le_mul_of_one_le_of_one_le (by linarith [abs_nonneg K]) he1
  by_cases hz : ‖z‖ ≤ R
  · have := hM z (by simpa [dist_eq_norm] using hz)
    nlinarith [le_abs_self M, abs_nonneg M]
  · have := hR ‖z‖ (by linarith [not_le.mp hz]) z rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at this
    have hK' : K * Real.exp (‖z‖ ^ p) ≤ |K| * Real.exp (‖z‖ ^ p) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
    nlinarith [abs_nonneg K, abs_nonneg M, Real.exp_pos (‖z‖ ^ p)]

/-- Order at most `ρ` gives order at most every larger exponent. -/
theorem mono (h : EntireOfOrderAtMost ρ f) (hρ : ρ ≤ ρ') : EntireOfOrderAtMost ρ' f := by
  refine ⟨h.differentiable, fun ε hε => ?_⟩
  obtain ⟨C, hC, hCb⟩ := h.exists_bound hε
  refine ⟨C, hC, fun z => (hCb z).trans (Real.exp_le_exp.mpr ?_)⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (by linarith)) hC.le

/-- An entire function of order at most `ρ` is `O(exp (‖z‖ ^ τ))` at infinity for every
`τ > max ρ 0`. Unlike `Complex.Hadamard.EntireOfOrderAtMost.isBigO`, this needs no sign condition
on `ρ`. -/
theorem isBigO_exp_rpow (h : EntireOfOrderAtMost ρ f) {τ : ℝ} (hρτ : ρ < τ) (hτ : 0 < τ) :
    f =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ τ) := by
  simpa using (h.mono (le_max_left ρ 0)).isBigO (le_max_right ρ 0)
    (ε := τ - max ρ 0) (sub_pos.2 (max_lt hρτ hτ))

/-- If `f` is entire, `f = O(g)` at infinity and `g` has order at most `ρ ≥ 0`, then so does
`f`. -/
theorem trans_isBigO (hg : EntireOfOrderAtMost ρ g) (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f)
    (hfg : f =O[cobounded ℂ] g) : EntireOfOrderAtMost ρ f :=
  of_isBigO hf hρ fun _ hε => hfg.trans (hg.isBigO hρ hε)

/-- **Sums.** If `f` and `g` have order at most `ρ ≥ 0`, so does `f + g`. -/
theorem add (hf : EntireOfOrderAtMost ρ f) (hg : EntireOfOrderAtMost ρ g) (hρ : 0 ≤ ρ) :
    EntireOfOrderAtMost ρ (fun z => f z + g z) :=
  of_isBigO (hf.differentiable.add hg.differentiable) hρ fun _ hε =>
    (hf.isBigO hρ hε).add (hg.isBigO hρ hε)

/-- **Products.** If `f` and `g` have order at most `ρ`, so does `f * g`. -/
theorem mul (hf : EntireOfOrderAtMost ρ f) (hg : EntireOfOrderAtMost ρ g) :
    EntireOfOrderAtMost ρ (fun z => f z * g z) := by
  refine ⟨hf.differentiable.mul hg.differentiable, fun ε hε => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hf.exists_bound hε
  obtain ⟨C₂, hC₂, h₂⟩ := hg.exists_bound hε
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun z => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  exact mul_le_mul (h₁ z) (h₂ z) (norm_nonneg _) (Real.exp_pos _).le

end EntireOfOrderAtMost

variable {ρ : ℝ} {f : ℂ → ℂ}

/-- For `ρ ≥ 0`, an entire function has order at most `ρ` if and only if it is
`O(exp (‖z‖ ^ (ρ + ε)))` at infinity for every `ε > 0`. The quantifier on `ε` sits outside the
`O`, so this is strictly weaker than `f =O[cobounded ℂ] fun z => exp (‖z‖ ^ ρ)`. -/
theorem entireOfOrderAtMost_iff (hρ : 0 ≤ ρ) :
    EntireOfOrderAtMost ρ f ↔
      Differentiable ℂ f ∧ ∀ ε > 0, f =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ (ρ + ε)) :=
  ⟨fun h => ⟨h.differentiable, fun _ hε => h.isBigO hρ hε⟩,
    fun h => EntireOfOrderAtMost.of_isBigO h.1 hρ h.2⟩

/-- An entire function bounded at infinity has order at most every `ρ ≥ 0`. -/
theorem entireOfOrderAtMost_of_isBigO_one (hf : Differentiable ℂ f)
    (hb : f =O[cobounded ℂ] fun _ => (1 : ℝ)) (hρ : 0 ≤ ρ) : EntireOfOrderAtMost ρ f := by
  refine EntireOfOrderAtMost.of_isBigO hf hρ fun ε _ => ?_
  refine hb.trans (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, norm_one]
  exact Real.one_le_exp (Real.rpow_nonneg (norm_nonneg _) _)

/-- A constant function has order at most every `ρ ≥ 0`. -/
theorem entireOfOrderAtMost_const (c : ℂ) (hρ : 0 ≤ ρ) :
    EntireOfOrderAtMost ρ (fun _ => c) :=
  entireOfOrderAtMost_of_isBigO_one (differentiable_const c)
    (isBigO_const_const c one_ne_zero _) hρ

/-- An entire function with `‖f z‖ ≤ C exp (A ‖z‖)` at infinity (a function of *exponential
type*) has order at most `1`. -/
theorem entireOfOrderAtMost_one_of_isBigO_exp_mul_norm {A : ℝ} (hf : Differentiable ℂ f)
    (hb : f =O[cobounded ℂ] fun z => Real.exp (A * ‖z‖)) : EntireOfOrderAtMost 1 f := by
  refine EntireOfOrderAtMost.of_isBigO hf zero_le_one fun ε hε => ?_
  refine hb.trans (IsBigO.of_bound 1 ?_)
  have hA : ∀ᶠ r : ℝ in atTop, A ≤ r ^ ε := (tendsto_rpow_atTop hε).eventually_ge_atTop A
  filter_upwards [tendsto_norm_cobounded_atTop.eventually hA,
    tendsto_norm_cobounded_atTop.eventually_ge_atTop 1] with z hz hz1
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_le_exp, Real.rpow_add (by linarith), Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_left hz (by linarith)

end Complex.Hadamard

namespace Complex

open Hadamard

/-- `f` has *order of growth `ρ`*: `ρ ≥ 0`, `f` is entire of order at most `ρ`, and of order at
most no smaller nonnegative exponent. For a nonzero entire `f` this is the classical order
`limsup log log M(r) / log r`; constants have order `0`. -/
def HasGrowthOrder (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ EntireOfOrderAtMost ρ f ∧ ∀ ρ' ∈ Set.Ico 0 ρ, ¬ EntireOfOrderAtMost ρ' f

section Basic

variable {f : ℂ → ℂ} {ρ ρ' : ℝ}

/-- A function of order `ρ` has order at most `ρ`. -/
theorem HasGrowthOrder.entireOfOrderAtMost (h : HasGrowthOrder f ρ) : EntireOfOrderAtMost ρ f :=
  h.2.1

/-- A function of order `ρ` is entire. -/
theorem HasGrowthOrder.differentiable (h : HasGrowthOrder f ρ) : Differentiable ℂ f :=
  h.entireOfOrderAtMost.differentiable

/-- **The order is nonnegative.** -/
theorem HasGrowthOrder.nonneg (h : HasGrowthOrder f ρ) : 0 ≤ ρ :=
  h.1

/-- A function of order `ρ` has order at most no nonnegative `ρ' < ρ`. -/
theorem HasGrowthOrder.not_entireOfOrderAtMost (h : HasGrowthOrder f ρ) (h0 : 0 ≤ ρ')
    (hlt : ρ' < ρ) : ¬ EntireOfOrderAtMost ρ' f :=
  h.2.2 ρ' ⟨h0, hlt⟩

/-- **The order is unique.** -/
theorem HasGrowthOrder.unique (h : HasGrowthOrder f ρ) (h' : HasGrowthOrder f ρ') :
    ρ = ρ' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.not_entireOfOrderAtMost h.nonneg hlt h.entireOfOrderAtMost
  · exact h.not_entireOfOrderAtMost h'.nonneg hlt h'.entireOfOrderAtMost

/-- `f` has order `0` exactly when it has order at most `0`. -/
theorem hasGrowthOrder_zero_iff : HasGrowthOrder f 0 ↔ EntireOfOrderAtMost 0 f :=
  ⟨HasGrowthOrder.entireOfOrderAtMost,
    fun h => ⟨le_rfl, h, fun _ h' => absurd h'.1 h'.2.not_ge⟩⟩

/-- An entire function bounded at infinity has order `0`. -/
theorem hasGrowthOrder_zero_of_isBigO_one (hf : Differentiable ℂ f)
    (hb : f =O[cobounded ℂ] fun _ => (1 : ℝ)) : HasGrowthOrder f 0 :=
  hasGrowthOrder_zero_iff.mpr (entireOfOrderAtMost_of_isBigO_one hf hb le_rfl)

/-- A constant function has order `0`. -/
theorem hasGrowthOrder_const (c : ℂ) : HasGrowthOrder (fun _ => c) 0 :=
  hasGrowthOrder_zero_iff.mpr (entireOfOrderAtMost_const c le_rfl)

end Basic

end Complex

/-! ### Zeros of entire functions of finite order -/

namespace Complex.Hadamard.EntireOfOrderAtMost

variable {f : ℂ → ℂ} {ρ : ℝ}

/-- **The zero-counting function of an entire function of finite order.** If `f` is entire of
order at most `ρ ≥ 0`, then for every `ε > 0` the number of zeros of `f` in the closed disc
`‖z‖ ≤ r`, counted with multiplicity, is `O(r ^ (ρ + ε))` as `r → ∞`.

The count is the finite sum of the divisor of `f` on the disc. If `f ≡ 0` the divisor is `0`, and
the statement is trivially true. A zero at the origin is allowed.

Source: J. Hadamard, "Étude sur les propriétés des fonctions entières et en particulier d'une
fonction considérée par Riemann," J. Math. Pures Appl. (4) 9 (1893), 171–215,
JFM 25.0698.03. Here the estimate is derived from Jensen's formula.

Source: H. Davenport, *Multiplicative Number Theory*, 3rd ed., Graduate Texts in Mathematics 74,
Springer, 2000, Chapter 11 (*Integral functions of order 1*),
DOI 10.1007/978-1-4757-5927-3_11. Generalised from order `1` to any order `ρ ≥ 0`. -/
theorem isBigO_sum_divisor_closedBall (h : EntireOfOrderAtMost ρ f) (hρ : 0 ≤ ρ) {ε : ℝ}
    (hε : 0 < ε) :
    (fun r : ℝ => ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ))
      =O[atTop] fun r => r ^ (ρ + ε) := by
  classical
  have hf := h.differentiable
  have han : ∀ U : Set ℂ, AnalyticOnNhd ℂ f U := fun U z _ => hf.analyticAt z
  set p := ρ + ε with hp
  have hp0 : 0 < p := by linarith
  by_cases hzero : ∀ a, f a = 0
  · have hf0 : f = 0 := funext hzero
    have : ∀ r : ℝ, ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) = 0 := by
      intro r
      simp [hf0]
    simp only [this]
    exact isBigO_zero _ _
  push Not at hzero
  obtain ⟨a, ha⟩ := hzero
  obtain ⟨C, hC⟩ := (h.isBigO hρ hε).bound
  rw [← comap_norm_atTop, eventually_comap, eventually_atTop] at hC
  obtain ⟨R0, hR0⟩ := hC
  set A := ‖a‖ with hA
  have hfa : 0 < ‖f a‖ := norm_pos_iff.mpr ha
  set K := (3 ^ p + |Real.log (1 + |C|)| + |Real.log ‖f a‖|) / Real.log 2 with hK
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (max 1 (max R0 (3 * A)))] with r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hrR0 : R0 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hr3A : 3 * A ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  have hA0 : 0 ≤ A := norm_nonneg _
  set ρ' := r + A with hρ'
  have hρ0 : 0 < ρ' := by linarith
  -- the zeros in `‖u‖ ≤ r` lie in the disc of radius `ρ'` about `a`
  have hcount : ∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u ≤
      ∑ᶠ u, MeromorphicOn.divisor f (closedBall a |ρ'|) u := by
    apply finsum_le_finsum
    · exact (MeromorphicOn.divisor f _).finiteSupport (isCompact_closedBall _ _)
    · exact (MeromorphicOn.divisor f _).finiteSupport (isCompact_closedBall _ _)
    · intro u
      by_cases hu : u ∈ closedBall (0 : ℂ) r
      · have hu' : u ∈ closedBall a |ρ'| := by
          rw [abs_of_pos hρ0]
          simp only [mem_closedBall, dist_eq_norm, sub_zero] at hu ⊢
          calc ‖u - a‖ ≤ ‖u‖ + ‖a‖ := norm_sub_le _ _
            _ ≤ ρ' := by linarith
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (han _) hu,
          MeromorphicOn.AnalyticOnNhd.divisor_apply (han _) hu']
      · simp only [hu, not_false_eq_true,
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
        exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (han (closedBall a |ρ'|)) u
  set M := 1 + |C| * Real.exp ((3 * r) ^ p) with hM
  have hJ := AnalyticOnNhd.sum_divisor_le (c := a) (r := ρ') (R := 2 * ρ') (M := M)
    (by rw [abs_of_pos hρ0]; exact hρ0)
    (by rw [abs_of_pos hρ0, abs_of_pos (by linarith)]; linarith)
    (le_add_of_nonneg_right (by positivity)) (han _) ha (by
      intro z hz
      rw [abs_of_pos (by linarith), mem_sphere_iff_norm] at hz
      have hz1 : ‖z‖ ≥ 2 * ρ' - A := by
        have := norm_sub_le z a
        have := norm_sub_norm_le z a
        linarith
      have hz2 : ‖z‖ ≤ 3 * r := by
        have : ‖z‖ ≤ ‖z - a‖ + ‖a‖ := by
          calc ‖z‖ = ‖(z - a) + a‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        linarith
      have h := hR0 ‖z‖ (by linarith) z rfl
      rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h
      have hmono : Real.exp (‖z‖ ^ p) ≤ Real.exp ((3 * r) ^ p) :=
        Real.exp_le_exp.mpr (Real.rpow_le_rpow (norm_nonneg _) hz2 hp0.le)
      calc ‖f z‖ ≤ C * Real.exp (‖z‖ ^ p) := h
        _ ≤ |C| * Real.exp (‖z‖ ^ p) := by gcongr; exact le_abs_self C
        _ ≤ |C| * Real.exp ((3 * r) ^ p) := by gcongr
        _ ≤ M := le_add_of_nonneg_left zero_le_one)
  have hlog2 : Real.log (2 * ρ' / ρ') = Real.log 2 := by
    rw [mul_div_assoc, div_self hρ0.ne', mul_one]
  rw [hlog2] at hJ
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrp : 1 ≤ r ^ p := Real.one_le_rpow hr1 hp0.le
  have h3 : (3 * r) ^ p = 3 ^ p * r ^ p := Real.mul_rpow (by norm_num) (by linarith)
  have hMle : Real.log M ≤ Real.log (1 + |C|) + (3 * r) ^ p := by
    have hx : 0 ≤ (3 * r) ^ p := Real.rpow_nonneg (by linarith) _
    have hex : 1 ≤ Real.exp ((3 * r) ^ p) := Real.one_le_exp hx
    rw [← Real.log_exp ((3 * r) ^ p), ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [hM]
    nlinarith [abs_nonneg C]
  have hMpos : 0 < M := by positivity
  rw [Real.log_div hMpos.ne' hfa.ne'] at hJ
  have hn0 : (0 : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) := by
    exact_mod_cast finsum_nonneg fun u =>
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg (han (closedBall 0 r)) u
  have hcount' : ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) ≤
      (Real.log M - Real.log ‖f a‖) / Real.log 2 :=
    le_trans (by exact_mod_cast hcount) hJ
  rw [Real.norm_of_nonneg hn0, Real.norm_of_nonneg (by linarith)]
  refine hcount'.trans ?_
  rw [hK, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hl2.le
  have e1 := le_abs_self (Real.log (1 + |C|))
  have e2 := neg_le_abs (Real.log ‖f a‖)
  have e3 : 0 ≤ |Real.log (1 + |C|)| := abs_nonneg _
  have e4 : 0 ≤ |Real.log ‖f a‖| := abs_nonneg _
  nlinarith

/-- **The exponent of convergence is at most the order.** Let `f` be entire of order at most
`ρ ≥ 0` with `f 0 ≠ 0`, and let `z : ι → ℂ` list the zeros of `f` with multiplicity, i.e. the
fibre of `z` over each `w` has `analyticOrderAt f w` elements. Then `∑ ‖z n‖ ^ (-ρ - ε)` converges
for every `ε > 0`.

The index type is arbitrary, which covers functions with finitely many zeros, and no ordering of
the zeros is needed. `f 0 ≠ 0` makes every `z n` nonzero.

Source: J. Hadamard, "Étude sur les propriétés des fonctions entières et en particulier d'une
fonction considérée par Riemann," J. Math. Pures Appl. (4) 9 (1893), 171–215,
JFM 25.0698.03.

Source: H. Davenport, *Multiplicative Number Theory*, 3rd ed., Graduate Texts in Mathematics 74,
Springer, 2000, Chapter 11 (*Integral functions of order 1*),
DOI 10.1007/978-1-4757-5927-3_11. Generalised from order `1` to any order `ρ ≥ 0`. -/
theorem summable_norm_rpow_neg {ι : Type*} {z : ι → ℂ} {ε : ℝ}
    (h : EntireOfOrderAtMost ρ f) (hρ : 0 ≤ ρ) (hf0 : f 0 ≠ 0)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt f w) (hε : 0 < ε) :
    Summable fun n => ‖z n‖ ^ (-ρ - ε) := by
  classical
  have hf := h.differentiable
  have han : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  -- every order of vanishing is finite
  have h00 : analyticOrderAt f 0 = 0 := (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0
  have hfin : ∀ w, analyticOrderAt f w ≠ ⊤ := fun w =>
    han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
      (Set.mem_univ w) (by rw [h00]; exact ENat.zero_ne_top)
  -- each `z n` is a zero of `f`
  have hzero : ∀ n, f (z n) = 0 := by
    intro n
    have h1 : analyticOrderAt f (z n) ≠ 0 := by
      rw [← hz (z n)]
      intro h
      have : IsEmpty {m // z m = z n} := ENat.card_eq_zero_iff_empty _ |>.mp h
      exact this.false ⟨n, rfl⟩
    by_contra h
    exact h1 ((hf.analyticAt _).analyticOrderAt_eq_zero.mpr h)
  -- the zeros stay away from the origin
  obtain ⟨r₀, hr₀, hr₀z⟩ : ∃ r₀ > 0, ∀ n, r₀ ≤ ‖z n‖ := by
    have hev : ∀ᶠ w in 𝓝 (0 : ℂ), f w ≠ 0 := hf.continuous.continuousAt.eventually_ne hf0
    obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨r₀, hr₀, fun n => ?_⟩
    by_contra h
    push Not at h
    exact hball (by simpa [dist_eq_norm] using h) (hzero n)
  -- counting the indices of a finite set against the zero-counting function
  have hcount : ∀ (t : Finset ι) (r : ℝ),
      ((t.filter fun n => ‖z n‖ ≤ r).card : ℝ) ≤
        ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) := by
    intro t r
    set T := t.filter fun n => ‖z n‖ ≤ r with hT
    set D := MeromorphicOn.divisor f (closedBall (0 : ℂ) r) with hD
    have hDnn : ∀ u, 0 ≤ D u := fun u =>
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hf.analyticAt w) u
    have hfib : ∀ w ∈ T.image z, ((T.filter fun n => z n = w).card : ℤ) ≤ D w := by
      intro w hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
      have hmem : z n ∈ closedBall (0 : ℂ) r := by
        simpa [hT, dist_eq_norm] using (Finset.mem_filter.mp hn).2
      rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply (fun w _ => hf.analyticAt w) hmem]
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hfin (z n))
      rw [← hm]
      have hle : (((T.filter fun k => z k = z n).card : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
        rw [hm, ← hz (z n)]
        rw [← Set.encard_coe_eq_coe_finsetCard]
        refine (Set.encard_le_encard (t := {k | z k = z n}) ?_).trans_eq ?_
        · intro k hk
          simpa using (Finset.mem_filter.mp hk).2
        · rfl
      have hle' : (T.filter fun k => z k = z n).card ≤ m := by exact_mod_cast hle
      simp only [ENat.map_natCast, WithTop.untop₀_coe]
      exact_mod_cast hle'
    have hsum : (T.card : ℤ) ≤ ∑ w ∈ T.image z, D w := by
      rw [Finset.card_eq_sum_card_image z T]
      push_cast
      exact Finset.sum_le_sum hfib
    have hsupp := D.finiteSupport (isCompact_closedBall (0 : ℂ) r)
    have hfs : (∑ᶠ u, D u) = ∑ u ∈ hsupp.toFinset ∪ T.image z, D u :=
      finsum_eq_sum_of_support_subset _ (by
        intro u hu
        simp only [Finset.coe_union, Set.Finite.coe_toFinset]
        exact Or.inl hu)
    have : (T.card : ℤ) ≤ ∑ᶠ u, D u := by
      rw [hfs]
      exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun u _ _ => hDnn u))
    exact_mod_cast this
  -- `n(r) ≤ L r ^ (ρ + ε / 2)` for `r ≥ r₀`
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set p := ρ + δ with hp
  have hp0 : 0 < p := by positivity
  obtain ⟨K, hK⟩ := (h.isBigO_sum_divisor_closedBall hρ hδ0).bound
  rw [eventually_atTop] at hK
  obtain ⟨R1, hR1⟩ := hK
  set R := max R1 r₀ with hR
  have hR0 : 0 < R := lt_of_lt_of_le hr₀ (le_max_right _ _)
  set L := |K| * (1 + R / r₀) ^ p with hL
  have hN : ∀ (t : Finset ι) (r : ℝ), r₀ ≤ r →
      ((t.filter fun n => ‖z n‖ ≤ r).card : ℝ) ≤ L * r ^ p := by
    intro t r hr
    have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
    have h1 : ((t.filter fun n => ‖z n‖ ≤ r).card : ℝ) ≤
        ((t.filter fun n => ‖z n‖ ≤ r + R).card : ℝ) := by
      refine Nat.cast_le.mpr (Finset.card_le_card fun n hn => ?_)
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, by linarith [hn.2]⟩
    have h2 := hR1 (r + R) (by linarith [le_max_left R1 r₀])
    have hrR : 0 ≤ (r + R) ^ p := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg hrR] at h2
    have h3 : r + R ≤ (1 + R / r₀) * r := by
      have : R ≤ R / r₀ * r := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr₀]
        nlinarith
      linarith
    have h4 : (r + R) ^ p ≤ (1 + R / r₀) ^ p * r ^ p := by
      rw [← Real.mul_rpow (by positivity) hr0.le]
      exact Real.rpow_le_rpow (by linarith) h3 hp0.le
    calc ((t.filter fun n => ‖z n‖ ≤ r).card : ℝ)
        ≤ ((t.filter fun n => ‖z n‖ ≤ r + R).card : ℝ) := h1
      _ ≤ _ := hcount t _
      _ ≤ ‖((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 (r + R)) u : ℤ) : ℝ)‖ :=
          Real.le_norm_self _
      _ ≤ K * (r + R) ^ p := h2
      _ ≤ |K| * (r + R) ^ p := by gcongr; exact le_abs_self K
      _ ≤ |K| * ((1 + R / r₀) ^ p * r ^ p) := by gcongr
      _ = L * r ^ p := by rw [hL]; ring
  -- dyadic shells `r₀ 2^k ≤ ‖z n‖ ≤ r₀ 2^(k+1)`
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set kf : ι → ℕ := fun n => ⌊Real.log (‖z n‖ / r₀) / Real.log 2⌋₊ with hkf
  have hx1 : ∀ n, 1 ≤ ‖z n‖ / r₀ := fun n => by rw [le_div_iff₀ hr₀]; linarith [hr₀z n]
  have hexp : ∀ n, ‖z n‖ / r₀ = (2 : ℝ) ^ (Real.log (‖z n‖ / r₀) / Real.log 2) := by
    intro n
    rw [Real.rpow_def_of_pos two_pos, mul_div_cancel₀ _ hl2.ne',
      Real.exp_log (by linarith [hx1 n])]
  have hlo : ∀ n, r₀ * (2 : ℝ) ^ (kf n : ℝ) ≤ ‖z n‖ := by
    intro n
    have h := Nat.floor_le (div_nonneg (Real.log_nonneg (hx1 n)) hl2.le)
    have h' : (2 : ℝ) ^ (kf n : ℝ) ≤ ‖z n‖ / r₀ := by
      rw [hexp n]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two h
    rw [le_div_iff₀ hr₀] at h'
    linarith
  have hhi : ∀ n, ‖z n‖ ≤ r₀ * (2 : ℝ) ^ ((kf n : ℝ) + 1) := by
    intro n
    have h := Nat.lt_floor_add_one (Real.log (‖z n‖ / r₀) / Real.log 2)
    have h' : ‖z n‖ / r₀ ≤ (2 : ℝ) ^ ((kf n : ℝ) + 1) := by
      rw [hexp n]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two h.le
    rw [div_le_iff₀ hr₀] at h'
    linarith
  set q : ℝ := (2 : ℝ) ^ (-δ) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set A := L * 2 ^ p * r₀ ^ (-δ) with hA
  have hshell : ∀ (s : Finset ι) (k : ℕ),
      ∑ n ∈ s.filter (fun n => kf n = k), ‖z n‖ ^ (-ρ - ε) ≤ A * q ^ k := by
    intro s k
    have hb0 : 0 < r₀ * (2 : ℝ) ^ (k : ℝ) := by positivity
    have hterm : ∀ n ∈ s.filter (fun n => kf n = k),
        ‖z n‖ ^ (-ρ - ε) ≤ (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) := by
      intro n hn
      have hk := (Finset.mem_filter.mp hn).2
      have := hlo n
      rw [hk] at this
      exact Real.rpow_le_rpow_of_nonpos hb0 this (by linarith)
    have hcard : ((s.filter (fun n => kf n = k)).card : ℝ) ≤
        L * (r₀ * (2 : ℝ) ^ ((k : ℝ) + 1)) ^ p := by
      refine le_trans ?_ (hN s _ ?_)
      · refine Nat.cast_le.mpr (Finset.card_le_card fun n hn => ?_)
        have hk := (Finset.mem_filter.mp hn).2
        have := hhi n
        rw [hk] at this
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, this⟩
      · have : (1 : ℝ) ≤ 2 ^ ((k : ℝ) + 1) := Real.one_le_rpow one_le_two (by positivity)
        nlinarith
    have hc0 : 0 ≤ (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) := by positivity
    have e : L * (r₀ * (2 : ℝ) ^ ((k : ℝ) + 1)) ^ p * (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) =
        A * q ^ k := by
      have h2 : (0 : ℝ) ≤ 2 := by norm_num
      rw [Real.mul_rpow hr₀.le (by positivity), Real.mul_rpow hr₀.le (by positivity),
        ← Real.rpow_mul h2, ← Real.rpow_mul h2]
      calc L * (r₀ ^ p * 2 ^ (((k : ℝ) + 1) * p)) * (r₀ ^ (-ρ - ε) * 2 ^ ((k : ℝ) * (-ρ - ε)))
          = L * (r₀ ^ p * r₀ ^ (-ρ - ε)) *
              (2 ^ (((k : ℝ) + 1) * p) * 2 ^ ((k : ℝ) * (-ρ - ε))) := by
            ring
        _ = L * r₀ ^ (p + (-ρ - ε)) * 2 ^ (((k : ℝ) + 1) * p + (k : ℝ) * (-ρ - ε)) := by
            rw [← Real.rpow_add hr₀, ← Real.rpow_add two_pos]
        _ = L * r₀ ^ (-δ) * 2 ^ (p + -δ * (k : ℝ)) := by
            rw [show p + (-ρ - ε) = -δ by rw [hp, hδ]; ring,
              show ((k : ℝ) + 1) * p + (k : ℝ) * (-ρ - ε) = p + -δ * (k : ℝ) by
                rw [hp, hδ]; ring]
        _ = A * q ^ k := by
            rw [Real.rpow_add two_pos, Real.rpow_mul h2, Real.rpow_natCast, hA, hq]
            ring
    calc ∑ n ∈ s.filter (fun n => kf n = k), ‖z n‖ ^ (-ρ - ε)
        ≤ ∑ n ∈ s.filter (fun n => kf n = k), (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) :=
          Finset.sum_le_sum hterm
      _ = ((s.filter (fun n => kf n = k)).card : ℝ) * (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ L * (r₀ * (2 : ℝ) ^ ((k : ℝ) + 1)) ^ p * (r₀ * (2 : ℝ) ^ (k : ℝ)) ^ (-ρ - ε) := by
          gcongr
      _ = A * q ^ k := e
  have hA0 : 0 ≤ A := by rw [hA, hL]; positivity
  refine summable_of_sum_le (c := ∑' k, A * q ^ k)
    (fun n => Real.rpow_nonneg (norm_nonneg _) _) ?_
  intro u
  rw [← Finset.sum_fiberwise_of_maps_to (g := kf) (t := u.image kf)
    (fun n hn => Finset.mem_image_of_mem kf hn)]
  calc ∑ k ∈ u.image kf, ∑ n ∈ u.filter (fun n => kf n = k), ‖z n‖ ^ (-ρ - ε)
      ≤ ∑ k ∈ u.image kf, A * q ^ k := Finset.sum_le_sum fun k _ => hshell u k
    _ ≤ ∑' k, A * q ^ k := Summable.sum_le_tsum _ (fun k _ => by positivity)
        ((summable_geometric_of_lt_one hq0 hq1).mul_left A)

end Complex.Hadamard.EntireOfOrderAtMost
