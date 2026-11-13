/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall

/-!
# Invariant regions of ordinary differential equations

Linear invariants of `x' = F x`, the boundary sign of mass-action kinetics, forward invariance
of the nonnegative orthant, and explicit solutions of scalar and diagonal linear equations.

## i. Overview

The state space is `ι → ℝ` for a finite species type `ι`, with its sup norm, and a vector field
is a map `F : (ι → ℝ) → ι → ℝ`. Throughout, `x : ℝ → ι → ℝ` is a *solution of `x' = F x` on
`I : Set ℝ`* if `∀ t ∈ I, HasDerivAt x (F (x t)) t`. Intervals are convex sets `I`
(`Convex ℝ I`); no nondegeneracy of `I` is needed. Explicit solutions are solutions on all of
`ℝ`, that is, `∀ t, HasDerivAt x (F (x t)) t`.

- *Linear invariants.* If `∑ i, w i * F y i = 0` for every state `y`, the weighted total
  `t ↦ ∑ i, w i * x t i` has derivative `∑ i, w i * F (x t) i = 0`, so it is constant on `I` by
  the mean value inequality on a convex set.
- *Mass action.* For stoichiometric coefficients `N : ι → J → ℤ`, reactant exponents
  `α : J → ι → ℕ` and rate constants `k : J → ℝ` with `k ≥ 0`, the field is
  `F y i = ∑ j, N i j * (k j * ∏ s, y s ^ α j s)`. Suppose that every reaction that consumes a
  species has that species among its reactants: `N s j < 0 → 1 ≤ α j s` for all `s` and `j`.
  Then `F y i ≥ 0` whenever `y ≥ 0` and `y i = 0`. This *boundary-sign* property alone does not
  show that solutions stay in the nonnegative orthant. The networks of
  `MathlibExt.Biology.Dynamics.ComplexBalanced` are a special case; see `massActionField`.
- *Orthant invariance.* For a locally Lipschitz field with the boundary-sign property, Gronwall's
  inequality for `t ↦ ∑ i, min (x t i) 0 ^ 2` shows that a solution which is nonnegative at
  `t₀ ∈ I` stays nonnegative at all later times of `I`. Mass-action fields are smooth, hence
  locally Lipschitz, so this applies to them.
- *Explicit solutions.* `t ↦ x₀ * exp (a * t)` solves `x' = a * x` with `x 0 = x₀`, and
  `t ↦ fun i => x₀ i * exp (d i * t)` solves the diagonal system `x' i = d i * x i` with
  `x 0 = x₀`. If `d i ≤ -c` for all `i`, then `|x t i| ≤ |x₀ i| * exp (-c * t)` for `t ≥ 0`.
  The two diagonal lemmas hold for every index type `ι`; for infinite `ι`, `HasDerivAt` refers
  to the product topology on `ι → ℝ`.

The differential equation is an assumed model. Local existence and uniqueness are not proved
here; Mathlib and ATLAS provide them (see the references). Mathlib's Picard–Lindelöf theorem
gives `HasDerivWithinAt` on `Icc tmin tmax`, so its solution is a solution in the above sense on
`Ioo tmin tmax`. A local solution need not exist for all time (the solution `1 / (1 - t)` of
`x' = x ^ 2`, `x 0 = 1`, blows up at `t = 1`), and polynomial reaction fields are locally
Lipschitz but in general not globally Lipschitz. Exponential stability for general
(non-diagonal) Hurwitz matrices is not proved here either.

## ii. Key results

- `MetaMathlibExt.linear_invariant_of_hasDerivAt`: a linear invariant is constant along
  solutions.
- `MetaMathlibExt.massActionField`: the mass-action vector field.
- `MetaMathlibExt.massActionField_nonneg_of_eq_zero`: the boundary sign of mass action.
- `MetaMathlibExt.contDiff_massActionField`: the mass-action field is smooth.
- `MetaMathlibExt.orthant_invariant_of_boundary_nonneg`: forward invariance of the nonnegative
  orthant for locally Lipschitz fields with the boundary-sign property.
- `MetaMathlibExt.massActionField_orthant_invariant`: forward invariance of the nonnegative
  orthant for mass action.
- `MetaMathlibExt.scalar_exp_solution`, `MetaMathlibExt.diagonal_exp_solution`: explicit
  exponential solutions.
- `MetaMathlibExt.scalar_exp_solution_abs_le`, `MetaMathlibExt.diagonal_exp_solution_abs_le`:
  exponential decay bounds.

## iii. Table of contents

- A. Linear invariants
- B. Mass-action kinetics and the boundary sign
- C. Forward invariance of the nonnegative orthant
- D. Explicit exponential solutions and decay

## iv. References

- Mass-action kinetics: F. Horn and R. Jackson, "General mass action kinetics", Arch. Rational
  Mech. Anal. 47 (1972) 81–116; M. Feinberg, *Foundations of Chemical Reaction Network Theory*,
  Springer (2019).
- Local existence and uniqueness, not reproved here. Mathlib `Mathlib.Analysis.ODE.ExistUnique`:
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`, `ODE_solution_unique` and
  `ODE_solution_unique_univ`. ATLAS:
  `MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz` (global
  existence and uniqueness for continuous, globally Lipschitz fields),
  `MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact` (maximal
  solutions for locally Lipschitz fields) and `MathlibExt.Analysis.ODE.PicardIteration`
  (convergence of Picard iterates for globally Lipschitz fields).
- Hurwitz matrices, not reproved here. ATLAS `MathlibExt.Analysis.ODE.LinearizedStability`:
  `Matrix.IsHurwitz.exists_norm_exp_smul_mulVec_le` (exponential bound for `exp (t • A)`) and
  `MathlibExt.Analysis.ODE.LinearizedStability.globalSolution_decay_of_hasFDerivAt` (conditional
  exponential decay of global solutions near an equilibrium with Hurwitz Jacobian).
- Mathlib lemmas used in the proofs: `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`,
  `le_gronwallBound_of_liminf_deriv_right_le`, `ContDiff.locallyLipschitz`,
  `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`, `Finset.prod_eq_zero`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open scoped Topology

/-! ## A. Linear invariants -/

/-- **Linear invariants.** If the weight vector `w` annihilates the vector field,
`∑ i, w i * F y i = 0` for every state `y`, then along every solution of `x' = F x` on a convex
set `I` the weighted total `∑ i, w i * x t i` takes the same value at any two times of `I`. -/
lemma linear_invariant_of_hasDerivAt {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ι → ℝ}
    {w : ι → ℝ} (hw : ∀ y, ∑ i, w i * F y i = 0) {I : Set ℝ} (hI : Convex ℝ I)
    {x : ℝ → ι → ℝ} (hx : ∀ t ∈ I, HasDerivAt x (F (x t)) t) :
    ∀ t₁ ∈ I, ∀ t₂ ∈ I, ∑ i, w i * x t₁ i = ∑ i, w i * x t₂ i := by
  intro t₁ ht₁ t₂ ht₂
  have hderiv : ∀ t ∈ I, HasDerivWithinAt (fun s => ∑ i, w i * x s i) 0 I t := by
    intro t ht
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (hasDerivAt_pi.1 (hx t ht) i).const_mul (w i)
    rw [hw (x t)] at h
    exact h.hasDerivWithinAt
  have h := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f' := fun _ => (0 : ℝ)) (C := 0)
    hderiv (fun _ _ => by simp) ht₂ ht₁
  rwa [zero_mul, norm_le_zero_iff, sub_eq_zero] at h

/-! ## B. Mass-action kinetics and the boundary sign -/

/-- The mass-action vector field `F y i = ∑ j, N i j * (k j * ∏ s, y s ^ α j s)` of a reaction
network with species `ι` and reactions `J`: `N i j` is the net change of species `i` in reaction
`j`, `α j s` is the exponent of species `s` in the rate of reaction `j`, and `k j` is the rate
constant of reaction `j`.

For a network with reactant and product complexes `src` and `prod`, the choice
`N s j = prod j s - src j s`, `α = src` gives the field
`MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork.massActionField`, and this choice
always satisfies the compatibility condition of `massActionField_nonneg_of_eq_zero`. -/
def massActionField {ι J : Type*} [Fintype ι] [Fintype J] (N : ι → J → ℤ)
    (α : J → ι → ℕ) (k : J → ℝ) (y : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, (N i j : ℝ) * (k j * ∏ s, y s ^ α j s)

/-- **Boundary sign of mass-action kinetics.** Let the rate constants be nonnegative, and let
every reaction that consumes a species have that species among its reactants:
`N s j < 0 → 1 ≤ α j s` for all `s` and `j`. If `y ≥ 0` and `y i = 0`, then `0 ≤ F y i` for the
mass-action field `F`.

This is the boundary-sign property only. By itself it does not show that solutions stay in the
nonnegative orthant: that needs a solution together with a first-exit-time or comparison
argument, which is `massActionField_orthant_invariant`. -/
lemma massActionField_nonneg_of_eq_zero {ι J : Type*} [Fintype ι] [Fintype J]
    {N : ι → J → ℤ} {α : J → ι → ℕ} {k : J → ℝ} (hk : ∀ j, 0 ≤ k j)
    (hcompat : ∀ i j, N i j < 0 → 1 ≤ α j i) {y : ι → ℝ} (hy : ∀ s, 0 ≤ y s) {i : ι}
    (hi : y i = 0) : 0 ≤ massActionField N α k y i := by
  refine Finset.sum_nonneg fun j _ => ?_
  rcases lt_or_ge (N i j) 0 with hN | hN
  · have hpow : y i ^ α j i = 0 := by
      rw [hi]
      exact zero_pow (Nat.one_le_iff_ne_zero.1 (hcompat i j hN))
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hpow, mul_zero, mul_zero]
  · exact mul_nonneg (by exact_mod_cast hN)
      (mul_nonneg (hk j) (Finset.prod_nonneg fun s _ => pow_nonneg (hy s) _))

/-- The mass-action vector field is `C^n` for every `n`, since each component is a polynomial in
the state. In particular it is locally Lipschitz (`ContDiff.locallyLipschitz`); in general it is
not globally Lipschitz. -/
lemma contDiff_massActionField {ι J : Type*} [Fintype ι] [Fintype J] (N : ι → J → ℤ)
    (α : J → ι → ℕ) (k : J → ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (massActionField N α k) := by
  refine contDiff_pi.2 fun i => ?_
  unfold massActionField
  fun_prop

/-! ## C. Forward invariance of the nonnegative orthant -/

/-- `v ↦ min v 0 ^ 2` has derivative `2 * min u 0` at every `u`. -/
private lemma hasDerivAt_min_zero_sq (u : ℝ) :
    HasDerivAt (fun v : ℝ => min v 0 ^ 2) (2 * min u 0) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have heq : (fun v : ℝ => min v 0 ^ 2) =ᶠ[𝓝 u] fun v => v ^ 2 := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      rw [min_eq_left hv.le]
    rw [min_eq_left hu.le]
    exact ((hasDerivAt_pow 2 u).congr_of_eventuallyEq heq).congr_deriv (by norm_num)
  · rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h => ?_))
      |>.trans_isLittleO (Asymptotics.isLittleO_pow_id (n := 2) (by norm_num))
    rcases le_total h 0 with hh | hh
    · simp [min_eq_left hh]
    · simp [min_eq_right hh, sq_nonneg]
  · have heq : (fun v : ℝ => min v 0 ^ 2) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      simp [min_eq_right (Set.mem_Ioi.1 hv).le]
    rw [min_eq_right hu.le, mul_zero]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq heq

/-- The square of the sup norm of `v : ι → ℝ` is at most `∑ i, v i ^ 2`. -/
private lemma norm_sq_le_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
  have h0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hle : ‖v‖ ≤ √(∑ i, v i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.le_sqrt (norm_nonneg _) h0, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  calc ‖v‖ ^ 2 ≤ √(∑ i, v i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hle 2
    _ = ∑ i, v i ^ 2 := Real.sq_sqrt h0

/-- **Forward invariance of the nonnegative orthant.** Let `F` be locally Lipschitz with the
boundary-sign property: `0 ≤ F y i` whenever `y ≥ 0` and `y i = 0`. If `x` solves `x' = F x` on
a convex set `I` and `x t₀ ≥ 0` componentwise for some `t₀ ∈ I`, then `x t ≥ 0` componentwise
for every `t ∈ I` with `t₀ ≤ t`.

The proof applies Gronwall's inequality to `s ↦ ∑ i, min (x s i) 0 ^ 2` on `[t₀, t]`, with a
Lipschitz constant of `F` on a closed ball that contains the trajectory and its positive
part. -/
lemma orthant_invariant_of_boundary_nonneg {ι : Type*} [Fintype ι]
    {F : (ι → ℝ) → ι → ℝ} (hF : LocallyLipschitz F)
    (hbd : ∀ y : ι → ℝ, (∀ s, 0 ≤ y s) → ∀ i, y i = 0 → 0 ≤ F y i)
    {I : Set ℝ} (hI : Convex ℝ I) {x : ℝ → ι → ℝ} (hx : ∀ t ∈ I, HasDerivAt x (F (x t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h₀ : ∀ i, 0 ≤ x t₀ i) :
    ∀ t ∈ I, t₀ ≤ t → ∀ i, 0 ≤ x t i := by
  intro t ht htt i
  have hD : Set.Icc t₀ t ⊆ I := hI.ordConnected.out ht₀ ht
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun s hs => (hx s (hD hs)).continuousAt.continuousWithinAt : ContinuousOn x (Set.Icc t₀ t))
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : ι → ℝ) R) hF.locallyLipschitzOn
  -- Compare `F y` with `F` at the positive part `y - min y 0`, where the boundary sign applies.
  have key : ∀ y ∈ Metric.closedBall (0 : ι → ℝ) R, ∀ j, y j < 0 →
      -F y j ≤ L * ‖fun s => min (y s) 0‖ := by
    intro y hy j hj
    have hp_mem : (fun s => y s - min (y s) 0) ∈ Metric.closedBall (0 : ι → ℝ) R := by
      rw [mem_closedBall_zero_iff] at hy ⊢
      refine le_trans ((pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun s => ?_) hy
      refine le_trans ?_ (norm_le_pi_norm y s)
      rcases le_total (y s) 0 with h | h
      · simp [min_eq_left h]
      · simp [min_eq_right h]
    have h1 := hbd (fun s => y s - min (y s) 0) (fun s => sub_nonneg.2 (min_le_left _ _)) j
      (by simp [min_eq_left hj.le])
    have h2 : |F (fun s => y s - min (y s) 0) j - F y j| ≤
        ‖F (fun s => y s - min (y s) 0) - F y‖ := by
      simpa using norm_le_pi_norm (F (fun s => y s - min (y s) 0) - F y) j
    have h3 := hL.norm_sub_le hp_mem hy
    have h4 : ((fun s => y s - min (y s) 0) - y) = -fun s => min (y s) 0 := by
      funext s
      simp
    rw [h4, norm_neg] at h3
    linarith [le_abs_self (F (fun s => y s - min (y s) 0) j - F y j)]
  have hφ : ∀ s ∈ Set.Icc t₀ t, HasDerivAt (fun r => ∑ j, min (x r j) 0 ^ 2)
      (∑ j, 2 * min (x s j) 0 * F (x s) j) s := by
    intro s hs
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact (hasDerivAt_min_zero_sq (x s j)).comp s (hasDerivAt_pi.1 (hx s (hD hs)) j)
  have hbound : ∀ s ∈ Set.Ico t₀ t, ∑ j, 2 * min (x s j) 0 * F (x s) j ≤
      (2 * L * Fintype.card ι) * ∑ j, min (x s j) 0 ^ 2 + 0 := by
    intro s hs
    have hmem : x s ∈ Metric.closedBall (0 : ι → ℝ) R :=
      mem_closedBall_zero_iff.2 (hR s (Set.Ico_subset_Icc_self hs))
    have hterm : ∀ j, 2 * min (x s j) 0 * F (x s) j ≤
        2 * L * ‖fun r => min (x s r) 0‖ ^ 2 := by
      intro j
      rcases le_or_gt 0 (x s j) with hj | hj
      · rw [min_eq_right hj, mul_zero, zero_mul]
        positivity
      · have hk := key (x s) hmem j hj
        have hmj := norm_le_pi_norm (fun r => min (x s r) 0) j
        rw [Real.norm_eq_abs, min_eq_left hj.le, abs_of_neg hj] at hmj
        rw [min_eq_left hj.le]
        have hL0 : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
        nlinarith [mul_nonneg (neg_nonneg.2 hj.le) (sub_nonneg.2 hk),
          mul_nonneg (sub_nonneg.2 hmj) (mul_nonneg hL0 (norm_nonneg (fun r => min (x s r) 0)))]
    calc ∑ j, 2 * min (x s j) 0 * F (x s) j
        ≤ ∑ _j : ι, 2 * L * ‖fun r => min (x s r) 0‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = Fintype.card ι * (2 * L * ‖fun r => min (x s r) 0‖ ^ 2) := by simp
      _ ≤ Fintype.card ι * (2 * L * ∑ j, min (x s j) 0 ^ 2) := by
        gcongr
        exact norm_sq_le_sum_sq _
      _ = (2 * L * Fintype.card ι) * ∑ j, min (x s j) 0 ^ 2 + 0 := by ring
  have hgr := le_gronwallBound_of_liminf_deriv_right_le
    (fun s hs => (hφ s hs).continuousAt.continuousWithinAt)
    (fun s hs r hr => ((hφ s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt.liminf_right_slope_le
      hr).mono fun z hz => by rwa [slope_def_field, div_eq_inv_mul] at hz)
    (le_of_eq (Finset.sum_eq_zero fun j _ => by rw [min_eq_right (h₀ j)]; norm_num)) hbound
    t ⟨htt, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at hgr
  have hsum : ∑ j, min (x t j) 0 ^ 2 = 0 :=
    le_antisymm hgr (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (min (x t j) 0)).1 hsum i
    (Finset.mem_univ i)
  exact min_eq_right_iff.1 ((pow_eq_zero_iff two_ne_zero).1 hi)

/-- **Mass-action kinetics preserves the nonnegative orthant.** Under the hypotheses of
`massActionField_nonneg_of_eq_zero` (nonnegative rate constants, and `α j i ≥ 1` whenever
`N i j < 0`), a solution of `x' = F x` on a convex set `I` that is nonnegative at some
`t₀ ∈ I` is nonnegative at every `t ∈ I` with `t₀ ≤ t`. The existence of solutions is not
asserted. -/
lemma massActionField_orthant_invariant {ι J : Type*} [Fintype ι] [Fintype J]
    {N : ι → J → ℤ} {α : J → ι → ℕ} {k : J → ℝ} (hk : ∀ j, 0 ≤ k j)
    (hcompat : ∀ i j, N i j < 0 → 1 ≤ α j i) {I : Set ℝ} (hI : Convex ℝ I)
    {x : ℝ → ι → ℝ} (hx : ∀ t ∈ I, HasDerivAt x (massActionField N α k (x t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h₀ : ∀ i, 0 ≤ x t₀ i) :
    ∀ t ∈ I, t₀ ≤ t → ∀ i, 0 ≤ x t i :=
  orthant_invariant_of_boundary_nonneg (contDiff_massActionField N α k).locallyLipschitz
    (fun _ hy _ hi => massActionField_nonneg_of_eq_zero hk hcompat hy hi) hI hx ht₀ h₀

/-! ## D. Explicit exponential solutions and decay -/

/-- **Scalar exponential solution.** If `x t = x₀ * exp (a * t)` for all `t`, then `x` solves
the initial value problem `x' = a * x`, `x 0 = x₀`, on all of `ℝ`. -/
lemma scalar_exp_solution {x : ℝ → ℝ} {a x₀ : ℝ} (hx : ∀ t, x t = x₀ * Real.exp (a * t)) :
    x 0 = x₀ ∧ ∀ t, HasDerivAt x (a * x t) t := by
  refine ⟨by rw [hx, mul_zero, Real.exp_zero, mul_one], fun t => ?_⟩
  rw [hx t, show x = fun t => x₀ * Real.exp (a * t) from funext hx]
  exact (((hasDerivAt_id' t).const_mul a).exp.const_mul x₀).congr_deriv (by ring)

/-- **Decay of the scalar exponential solution.** If `x t = x₀ * exp (a * t)` for all `t` and
`a ≤ -c`, then `|x t| ≤ |x₀| * exp (-c * t)` for every `t ≥ 0`. For `c > 0` this is exponential
decay at rate `c`. -/
lemma scalar_exp_solution_abs_le {x : ℝ → ℝ} {a c x₀ : ℝ}
    (hx : ∀ t, x t = x₀ * Real.exp (a * t)) (ha : a ≤ -c) {t : ℝ} (ht : 0 ≤ t) :
    |x t| ≤ |x₀| * Real.exp (-c * t) := by
  rw [hx, abs_mul, Real.abs_exp]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ha ht))
    (abs_nonneg x₀)

/-- **Diagonal linear system.** If `x t i = x₀ i * exp (d i * t)` for all `t` and `i`, then `x`
solves the diagonal system `x' i = d i * x i`, that is `HasDerivAt x (fun i => d i * x t i) t`
for every `t`, with `x 0 = x₀`. -/
lemma diagonal_exp_solution {ι : Type*} {x : ℝ → ι → ℝ} {d x₀ : ι → ℝ}
    (hx : ∀ t i, x t i = x₀ i * Real.exp (d i * t)) :
    x 0 = x₀ ∧ ∀ t, HasDerivAt x (fun i => d i * x t i) t :=
  ⟨funext fun i => (scalar_exp_solution (x := fun s => x s i) (hx · i)).1,
    fun t => hasDerivAt_pi.2 fun i => (scalar_exp_solution (x := fun s => x s i) (hx · i)).2 t⟩

/-- **Decay for a negative diagonal.** If `x t i = x₀ i * exp (d i * t)` for all `t` and `i`, and
`d i ≤ -c` for every `i`, then `|x t i| ≤ |x₀ i| * exp (-c * t)` for every `t ≥ 0` and every
`i`. For `c > 0` this is exponential decay at rate `c`. -/
lemma diagonal_exp_solution_abs_le {ι : Type*} {x : ℝ → ι → ℝ} {d x₀ : ι → ℝ} {c : ℝ}
    (hx : ∀ t i, x t i = x₀ i * Real.exp (d i * t)) (hd : ∀ i, d i ≤ -c) {t : ℝ} (ht : 0 ≤ t)
    (i : ι) : |x t i| ≤ |x₀ i| * Real.exp (-c * t) :=
  scalar_exp_solution_abs_le (x := fun s => x s i) (hx · i) (hd i) ht

end MetaMathlibExt
