/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Lipschitz
public import MathlibExt.Probability.FiniteProbability

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import PhyslibExt.Chemistry.Uncertainty.Propagation

/-!
# Uncertainty propagation for finite models, Jacobians, Lipschitz maps and calibration

Exact affine covariance propagation on finite sample spaces, first-order Jacobian
propagation with an explicit remainder bound, deterministic Lipschitz error bounds, and
linear calibration identifiability.

## i. Overview

The finite probability model is that of `MathlibExt.Probability.FiniteProbability`: a finite
sample space `Ω` with `[Fintype Ω]` and a weight `p : Ω → ℝ`, a finite distribution when
`∀ ω, 0 ≤ p ω` and `∑ ω, p ω = 1`. Both conditions are explicit hypotheses where they are
used, never derived facts: error distributions and covariances are INPUTS. Expectations are
`FiniteProbability.expectation` and covariance matrices are `FiniteProbability.covMatrix`,
used directly; no measure theory is used.

Section A proves exact covariance propagation for affine maps on top of that API: the mean
law `meanVec p (A *ᵥ X · + b) = A *ᵥ meanVec p X + b` for the coordinate-wise mean
`meanVec`, and `covMatrix p (A *ᵥ X · + b) = A * covMatrix p X * Aᵀ`, whose linear part is
`FiniteProbability.covMatrix_mulVec`. The correlated two-input consequence carries the
explicit cross term `2 a₁ a₂ Cov(X₁, X₂)`. Quadrature (addition in quadrature) is proved only
as a SPECIAL case under zero cross-covariance, never as the general law.

Section B treats Jacobian propagation as what it is: an APPROXIMATION. The first-order
value is `f x + fderiv ℝ f x δ`, the remainder `jacobianRemainder f x δ` is bounded, not
zero. The scalar bound reuses Mathlib's Lagrange remainder
`taylor_mean_remainder_lagrange_iteratedDeriv`. The vector bounds are componentwise. Two of
them bound the second derivative of the one-variable segment function
`φᵢ t = f i (x + t • δ)`: by `H i` (`jacobianRemainder_component_le`, conclusion `H i / 2`)
or by `H i * ‖δ‖ ^ 2` (`jacobianRemainder_component_le_of_scaled`, conclusion
`H i / 2 * ‖δ‖ ^ 2`). The third, `jacobianRemainder_component_le_of_hessian`, assumes a
bound `H i` on the operator norm of the second Fréchet derivative of `f i` on a box and
concludes `H i / 2 * ‖δ‖ ^ 2`; it instantiates
`Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le`.

Section C proves deterministic Lipschitz error propagation: the basic bound, its
error-budget form, and the affine map as an exact special case. Composition of Lipschitz
constants is Mathlib's `LipschitzWith.comp`. Any Lipschitz bound for an affine map is a
consequence of the exact equality, not the sharp statement.

Section D treats linear calibration `y = A *ᵥ θ`: identifiability as injectivity of
`θ ↦ A *ᵥ θ` (linear-algebraic, distinct from statistical `IsIdentifiedBy`), its trivial
kernel characterization, non-uniqueness from any nonzero kernel vector, rank deficiency
(`m < n`) implying non-identifiability, and injectivity of the normal matrix with at
most one normal-equations solution. Unique-estimate claims are PROHIBITED without
identifiability.

Instrument resolution, systematic bias and sampling variance are different
uncertainties; they enter only as separate hypotheses and inputs, never conflated.

## ii. Key results

- `meanVec` : the coordinate-wise finite mean of a random vector.
- `meanVec_affine` : exact affine mean law (needs total mass one).
- `covMatrix_affine` : exact affine covariance propagation `A * C * Aᵀ` (needs total mass one).
- `covMatrix_two_linear` : correlated two-input variance with the explicit cross term.
- `variance_linear_two_uncorrelated` : quadrature as a special case only.
- `taylor_first_order_bound` : scalar first-order remainder `H / 2 * δ ^ 2`.
- `jacobianRemainder` : the (nonzero in general) first-order remainder.
- `jacobianRemainder_component_le(_of_scaled)` : componentwise bounds from bounds along the
  segment.
- `jacobianRemainder_component_le_of_hessian` : componentwise bound from a Hessian bound.
- `lipschitz_error_propagation`, `lipschitz_error_budget` : Lipschitz error bounds.
- `affine_exact` : the affine map is exact, not merely Lipschitz.
- `Identifiable`, `identifiable_iff_trivial_ker` : calibration identifiability.
- `exists_distinct_of_nontrivial_ker` : nonzero kernel vector kills uniqueness.
- `not_identifiable_of_lt` : wide matrices are not identifiable.
- `identifiable_normal_injective`, `normalEquations_unique` : normal-matrix injectivity.

## iii. Table of contents

- A. Finite means and exact affine covariance propagation
- B. Jacobian propagation as a first-order approximation
- C. Deterministic Lipschitz error propagation
- D. Rank-deficient calibration and parameter identification

## iv. References

- JCGM 100:2008, *Guide to the Expression of Uncertainty in Measurement* (GUM), law of
  propagation of uncertainty (first-order approximation for nonlinear functions).
- Mathlib's Taylor theorem with Lagrange remainder,
  `taylor_mean_remainder_lagrange_iteratedDeriv` in `Mathlib.Analysis.Calculus.Taylor`.
- `MathlibExt.Probability.FiniteProbability` (finite expectation and covariance matrices).
- `Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le` (first-order remainder
  from a second-derivative bound).
-/

@[expose] public section

open scoped BigOperators
open Matrix MathlibExt.Probability.FiniteProbability

namespace Statistics.UncertaintyPropagation

/-! ## A. Finite means and exact affine covariance propagation -/

/-- The coordinate-wise finite mean of a random vector `X : Ω → Fin n → ℝ`: coordinate `i`
is the expectation `FiniteProbability.expectation p (X · i)`. For a finite distribution
(`0 ≤ p`, `∑ ω, p ω = 1`) this is the mean vector of `X`; the distribution conditions are
hypotheses of the lemmas below, not part of the definition. -/
noncomputable def meanVec {Ω : Type*} [Fintype Ω] {n : ℕ} (p : Ω → ℝ)
    (X : Ω → Fin n → ℝ) : Fin n → ℝ :=
  fun i => expectation p (fun ω => X ω i)

/-- Unfolding a vector-mean coordinate. -/
lemma meanVec_apply {Ω : Type*} [Fintype Ω] {n : ℕ} (p : Ω → ℝ) (X : Ω → Fin n → ℝ)
    (i : Fin n) :
    meanVec p X i = expectation p (fun ω => X ω i) :=
  rfl

/-- **Affine mean law**, exact: the mean of `A *ᵥ X ω + b` is `A *ᵥ meanVec p X + b`.
The `+ b` part needs total mass one (`expectation_const`); without `hp1` the constant shift
is scaled by the total mass instead. -/
lemma meanVec_affine {Ω : Type*} [Fintype Ω] {m n : ℕ} (p : Ω → ℝ)
    (X : Ω → Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hp1 : ∑ ω, p ω = 1) :
    meanVec p (fun ω => A *ᵥ X ω + b) = A *ᵥ meanVec p X + b := by
  ext i
  simp only [meanVec_apply, Pi.add_apply, Matrix.mulVec, dotProduct]
  rw [expectation_add, expectation_sum _ Finset.univ, expectation_const hp1]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact expectation_const_mul p (fun ω => X ω j) (A i j)

/-- **Exact covariance propagation for affine maps**:
`covMatrix p (A *ᵥ X · + b) = A * covMatrix p X * Aᵀ`, with exactly this multiplication
order. The linear part is `FiniteProbability.covMatrix_mulVec`, valid for every weight; the
shift by `b` cancels in the centering, which needs total mass one. -/
lemma covMatrix_affine {Ω : Type*} [Fintype Ω] {m n : ℕ} (p : Ω → ℝ)
    (X : Ω → Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hp1 : ∑ ω, p ω = 1) :
    covMatrix p (fun ω => A *ᵥ X ω + b) = A * covMatrix p X * Aᵀ := by
  rw [← covMatrix_mulVec]
  have hE : ∀ k, expectation p (fun ω => (A *ᵥ X ω) k + b k) =
      expectation p (fun ω => (A *ᵥ X ω) k) + b k := fun k => by
    rw [expectation_add, expectation_const hp1]
  ext i j
  simp only [covMatrix_apply, covariance, Pi.add_apply, hE]
  congr 1
  funext ω
  ring

/-- **Correlated two-input variance**, via `covMatrix` entries so the cross term is
explicit: the variance of `a₁ X₁ + a₂ X₂` is
`a₁² Var X₁ + a₂² Var X₂ + 2 a₁ a₂ Cov(X₁, X₂)`, for every weight. The linear combination
is the single entry of a `1 × 2` measurement matrix, so this is
`FiniteProbability.covMatrix_mulVec`; the `2 a₁ a₂` cross term comes from the symmetry
`covariance_comm`, not from any independence assumption. -/
lemma covMatrix_two_linear {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → Fin 2 → ℝ)
    (a₁ a₂ : ℝ) :
    covMatrix p (fun ω => Matrix.of ![![a₁, a₂]] *ᵥ X ω) 0 0
      = a₁ ^ 2 * covMatrix p X 0 0 + a₂ ^ 2 * covMatrix p X 1 1
        + 2 * a₁ * a₂ * covMatrix p X 0 1 := by
  have hsymm : covMatrix p X 1 0 = covMatrix p X 0 1 := by
    rw [covMatrix_apply, covMatrix_apply, covariance_comm]
  rw [covMatrix_mulVec]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hsymm]
  ring

/-- **Quadrature is a SPECIAL case, not the general law**: only when the
cross-covariance entry vanishes does the variance of `a₁ X₁ + a₂ X₂` reduce to
`a₁² Var X₁ + a₂² Var X₂`. Correlated errors must keep the cross term of
`covMatrix_two_linear`. -/
lemma variance_linear_two_uncorrelated {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (X : Ω → Fin 2 → ℝ) (a₁ a₂ : ℝ) (hcov : covMatrix p X 0 1 = 0) :
    covMatrix p (fun ω => Matrix.of ![![a₁, a₂]] *ᵥ X ω) 0 0
      = a₁ ^ 2 * covMatrix p X 0 0 + a₂ ^ 2 * covMatrix p X 1 1 := by
  rw [covMatrix_two_linear p X a₁ a₂, hcov, mul_zero, add_zero]

/-! ## B. Jacobian propagation as a first-order approximation -/

/-- **Scalar first-order remainder bound.** For `f` twice continuously differentiable
(`ContDiff ℝ 2 f`, hence differentiable at every base point including interval
endpoints) with `|deriv (deriv f) y| ≤ H` on the closed interval `Set.Icc a b`, and
`x`, `x + δ` both in that interval,
`|f (x + δ) - f x - deriv f x * δ| ≤ H / 2 * δ ^ 2`. The proof reuses Mathlib's
`taylor_mean_remainder_lagrange_iteratedDeriv` at `n = 1`. The side conditions are
exact: global `C²` for the derivative identification at the base point, the
second-derivative bound only on `Icc a b`, and both endpoints in `Icc a b`. -/
lemma taylor_first_order_bound {a b H : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hH : ∀ y ∈ Set.Icc a b, |deriv (deriv f) y| ≤ H)
    {x δ : ℝ} (hx : x ∈ Set.Icc a b) (hxd : x + δ ∈ Set.Icc a b) :
    |f (x + δ) - f x - deriv f x * δ| ≤ H / 2 * δ ^ 2 := by
  by_cases hδ : δ = 0
  · subst hδ
    simp only [add_zero, sub_self, mul_zero, abs_zero, pow_two, mul_zero]
    exact le_rfl
  · have hne : x ≠ x + δ := fun h => hδ (by linarith)
    have hsub : Set.uIcc x (x + δ) ⊆ Set.Icc a b := by
      by_cases hle : x ≤ x + δ
      · rw [Set.uIcc_of_le hle]
        intro y hy
        exact ⟨hx.1.trans hy.1, hy.2.trans hxd.2⟩
      · rw [Set.uIcc_of_ge (le_of_not_ge hle)]
        intro y hy
        exact ⟨hxd.1.trans hy.1, hy.2.trans hx.2⟩
    have hderiv : derivWithin f (Set.uIcc x (x + δ)) x = deriv f x := by
      apply HasDerivWithinAt.derivWithin _ (uniqueDiffOn_uIcc hne x Set.left_mem_uIcc)
      exact (hf.contDiffAt.differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt
    obtain ⟨x', hx'mem, hx'eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne (hf.contDiffOn.mono hsub)
    have hT : taylorWithinEval f 1 (Set.uIcc x (x + δ)) x (x + δ) = f x + δ * deriv f x := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval,
        show (0 : ℕ) + 1 = 1 from rfl, iteratedDerivWithin_one, hderiv]
      simp [add_sub_cancel_left, smul_eq_mul]
    rw [hT, add_sub_cancel_left] at hx'eq
    have hiter : iteratedDeriv ((1 : ℕ) + 1) f x' = deriv (deriv f) x' := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [hiter, show Nat.factorial ((1 : ℕ) + 1) = 2 from rfl,
      show (1 : ℕ) + 1 = 2 from rfl] at hx'eq
    push_cast at hx'eq
    have hx'Icc : x' ∈ Set.Icc a b := hsub (Set.uIoo_subset_uIcc_self hx'mem)
    have hH' := hH x' hx'Icc
    have hδ2 : (0 : ℝ) ≤ δ ^ 2 := by positivity
    have hgoal : f (x + δ) - f x - deriv f x * δ = f (x + δ) - (f x + δ * deriv f x) := by
      ring
    rw [hgoal, hx'eq, abs_div, abs_mul, abs_of_nonneg hδ2, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmul : |deriv (deriv f) x'| * δ ^ 2 ≤ H * δ ^ 2 :=
      mul_le_mul_of_nonneg_right hH' hδ2
    calc |deriv (deriv f) x'| * δ ^ 2 / 2 ≤ H * δ ^ 2 / 2 := by linarith [hmul]
      _ = H / 2 * δ ^ 2 := by ring

/-- **Jacobian propagation is an APPROXIMATION.** The first-order value of `f` at
`x + δ` is `f x + fderiv ℝ f x δ`; `jacobianRemainder f x δ` is the leftover
`f (x + δ) - f x - fderiv ℝ f x δ`, bounded by the lemmas below but NOT zero in
general: for the square map on `Fin 1 → ℝ` at `x = 0` and `δ = 1 / 2` it is `1 / 4`
(see the tests). Where `f` is not differentiable at `x`, Mathlib's `fderiv ℝ f x` is `0`
and the value is just `f (x + δ) - f x`; every bound below assumes differentiability at
`x`. -/
noncomputable def jacobianRemainder {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (x δ : Fin n → ℝ) : Fin m → ℝ :=
  f (x + δ) - f x - fderiv ℝ f x δ

/-- **Componentwise Jacobian remainder bound, unit-step form.** If `f` is differentiable at
`x` and, for each component `i`, the concrete one-variable segment function
`φᵢ t = f i (x + t • δ)` is `C²` with `|φᵢ'' t| ≤ H i` on `[0, 1]`, then
`|jacobianRemainder f x δ i| ≤ H i / 2`. This is the scalar bound applied to `φᵢ`
with unit step; the `fderiv`/`φᵢ'` identification uses the chain rule along the
segment. The second derivative of `φᵢ` already carries two factors of `δ`, so `H i` bounds
it along this one segment and is not a Hessian bound; see
`jacobianRemainder_component_le_of_scaled` for the `‖δ‖ ^ 2`-scaled form and
`jacobianRemainder_component_le_of_hessian` for the bound from a Hessian bound. -/
lemma jacobianRemainder_component_le {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (x δ : Fin n → ℝ) (i : Fin m) (H : Fin m → ℝ)
    (hdiff : DifferentiableAt ℝ f x)
    (hφ : ∀ i, ContDiff ℝ 2 (fun t : ℝ => f (x + t • δ) i))
    (hH : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (fun t : ℝ => f (x + t • δ) i)) t| ≤ H i) :
    |jacobianRemainder f x δ i| ≤ H i / 2 := by
  set φ : ℝ → ℝ := fun t => f (x + t • δ) i with hφdef
  have hφ0 : φ 0 = f x i := by simp [hφdef]
  have hφ1 : φ 1 = f (x + δ) i := by simp [hφdef]
  have hbound := taylor_first_order_bound (f := φ) (hφ i) (hH i) (x := 0) (δ := 1)
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) + 1 ∈ Set.Icc 0 1)
  rw [zero_add, one_pow, mul_one, mul_one] at hbound
  have hline : HasDerivAt (fun t : ℝ => x + t • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add x
  have hg : HasFDerivAt (fun y : Fin n → ℝ => f y i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ f x)) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) i (f x)).comp x hdiff.hasFDerivAt
  have hderiv_eq : fderiv ℝ (fun y : Fin n → ℝ => f y i) x
      = (ContinuousLinearMap.proj i).comp (fderiv ℝ f x) := hg.fderiv
  have hφeq : φ = (fun y : Fin n → ℝ => f y i) ∘ (fun t : ℝ => x + t • δ) := by
    funext t
    simp only [hφdef, Function.comp_apply]
  have hchain : HasDerivAt φ (fderiv ℝ (fun y : Fin n → ℝ => f y i) x δ) 0 := by
    rw [hφeq]
    have hg0 : HasFDerivAt (fun y : Fin n → ℝ => f y i)
        ((ContinuousLinearMap.proj i).comp (fderiv ℝ f x)) (x + (0 : ℝ) • δ) := by
      simpa using hg
    have h2 := hg0.comp_hasDerivAt 0 hline
    rwa [← hderiv_eq] at h2
  have hderiv0 : deriv φ 0 = fderiv ℝ (fun y : Fin n → ℝ => f y i) x δ := hchain.deriv
  have hconn : (fderiv ℝ f x δ) i = deriv φ 0 := by
    rw [hderiv0, hderiv_eq, ContinuousLinearMap.comp_apply]
    rfl
  have hrem : jacobianRemainder f x δ i = φ 1 - φ 0 - deriv φ 0 := by
    simp only [jacobianRemainder, Pi.sub_apply, ← hφ0, ← hφ1, hconn]
  rw [hrem]
  exact hbound

/-- **Componentwise remainder bound, `‖δ‖ ^ 2`-scaled segment form.** If the segment
functions `φᵢ t = f i (x + t • δ)` are `C²` with `|φᵢ'' t| ≤ H i * ‖δ‖ ^ 2` on `[0, 1]`,
where `‖δ‖` is Mathlib's sup norm on `Fin n → ℝ`, then
`|jacobianRemainder f x δ i| ≤ H i / 2 * ‖δ‖ ^ 2`. This is
`jacobianRemainder_component_le` for the bound `H i * ‖δ‖ ^ 2`. The hypothesis still bounds
the second derivative along the given segment, not the Hessian of `f i`; for a Hessian
bound use `jacobianRemainder_component_le_of_hessian`. With the unscaled hypothesis
`|φᵢ'' t| ≤ H i`, the `‖δ‖ ^ 2` conclusion is false: the square map at `δ = 1 / 2` is a
counterexample (see the tests). -/
lemma jacobianRemainder_component_le_of_scaled {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (x δ : Fin n → ℝ) (i : Fin m) (H : Fin m → ℝ)
    (hdiff : DifferentiableAt ℝ f x)
    (hφ : ∀ i, ContDiff ℝ 2 (fun t : ℝ => f (x + t • δ) i))
    (hH : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (fun t : ℝ => f (x + t • δ) i)) t| ≤ H i * ‖δ‖ ^ 2) :
    |jacobianRemainder f x δ i| ≤ H i / 2 * ‖δ‖ ^ 2 := by
  have h := jacobianRemainder_component_le f x δ i (fun i => H i * ‖δ‖ ^ 2) hdiff hφ hH
  calc |jacobianRemainder f x δ i| ≤ H i * ‖δ‖ ^ 2 / 2 := h
    _ = H i / 2 * ‖δ‖ ^ 2 := by ring

/-- **Componentwise remainder bound from a Hessian bound.** Let `f` be `C²` on an open set
`U` containing the box `Set.Icc lo hi`, and let the second Fréchet derivative of component
`i` satisfy `‖fderiv ℝ (fderiv ℝ (fun y => f y i)) y‖ ≤ H i` on the box, the operator norm
for the sup norm on `Fin n → ℝ`. For `x` and `x + δ` in the box,
`|jacobianRemainder f x δ i| ≤ H i / 2 * ‖δ‖ ^ 2`. This is
`Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le` for the component
`fun y => f y i`; the chain rule identifies its derivative at `x` with component `i` of
`fderiv ℝ f x`. -/
lemma jacobianRemainder_component_le_of_hessian {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (x δ : Fin n → ℝ) (i : Fin m) (H : Fin m → ℝ) {lo hi : Fin n → ℝ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hbox : Set.Icc lo hi ⊆ U)
    (hf : ContDiffOn ℝ 2 f U)
    (hH : ∀ y ∈ Set.Icc lo hi, ‖fderiv ℝ (fderiv ℝ (fun y => f y i)) y‖ ≤ H i)
    (hx : x ∈ Set.Icc lo hi) (hxδ : x + δ ∈ Set.Icc lo hi) :
    |jacobianRemainder f x δ i| ≤ H i / 2 * ‖δ‖ ^ 2 := by
  have hdiff : DifferentiableAt ℝ f x :=
    (hf.differentiableOn (by norm_num) x (hbox hx)).differentiableAt (hU.mem_nhds (hbox hx))
  have hg : HasFDerivAt (fun y : Fin n → ℝ => f y i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ f x)) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) i (f x)).comp x hdiff.hasFDerivAt
  have hconn : fderiv ℝ f x δ i = fderiv ℝ (fun y : Fin n → ℝ => f y i) x δ := by
    rw [hg.fderiv, ContinuousLinearMap.comp_apply]
    rfl
  have h := Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le hU hbox
    (contDiffOn_pi.1 hf i) hH hx hxδ
  have hrem : jacobianRemainder f x δ i =
      f (x + δ) i - f x i - fderiv ℝ (fun y : Fin n → ℝ => f y i) x δ := by
    simp only [jacobianRemainder, Pi.sub_apply, hconn]
  rw [hrem]
  calc _ ≤ 1 / 2 * H i * ‖δ‖ ^ 2 := h
    _ = H i / 2 * ‖δ‖ ^ 2 := by ring

/-! ## C. Deterministic Lipschitz error propagation -/

/-- **Lipschitz error propagation**: if `f` is Lipschitz with constant `L`
(`LipschitzWith L f`, so `L : ℝ≥0` per Mathlib), then
`‖f (x + δ) - f x‖ ≤ L * ‖δ‖`. This is Mathlib's `LipschitzWith.dist_le_mul_of_le` read
with `dist_eq_norm` and `(x + δ) - x = δ`. -/
lemma lipschitz_error_propagation {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {f : E → F} {L : NNReal} (hf : LipschitzWith L f)
    (x δ : E) :
    ‖f (x + δ) - f x‖ ≤ (L : ℝ) * ‖δ‖ := by
  have h := hf.dist_le_mul_of_le (le_rfl : dist (x + δ) x ≤ dist (x + δ) x)
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h
  exact h

/-- **Error-budget form**: if the input error satisfies `‖δ‖ ≤ ε` then the output
error satisfies `‖f (x + δ) - f x‖ ≤ L * ε`. -/
lemma lipschitz_error_budget {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {f : E → F} {L : NNReal} (hf : LipschitzWith L f)
    {x δ : E} {ε : ℝ} (hδε : ‖δ‖ ≤ ε) :
    ‖f (x + δ) - f x‖ ≤ (L : ℝ) * ε := by
  calc ‖f (x + δ) - f x‖ ≤ (L : ℝ) * ‖δ‖ := lipschitz_error_propagation hf x δ
    _ ≤ (L : ℝ) * ε := mul_le_mul_of_nonneg_left hδε (by positivity)

/-- **The affine map is exact**: for `f x = A *ᵥ x + b`,
`f (x + δ) - f x = A *ᵥ δ` on the nose. Any Lipschitz bound for an affine map is a
consequence of this equality, not the sharp statement. -/
lemma affine_exact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x δ : Fin n → ℝ) :
    (fun x => A *ᵥ x + b) (x + δ) - (fun x => A *ᵥ x + b) x = A *ᵥ δ := by
  change A *ᵥ (x + δ) + b - (A *ᵥ x + b) = A *ᵥ δ
  rw [Matrix.mulVec_add, add_right_comm, add_sub_cancel_left]

/-! ## D. Rank-deficient calibration and parameter identification -/

/-- Linear-algebraic identifiability of the calibration model `y = A *ᵥ θ`:
injectivity of `θ ↦ A *ᵥ θ`. This is injectivity of the design matrix as a linear
map, distinct from statistical identification of estimands (`IsIdentifiedBy`).
Unique-estimate claims are PROHIBITED without this hypothesis: see
`exists_distinct_of_nontrivial_ker`. -/
def Identifiable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Function.Injective (fun θ => A *ᵥ θ)

/-- Identifiability holds iff the kernel is trivial: `A *ᵥ θ = 0 → θ = 0`. -/
lemma identifiable_iff_trivial_ker {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Identifiable A ↔ ∀ θ, A *ᵥ θ = 0 → θ = 0 := by
  constructor
  · intro h θ hθ
    apply h
    change A *ᵥ θ = A *ᵥ 0
    rw [hθ, Matrix.mulVec_zero]
  · intro h θ₁ θ₂ heq
    change A *ᵥ θ₁ = A *ᵥ θ₂ at heq
    have h0 : A *ᵥ (θ₁ - θ₂) = 0 := by rw [Matrix.mulVec_sub, heq, sub_self]
    have hz := h _ h0
    simpa [sub_eq_zero] using hz

/-- **Non-identifiability kills uniqueness**: from any nonzero kernel vector `θ₀`,
every parameter vector `θ` with `A *ᵥ θ = y` shares its observation `y` with the
distinct vector `θ' = θ + θ₀`. Hence unique-estimate claims are PROHIBITED without
identifiability. -/
lemma exists_distinct_of_nontrivial_ker {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hex : ∃ θ₀, θ₀ ≠ 0 ∧ A *ᵥ θ₀ = 0) (θ : Fin n → ℝ) (y : Fin m → ℝ)
    (hy : A *ᵥ θ = y) :
    ∃ θ', θ' ≠ θ ∧ A *ᵥ θ' = y := by
  obtain ⟨θ₀, hne, h0⟩ := hex
  refine ⟨θ + θ₀, ?_, ?_⟩
  · intro hcon
    have h2 : θ + θ₀ = θ + 0 := by rw [add_zero]; exact hcon
    exact hne (add_left_cancel h2)
  · rw [Matrix.mulVec_add, hy, h0, add_zero]

/-- **Rank deficiency implies non-identifiability**: if `m < n`, the linear map
`A.mulVecLin : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)` has a nontrivial kernel by
`LinearMap.ker_ne_bot_of_finrank_lt` (rank-nullity: `finrank` of source `n` exceeds
`finrank` of target `m`, via `Module.finrank_fin_fun`), and any nonzero kernel
vector defeats injectivity. -/
lemma not_identifiable_of_lt {m n : ℕ} (hmn : m < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    ¬ Identifiable A := by
  rw [identifiable_iff_trivial_ker]
  intro hcon
  have hfin : Module.finrank ℝ (Fin m → ℝ) < Module.finrank ℝ (Fin n → ℝ) := by
    rw [Module.finrank_fin_fun ℝ, Module.finrank_fin_fun ℝ]
    exact hmn
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfin
  obtain ⟨θ₀, hmem, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
  exact hne (hcon θ₀ hmem)

/-- **The normal matrix is injective** when `A` is identifiable: from
`(Aᵀ * A) *ᵥ θ = 0`, the quadratic form `θ ⬝ᵥ (Aᵀ * A) *ᵥ θ` rewrites (via
`Matrix.mulVec_mulVec`, `Matrix.dotProduct_mulVec` and `Matrix.vecMul_transpose`)
to `(A *ᵥ θ) ⬝ᵥ (A *ᵥ θ) = 0`, so `A *ᵥ θ = 0` by Mathlib's `dotProduct_self_eq_zero` and
then `θ = 0`. -/
lemma identifiable_normal_injective {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Identifiable A) :
    Function.Injective (fun θ => (Aᵀ * A) *ᵥ θ) := by
  rw [identifiable_iff_trivial_ker] at hA
  change Identifiable (Aᵀ * A)
  rw [identifiable_iff_trivial_ker]
  intro θ hθ
  apply hA
  have hquad : (A *ᵥ θ) ⬝ᵥ (A *ᵥ θ) = 0 := by
    have h0 : θ ⬝ᵥ ((Aᵀ * A) *ᵥ θ) = 0 := by simp [hθ, dotProduct]
    rwa [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at h0
  exact dotProduct_self_eq_zero.1 hquad

/-- **Normal equations have AT MOST ONE solution**: any two solutions of
`Aᵀ * A *ᵥ θ = Aᵀ *ᵥ y` agree, by injectivity of the normal matrix. Existence is a
separate claim and is not asserted here. -/
lemma normalEquations_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : Identifiable A)
    (y : Fin m → ℝ) (θ₁ θ₂ : Fin n → ℝ)
    (h₁ : (Aᵀ * A) *ᵥ θ₁ = Aᵀ *ᵥ y) (h₂ : (Aᵀ * A) *ᵥ θ₂ = Aᵀ *ᵥ y) :
    θ₁ = θ₂ :=
  identifiable_normal_injective A hA (h₁.trans h₂.symm)

end Statistics.UncertaintyPropagation
