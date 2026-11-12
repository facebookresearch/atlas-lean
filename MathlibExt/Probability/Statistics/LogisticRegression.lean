/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Logistic negative log-likelihood is convex in coefficients

For a design matrix `X`, outcomes `y`, and coefficients `β`, the
logistic negative log-likelihood
`∑ i, [log (1 + exp (x_i ⬝ β)) - y_i (x_i ⬝ β)]` is convex in `β` on
the whole coefficient space. Each summand is the scalar softplus
composed with the linear map `β ↦ x_i ⬝ β`, minus a linear term
(Atlas roadmap ST09.T02). The scalar softplus convexity is proved as a
private helper from Mathlib's derivative criterion, because MathlibExt
cannot import the PhyslibExt softplus kernel; see the helper's note.
-/

@[expose] public section


open Finset

namespace MathlibExt.Probability.Statistics.LogisticRegression

/-- The logistic negative log-likelihood (NLL) of binary outcomes `y`
against a design matrix `X` at coefficients `β`:
`∑ i, [log (1 + exp (x_i ⬝ β)) - y_i (x_i ⬝ β)]`.
For binary outcomes `y_i ∈ {0, 1}` this is the usual logistic NLL;
convexity below holds for arbitrary real `y`, since the second term is
linear in `β`. -/
noncomputable def logisticNLL {n m : ℕ} (X : Fin n → Fin m → ℝ) (y : Fin n → ℝ)
    (β : Fin m → ℝ) : ℝ :=
  ∑ i, (Real.log (1 + Real.exp (∑ j, X i j * β j)) - y i * ∑ j, X i j * β j)

/-- Scalar softplus convexity, as a private helper. MathlibExt cannot
import the PhyslibExt softplus-convexity kernel
(`fsc_softplus_convexOn`), so this helper is proved here from Mathlib's
derivative criterion (`MonotoneOn.convexOn_of_deriv`) via monotonicity
of `Real.sigmoid`. It is not public API: a follow-up unification that
moves the softplus kernel to MathlibExt would delete this helper and
cite the kernel instead. -/
private theorem convexOn_log_one_add_exp :
    ConvexOn ℝ Set.univ (fun t => Real.log (1 + Real.exp t)) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t => Real.log (1 + Real.exp t))
      (Real.sigmoid t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 1 + Real.exp t) (Real.exp t) t :=
      (Real.hasDerivAt_exp t).const_add 1
    have hne : (1 : ℝ) + Real.exp t ≠ 0 := by positivity
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp t))
        (Real.exp t / (1 + Real.exp t)) t :=
      h1.log hne
    have h3 : Real.exp t / (1 + Real.exp t) = Real.sigmoid t := by
      rw [Real.sigmoid_def, Real.exp_neg]
      have hexp : Real.exp t ≠ 0 := Real.exp_ne_zero t
      have hne2 : (1 : ℝ) + (Real.exp t)⁻¹ ≠ 0 := by positivity
      field_simp
      ring
    rw [h3] at h2
    exact h2
  have hderiv_eq : deriv (fun t => Real.log (1 + Real.exp t)) = Real.sigmoid := by
    funext t
    exact (hderiv t).deriv
  refine MonotoneOn.convexOn_of_deriv convex_univ ?_ ?_ ?_
  · exact fun t _ => (hderiv t).differentiableAt.continuousAt.continuousWithinAt
  · rw [interior_univ]
    exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
  · rw [interior_univ, hderiv_eq]
    exact Real.sigmoid_monotone.monotoneOn _

/-- **Logistic NLL is convex in the coefficients (ST09.T02).** Each
summand is the scalar softplus composed with the linear map
`β ↦ x_i ⬝ β`, minus a linear term; a sum of convex functions is convex. -/
theorem convexOn_logisticNLL {n m : ℕ} (X : Fin n → Fin m → ℝ) (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (logisticNLL X y) := by
  refine ⟨convex_univ, ?_⟩
  intro β₁ _ β₂ _ a b ha hb hab
  simp only [logisticNLL, smul_eq_mul]
  have hlin : ∀ i : Fin n, (∑ j, X i j * (a • β₁ + b • β₂) j)
      = a * (∑ j, X i j * β₁ j) + b * (∑ j, X i j * β₂ j) := by
    intro i
    have h1 : ∀ j : Fin m, X i j * (a • β₁ + b • β₂) j
        = a * (X i j * β₁ j) + b * (X i j * β₂ j) := by
      intro j
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    calc ∑ j, X i j * (a • β₁ + b • β₂) j
        = ∑ j, (a * (X i j * β₁ j) + b * (X i j * β₂ j)) :=
          Finset.sum_congr rfl (fun j _ => h1 j)
      _ = a * (∑ j, X i j * β₁ j) + b * (∑ j, X i j * β₂ j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hpt : ∀ i : Fin n,
      (Real.log (1 + Real.exp (∑ j, X i j * (a • β₁ + b • β₂) j))
        - y i * ∑ j, X i j * (a • β₁ + b • β₂) j)
      ≤ a * (Real.log (1 + Real.exp (∑ j, X i j * β₁ j)) - y i * ∑ j, X i j * β₁ j)
        + b * (Real.log (1 + Real.exp (∑ j, X i j * β₂ j)) - y i * ∑ j, X i j * β₂ j) := by
    intro i
    have hS := convexOn_log_one_add_exp.2 (Set.mem_univ (∑ j, X i j * β₁ j))
      (Set.mem_univ (∑ j, X i j * β₂ j)) ha hb hab
    simp only [smul_eq_mul] at hS
    rw [hlin i]
    have hL : y i * (a * (∑ j, X i j * β₁ j) + b * (∑ j, X i j * β₂ j))
        = a * (y i * (∑ j, X i j * β₁ j)) + b * (y i * (∑ j, X i j * β₂ j)) := by ring
    have hgoal : a * (Real.log (1 + Real.exp (∑ j, X i j * β₁ j))
          - y i * ∑ j, X i j * β₁ j)
        + b * (Real.log (1 + Real.exp (∑ j, X i j * β₂ j)) - y i * ∑ j, X i j * β₂ j)
        = (a * Real.log (1 + Real.exp (∑ j, X i j * β₁ j))
          + b * Real.log (1 + Real.exp (∑ j, X i j * β₂ j)))
          - (a * (y i * (∑ j, X i j * β₁ j)) + b * (y i * (∑ j, X i j * β₂ j))) := by ring
    rw [hgoal, ← hL]
    exact sub_le_sub_right hS _
  calc (∑ i, (Real.log (1 + Real.exp (∑ j, X i j * (a • β₁ + b • β₂) j))
        - y i * ∑ j, X i j * (a • β₁ + b • β₂) j))
        ≤ ∑ i, (a * (Real.log (1 + Real.exp (∑ j, X i j * β₁ j))
          - y i * ∑ j, X i j * β₁ j)
          + b * (Real.log (1 + Real.exp (∑ j, X i j * β₂ j))
            - y i * ∑ j, X i j * β₂ j)) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = a * (∑ i, (Real.log (1 + Real.exp (∑ j, X i j * β₁ j))
          - y i * ∑ j, X i j * β₁ j))
        + b * (∑ i, (Real.log (1 + Real.exp (∑ j, X i j * β₂ j))
          - y i * ∑ j, X i j * β₂ j)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end MathlibExt.Probability.Statistics.LogisticRegression
