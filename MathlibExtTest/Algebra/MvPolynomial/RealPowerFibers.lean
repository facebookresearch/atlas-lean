/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.RealPowerFibers

@[expose] public section

-- `exactSource` consumer with the original binders.
example (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ)
    (hS : S.Infinite) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    P = Q :=
  MvPolynomial.eq_of_forall_eval_rpow_eq N hN u₀ S hS P Q h

-- Boundary: with a finite first-coordinate set the conclusion can fail.
-- On `S = {0}`, the polynomials `X 0` and `0` agree at every `(0, N ^ u)`,
-- but they are not equal, so infinitude of `S` cannot be dropped.
example : ∃ P Q : MvPolynomial (Fin 2) ℂ,
    (∀ x ∈ ({0} : Set ℂ), ∀ u : ℝ, (0 : ℝ) < u →
      MvPolynomial.eval ![x, (((2 : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((2 : ℝ) ^ u : ℝ) : ℂ)] Q) ∧ P ≠ Q := by
  refine ⟨MvPolynomial.X 0, 0, fun x hx _ _ => ?_, ?_⟩
  · simp only [Set.mem_singleton_iff] at hx
    simp [hx]
  · intro hEq
    have h1 := congrArg (MvPolynomial.eval ![1, 0]) hEq
    simp at h1
