/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.Algebra.MvPolynomial.DilationRigidity

@[expose] public section

/-- Consumer with the original binders. -/
example (g n : ℕ) (hn : 2 ≤ n) (α β : ℕ) (hαβ : α + β = n ^ 2) (hα : α = β + n)
    (P : MvPolynomial (Fin 2) ℚ) (hP : P.totalDegree ≤ g)
    (h : ∀ a b : ℕ,
      MvPolynomial.eval ![((α * a + β * b : ℕ) : ℚ), ((β * a + α * b : ℕ) : ℚ)] P =
        (n : ℚ) ^ (2 * g) * MvPolynomial.eval ![(a : ℚ), (b : ℚ)] P) :
    ∃ c : ℚ, P = MvPolynomial.C c * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ g :=
  MvPolynomial.exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval
    g n hn α β hαβ hα P hP h

/-- The conclusion holds for `(X₀ + X₁)²` with `n = 2`, `α = 3`, `β = 1`. -/
example : ∃ c : ℚ, (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ^ 2 =
    MvPolynomial.C c * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 2 :=
  ⟨1, by simp⟩

/-- Boundary: `X₀` alone (with `g = 1`, `n = 2`, `α = 3`, `β = 1`) does not
satisfy the dilation identity, at `a = 1`, `b = 0` it gives `3 ≠ 4`. -/
example : ¬ (∀ a b : ℕ,
    MvPolynomial.eval ![((3 * a + 1 * b : ℕ) : ℚ), ((1 * a + 3 * b : ℕ) : ℚ)]
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) =
      (2 : ℚ) ^ (2 * 1) *
        MvPolynomial.eval ![(a : ℚ), (b : ℚ)] (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)) := by
  intro h
  have h10 := h 1 0
  simp at h10
  have h4 : ((2 : ℚ) ^ (2 : ℕ)) = 4 := by norm_num
  rw [h4] at h10
  linarith
