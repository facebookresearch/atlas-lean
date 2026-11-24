/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.ClearedFunctionalEquationSum

@[expose] public section

set_option autoImplicit false

open Polynomial

/-- Exact-source consumer, using the original binders verbatim. -/
example (N : ℕ) (hN : 1 < N) (C : ℂ) (r : ℤ)
    {ι : Type} [Fintype ι] (κ : ι → ℂ) (A B : ι → ℂ → ℂ)
    (hj : ∀ j : ι, ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
      (∀ s : ℂ, σ < s.re →
        A j s * Q.eval ((N : ℂ) ^ (-s)) =
          (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σd < s.re →
        B j s * Qd.eval ((N : ℂ) ^ (-s)) =
          (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) *
              Qd.eval ((N : ℂ) ^ (-s)))) :
    ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 → Qd ≠ 0 →
      (∀ s : ℂ, σ < s.re →
        (∑ j, κ j * A j s) * Q.eval ((N : ℂ) ^ (-s)) =
          (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) →
      (∀ s : ℂ, σd < s.re →
        (∑ j, κ j * B j s) * Qd.eval ((N : ℂ) ^ (-s)) =
          (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) →
      ∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) *
              Qd.eval ((N : ℂ) ^ (-s)) :=
  forall_clearedFE_sum_smul_of_forall_clearedFE_of_forall_rational N hN C r κ A B hj

/-- The same consumer in a higher universe. -/
example (N : ℕ) (hN : 1 < N) (C : ℂ) (r : ℤ)
    {ι : Type 1} [Fintype ι] (κ : ι → ℂ) (A B : ι → ℂ → ℂ)
    (hj : ∀ j : ι, ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
      (∀ s : ℂ, σ < s.re →
        A j s * Q.eval ((N : ℂ) ^ (-s)) =
          (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σd < s.re →
        B j s * Qd.eval ((N : ℂ) ^ (-s)) =
          (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) *
              Qd.eval ((N : ℂ) ^ (-s)))) :
    ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 → Qd ≠ 0 →
      (∀ s : ℂ, σ < s.re →
        (∑ j, κ j * A j s) * Q.eval ((N : ℂ) ^ (-s)) =
          (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) →
      (∀ s : ℂ, σd < s.re →
        (∑ j, κ j * B j s) * Qd.eval ((N : ℂ) ^ (-s)) =
          (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) →
      ∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) *
              Qd.eval ((N : ℂ) ^ (-s)) :=
  forall_clearedFE_sum_smul_of_forall_clearedFE_of_forall_rational N hN C r κ A B hj

/-- The per-term functional equation cannot be dropped: with all polynomial
factors equal to `1`, exponents `0`, and constant term-functions `1`, the
cleared identities for the sums hold, but the concluded identity would say
`1 = 0` when the scalar factor is `0`. -/
example : ¬ ∀ s : ℂ,
    ((1 : Polynomial ℂ)).eval ((2 : ℂ) ^ s) *
        ((2 : ℂ) ^ (((0 : ℤ) : ℂ) * s) * (1 : Polynomial ℂ).eval ((2 : ℂ) ^ (-s))) *
        (1 : Polynomial ℂ).eval ((2 : ℂ) ^ s) =
      ((Polynomial.C (0 : ℂ)).eval ((2 : ℂ) ^ s) * (2 : ℂ) ^ (((0 : ℤ) : ℂ) * s)) *
        ((2 : ℂ) ^ (((0 : ℤ) : ℂ) * (-s)) * (1 : Polynomial ℂ).eval ((2 : ℂ) ^ s)) *
          (1 : Polynomial ℂ).eval ((2 : ℂ) ^ (-s)) := by
  intro h
  have hs := h 0
  simp at hs
