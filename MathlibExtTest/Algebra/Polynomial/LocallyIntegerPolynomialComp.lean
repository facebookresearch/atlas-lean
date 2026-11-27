/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomialComp

/-! # Tests for composition of locally integer polynomial functions -/

open MetaMathlibExt Polynomial

-- Squaring after a shift is not the same as shifting after squaring.
example : (fun x : (Set.univ : Set ℤ) => ((x : ℤ) + 1) ^ 2) ∈ lipSubring Set.univ := by
  have h := lip_univ_comp (polynomialToLIP Set.univ (X ^ 2)).property
    (polynomialToLIP Set.univ (X + C 1)).property
  convert h using 1
  funext x
  simp only [polynomialToLIP_apply, eval_pow, eval_add, eval_X, eval_C]

-- The inner function can map every interpolation node to the same integer.
example {f : ↥(Set.univ : Set ℤ) → ℤ} (hf : f ∈ lipSubring Set.univ) :
    (fun _ => f ⟨-3, Set.mem_univ _⟩) ∈ lipSubring Set.univ := by
  have h := lip_univ_comp hf (polynomialToLIP Set.univ (C (-3))).property
  convert h using 1
  funext x
  simp only [polynomialToLIP_apply, eval_C]
