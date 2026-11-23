/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Basic

/-!
# Discrete plastic work certificates

## i. Overview

Discrete limit analysis: for a compatibility matrix `B`, equilibrium
`B^T sigma = lambda f`, capacities `|sigma_e| <= y_e`, and a
mechanism `v` with `f . v = 1`, the load factor is at most the
plastic dissipation `sum y_e |(B v)_e|`; equality holds under the
complementary alignment certificate.

## ii. Key results

- `PlasticWork.loadFactor_le`: the bound.
- `PlasticWork.loadFactor_eq_of_complementary`: equality case.

## iii. Table of contents

- A. Work certificates

## iv. References

- J. B. Martin, *Plasticity: Fundamentals and General Results*,
  MIT Press, 1975, chapters on discrete limit analysis (bounding
  theorems and complementary energy equality conditions).

## A. Work certificates
-/

@[expose] public section

namespace PlasticWork

open Finset Matrix

theorem lam_eq_dotProduct {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) (sigma : m → ℝ) (f v : n → ℝ) (lam : ℝ)
    (heq : Bᵀ *ᵥ sigma = lam • f)
    (hnorm : f ⬝ᵥ v = 1) :
    lam = sigma ⬝ᵥ (B *ᵥ v) := by
  have h1 : (lam • f) ⬝ᵥ v = lam := by
    rw [smul_dotProduct, hnorm, smul_eq_mul, mul_one]
  have h2 : (Bᵀ *ᵥ sigma) ⬝ᵥ v = sigma ⬝ᵥ (B *ᵥ v) := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have h3 : (Bᵀ *ᵥ sigma) ⬝ᵥ v = lam := by rw [heq, h1]
  rw [h2] at h3
  exact h3.symm

/-- Discrete limit-analysis bound: for a compatibility matrix `B`,
stress `sigma` in equilibrium `Bᵀ *ᵥ sigma = lam • f`, capacities
`y` with `|sigma e| ≤ y e`, and a mechanism `v` normalized by
`f ⬝ᵥ v = 1`, the load factor satisfies
`lam ≤ ∑ e, y e * |(B *ᵥ v) e|`. -/
theorem loadFactor_le {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) (sigma y : m → ℝ) (f v : n → ℝ) (lam : ℝ)
    (heq : Bᵀ *ᵥ sigma = lam • f)
    (hcap : ∀ e : m, |sigma e| ≤ y e)
    (hnorm : f ⬝ᵥ v = 1) :
    lam ≤ ∑ e, y e * |(B *ᵥ v) e| := by
  have hkey : lam = sigma ⬝ᵥ (B *ᵥ v) :=
    lam_eq_dotProduct B sigma f v lam heq hnorm
  rw [hkey]
  show (∑ e, sigma e * (B *ᵥ v) e) ≤ _
  apply Finset.sum_le_sum
  intro e _
  calc sigma e * (B *ᵥ v) e ≤ |sigma e * (B *ᵥ v) e| := le_abs_self _
    _ = |sigma e| * |(B *ᵥ v) e| := abs_mul _ _
    _ ≤ y e * |(B *ᵥ v) e| :=
        mul_le_mul_of_nonneg_right (hcap e) (abs_nonneg _)

/-- Matching equality from a supplied complementary certificate:
if additionally `y e * |(B *ᵥ v) e| = sigma e * (B *ᵥ v) e` for every
`e` (stress aligned with the mechanism strain, no slack), equality
holds. -/
theorem loadFactor_eq_of_complementary {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) (sigma y : m → ℝ) (f v : n → ℝ) (lam : ℝ)
    (heq : Bᵀ *ᵥ sigma = lam • f)
    (hcap : ∀ e : m, |sigma e| ≤ y e)
    (hnorm : f ⬝ᵥ v = 1)
    (hcomp : ∀ e : m, y e * |(B *ᵥ v) e| = sigma e * (B *ᵥ v) e) :
    lam = ∑ e, y e * |(B *ᵥ v) e| := by
  have hle : lam ≤ ∑ e, y e * |(B *ᵥ v) e| :=
    loadFactor_le B sigma y f v lam heq hcap hnorm
  have hkey : lam = sigma ⬝ᵥ (B *ᵥ v) :=
    lam_eq_dotProduct B sigma f v lam heq hnorm
  have hsum : sigma ⬝ᵥ (B *ᵥ v) = ∑ e, y e * |(B *ᵥ v) e| := by
    show (∑ e, sigma e * (B *ᵥ v) e) = _
    apply Finset.sum_congr rfl
    intro e _
    exact (hcomp e).symm
  exact le_antisymm hle (hsum.symm.trans hkey.symm).le

end PlasticWork
