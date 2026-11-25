/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.ZMod
import MathlibExt.NumberTheory.FunctionField.DegreeSlicePerron

open MetaMathlibExt Polynomial

-- `X` is the monic polynomial of degree one with constant coefficient zero.
example : (X : (ZMod 2)[X]) ∈ fixedDegreeMonic (ZMod 2) 1 :=
  (mem_fixedDegreeMonic_iff (ZMod 2) 1 X).2 ⟨0, by simp⟩

-- The degree-zero slice is the single polynomial `1`.
example : fixedDegreeMonic (ZMod 3) 0 = {1} :=
  fixedDegreeMonic_zero (ZMod 3)

-- Perron's formula over `𝔽₂` on the circle of radius `1 / 2`, for the constant term.
example (a : (ZMod 2)[X] → ℂ) (A : ℂ → ℂ)
    (hsum : Summable fun n : ℕ => ‖∑ f ∈ fixedDegreeMonic (ZMod 2) n, a f‖ * (1 / 2 : ℝ) ^ n)
    (hA : ∀ u : ℂ, ‖u‖ = 1 / 2 →
      A u = ∑' m : ℕ, (∑ f ∈ fixedDegreeMonic (ZMod 2) m, a f) * u ^ m) :
    a 1 = (1 / (2 * Real.pi * Complex.I)) * ∮ u in C(0, 1 / 2), A u / u := by
  have h := perron_formula_polynomial_degree_slice (ZMod 2) a A (1 / 2) (by norm_num)
    (by norm_num) hsum hA 0
  simpa [fixedDegreeMonic_zero] using h
