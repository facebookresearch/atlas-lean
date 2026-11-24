/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CanonicalLineEhrhart
import Mathlib.Tactic.ComputeDegree

open Polynomial MetaMathlibExt

-- A negative real scale is allowed, including for a polynomial of degree zero.
example : IsCLWithParameters (C (-1 : ℂ)) (-1) [] := by
  simp [IsCLWithParameters, clQuadraticProduct]

-- For a single quadratic factor the parameter bound includes its endpoint.
example (c : ℝ) : IsCLWithParameters (X ^ 2 + X + C (c : ℂ)) 1 [c] ↔ 1 / 4 ≤ c := by
  have hd : (X ^ 2 + X + C (c : ℂ)).natDegree = 2 := by compute_degree!
  simp [IsCLWithParameters, clQuadraticProduct, hd]

-- The odd linear factor takes purely imaginary values at every height on the line.
example (t : ℝ) : ((2 * X + 1 : Polynomial ℂ).eval ⟨-(1 / 2), t⟩).re = 0 := by
  have hd : (2 * X + 1 : Polynomial ℂ).natDegree = 1 := by compute_degree!
  have hf : IsCL (2 * X + 1) :=
    ⟨1, [], by simp [IsCLWithParameters, clQuadraticProduct, hd]⟩
  obtain ⟨r, hr⟩ := cl_value_on_canonicalLine _ hf ⟨-(1 / 2), t⟩ rfl
  rw [hr, hd, pow_one]
  simp
