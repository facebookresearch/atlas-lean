/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.Polynomial.BernsteinSubdivision
import Mathlib.Tactic.NormNum

open bernsteinPolynomial

-- The nonconstant control values 0,1,4 evaluate to 3/2 at the midpoint.
example : deCasteljau (1/2) (fun j => (j : ℝ)^2) 2 = 3/2 := by
  norm_num [deCasteljau]

-- The left child has control values 0,1/2,3/2 and reconstructs p(x/2).
example (x : ℝ) :
    deCasteljau x (fun j => deCasteljau (1/2) (fun i => (i : ℝ)^2) j) 2 =
      deCasteljau (x/2) (fun i => (i : ℝ)^2) 2 := by
  simpa [div_eq_mul_inv] using deCasteljau_left (1/2) x (fun i => (i : ℝ)^2) 2

-- The right child reconstructs the other half at every real x, not just in [0,1].
example (x : ℝ) :
    deCasteljau x (fun j => deCasteljau (1/2)
      (fun i => ((i + j : ℕ) : ℝ)^2) (2-j)) 2 =
      deCasteljau (1/2 + x/2) (fun i => (i : ℝ)^2) 2 := by
  convert deCasteljau_right (1/2) x (fun i => (i : ℝ)^2) 2 using 1
  congr 2
  ring

-- Depth zero ignores both the cut and every coefficient beyond the first.
example (t a : ℝ) : deCasteljau t (fun j => if j = 0 then a else 12345) 0 = a := by
  simp [deCasteljau]

-- Endpoint cuts, including a nontrivial triangle depth.
example : deCasteljau 0 (fun j => (j : ℝ)^2 + 3) 3 = 3 := by
  norm_num [deCasteljau]

example : deCasteljau 1 (fun j => (j : ℝ)^2 + 3) 3 = 12 := by
  norm_num [deCasteljau]

-- The interval restriction is essential: an extrapolating cut escapes [0,4].
example : ¬ deCasteljau 2 (fun j => (j : ℝ)^2) 2 ∈ Set.Icc 0 4 := by
  norm_num [deCasteljau]

-- Convex enclosure applies uniformly to arbitrary triangle depth.
example {t L U : ℝ} (ht : t ∈ Set.Icc 0 1) (c : ℕ → ℝ) (n : ℕ)
    (hc : ∀ j ≤ n, c j ∈ Set.Icc L U) : deCasteljau t c n ∈ Set.Icc L U :=
  deCasteljau_mem_Icc ht hc

#print axioms deCasteljau_left
#print axioms deCasteljau_right
#print axioms deCasteljau_eq_sum
#print axioms deCasteljau_mem_Icc
