/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HibiSymmetricHStarUnimodal

/-! # Lattice hulls and the counterexample to unimodality -/

open MathlibExt.Combinatorics.HibiSymmetricHStarUnimodalOWR741Problem003Wanted
open MetaMathlibExt

-- Even in dimension zero the empty vertex set spans the empty polytope.
example : latticePolytope (∅ : Finset (Fin 0 → ℤ)) = ∅ := by
  simp [latticePolytope]

-- A single lattice point spans precisely its real image.
example {d : ℕ} (v : Fin d → ℤ) :
    latticePolytope {v} = {fun i => (v i : ℝ)} := by
  simp [latticePolytope]

-- Extract a geometric witness with all the hypotheses of the conjecture.
example : ∃ (d : ℕ) (S : Finset (Fin d → ℤ)) (h : Polynomial ℤ),
    (interior (latticePolytope S)).Nonempty ∧ IsHStarPolynomial (latticePolytope S) h ∧
      (∀ i ≤ d, h.coeff i = h.coeff (d - i)) ∧ ¬ IsUnimodal h := by
  by_contra! hall
  apply hibiSymmetricUnimodal_refuted
  intro d S hS h hstar hsym
  exact hall d S h hS hstar hsym

open Polynomial in
-- The symmetric vector (1, 1, 2, 1, 2, 1, 1) of the counterexample dips at index 3, so it is not
-- unimodal.
example : ¬ IsUnimodal (1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℤ[X]) := by
  rintro ⟨t, -, hinc, hdec⟩
  have c2 : (1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℤ[X]).coeff 2 = 2 := by
    simp [coeff_X, coeff_one, coeff_X_pow]
  have c3 : (1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℤ[X]).coeff 3 = 1 := by
    simp [coeff_X, coeff_one, coeff_X_pow]
  have c4 : (1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℤ[X]).coeff 4 = 2 := by
    simp [coeff_X, coeff_one, coeff_X_pow]
  rcases le_or_gt 3 t with ht | ht
  · have := hinc 2 3 (by norm_num) ht
    omega
  · have hd := le_natDegree_of_ne_zero (show
      (1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℤ[X]).coeff 4 ≠ 0 by
        rw [c4]; norm_num)
    have := hdec 3 4 (by omega) (by norm_num) hd
    omega
