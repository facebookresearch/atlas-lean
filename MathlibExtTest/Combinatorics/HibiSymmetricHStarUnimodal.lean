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
