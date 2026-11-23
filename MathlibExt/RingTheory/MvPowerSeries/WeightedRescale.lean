/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/rates/GeneralPieces/GenF/Exp.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
express weighted coefficient scaling through Mathlib's canonical coefficient
map and multivariate power-series rescaling homomorphisms.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Weighted rescaling of multivariate power series

An additive weight on monomials determines the variable scalars needed by
`MvPowerSeries.rescale`.  The coefficient formula below identifies this
canonical ring homomorphism, after mapping rational coefficients, with the
weighted coefficient scaling used in the source development.
-/

@[expose] public section

namespace MvPowerSeries

private theorem prod_pow_single_weight {X R : Type*} [CommMonoid R]
    (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (d : X →₀ ℕ) :
    d.prod (fun i n => (ε ^ wt (Finsupp.single i 1)) ^ n) = ε ^ wt d := by
  classical
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i n d hi hn ih =>
      calc
        (Finsupp.single i n + d).prod
              (fun j m => (ε ^ wt (Finsupp.single j 1)) ^ m) =
            (Finsupp.single i n).prod
                (fun j m => (ε ^ wt (Finsupp.single j 1)) ^ m) *
              d.prod (fun j m => (ε ^ wt (Finsupp.single j 1)) ^ m) :=
          Finsupp.prod_add_index (by simp) (by simp [pow_add])
        _ = (ε ^ wt (Finsupp.single i 1)) ^ n * ε ^ wt d := by
          rw [Finsupp.prod_single_index (by simp), ih]
        _ = ε ^ (wt (Finsupp.single i n) + wt d) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          rw [← Finsupp.smul_single_one i n, map_nsmul, nsmul_eq_mul, mul_comm]
          simp
        _ = ε ^ wt (Finsupp.single i n + d) := by rw [map_add]

/-- Mapping rational coefficients and rescaling variable `i` by
`ε ^ wt (Finsupp.single i 1)` multiplies coefficient `d` by `ε ^ wt d`. -/
theorem coeff_rescale_map_of_weight {X R : Type*} [CommRing R] [Algebra ℚ R]
    (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (q : MvPowerSeries X ℚ) (d : X →₀ ℕ) :
    coeff d
        (rescale (fun i => ε ^ wt (Finsupp.single i 1))
          (map (algebraMap ℚ R) q)) =
      algebraMap ℚ R (coeff d q) * ε ^ wt d := by
  rw [coeff_rescale, coeff_map, prod_pow_single_weight, mul_comm]

/-- A series has the weighted coefficients of `q` exactly when it is the
canonical coefficient map of `q` followed by the corresponding rescaling. -/
theorem eq_rescale_map_of_weight_iff {X R : Type*} [CommRing R] [Algebra ℚ R]
    (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (q : MvPowerSeries X ℚ) (w : MvPowerSeries X R) :
    w = rescale (fun i => ε ^ wt (Finsupp.single i 1)) (map (algebraMap ℚ R) q) ↔
      ∀ d, coeff d w = algebraMap ℚ R (coeff d q) * ε ^ wt d := by
  constructor
  · rintro rfl d
    exact coeff_rescale_map_of_weight wt ε q d
  · intro h
    ext d
    rw [h d, coeff_rescale_map_of_weight]

end MvPowerSeries
