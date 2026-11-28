/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HomogeneousResultant

/-!
# Homogeneous multivariate resultants

Construct the normalized universal resultant for positive-degree systems.
The coefficient extraction, homogeneity and specialization are concrete
polynomial operations. Existing univariate resultant and Gröbner proofs
are covered components; this request is for the projective multivariate
common-zero polynomial with its normalization and multiplicities.

References:
* GKZ, *Discriminants, Resultants, and Multidimensional Determinants*,
  Chapter 13, https://doi.org/10.1007/978-0-8176-4771-1.
* Covered univariate source: `Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`.
* Covered Gröbner source: TauCetiProject/TauCeti at
  62bbc0596dc3539d488232e4e924a338548ea0a9,
  `TauCeti/RingTheory/MvPolynomial/Groebner/Colon.lean`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HomogeneousResultantWanted

open MathlibExt.AlgebraicGeometry.HomogeneousResultant

universe u

/-- Existence of the integral universal resultant with all defining laws. -/
theorem_wanted exists_homogeneousResultant (n : ℕ) (d : Fin (n + 1) → ℕ)
    (hd : ∀ i, 0 < d i) : Nonempty (UniversalResultant.{u} n d)

/-- The normalization and defining laws identify a unique polynomial. -/
theorem_wanted homogeneousResultant_unique (n : ℕ) (d : Fin (n + 1) → ℕ)
    (hd : ∀ i, 0 < d i) (P Q : UniversalResultant.{u} n d) :
    P.polynomial = Q.polynomial

end WantedExt.AlgebraicGeometry.HomogeneousResultantWanted
