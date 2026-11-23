/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.MacaulayGrowth

@[expose] public section

open MvPolynomial AlgebraicGeometry.HilbertFunctor

universe u

-- Consumer with the original binders.
example (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d)) :=
  MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd K J hJ

-- The same consumer in a higher universe.
example (n d : ℕ) (hd : 1 ≤ d) (K : Type u) [Field K]
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d)) :=
  MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd K J hJ
