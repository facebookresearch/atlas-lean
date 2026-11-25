/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.StructureConstants

@[expose] public noncomputable section

namespace CartierStructureConstantsTest

open CerednikDrinfeld MvPolynomial

/-- Consumer with the original binders: division by a non-zero-divisor `π` inside the ideal
`(X u * X v - π)`. -/
theorem exactSource {σ : Type*} {R : Type*} [CommRing R] {π : R}
    (hπ : ∀ r : R, π * r = 0 → r = 0) (u v : σ) {g : MvPolynomial σ R}
    (h : C π * g ∈ Ideal.span {(X u * X v - C π : MvPolynomial σ R)}) :
    g ∈ Ideal.span {(X u * X v - C π : MvPolynomial σ R)} :=
  mem_span_of_C_mul_mem_span_X_mul_X_sub_C hπ u v h

/-- The lift ring maps back to `B`, sending each variable to itself. -/
example (p : ℕ) {R B : Type*} [CommRing R] [CommRing B] (j : R →+* B) (u v : B)
    (huv : u * v = p) (b : B) : CartierLift.liftHom j u v huv (CartierLift.liftVar u v b) = b :=
  CartierLift.liftHom_liftVar j u v huv b

end CartierStructureConstantsTest
