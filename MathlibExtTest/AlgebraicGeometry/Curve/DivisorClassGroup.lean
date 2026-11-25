/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

@[expose] public section

namespace AlgebraicCurve.DivisorClassGroupTest

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

-- The degree of a place is the dimension of its residue field over the constant field.
example (v : Place K F) : v.deg = Module.finrank K v.ResidueField :=
  rfl

-- The degree weights each coefficient by the degree of its place.
example (v : Place K F) : Divisor.degree (Finsupp.single v 2) = 2 * v.deg :=
  Divisor.degree_single v 2

example (v w : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n + Finsupp.single w (-n)) = n * (v.deg - w.deg) := by
  rw [map_add, Divisor.degree_single, Divisor.degree_single]
  ring

-- The divisor of a nonzero element is principal, and so is its negative, the divisor of the
-- inverse.
example (D : Divisor K F) (f : F) (hf : f ≠ 0) (hD : ∀ v : Place K F, D v = v.ord f) :
    D ∈ Divisor.principal (K := K) (F := F) ∧ -D ∈ Divisor.principal (K := K) (F := F) :=
  ⟨⟨f, hf, hD⟩, Divisor.principal.neg_mem ⟨f, hf, hD⟩⟩

-- A divisor of degree zero has class zero exactly when it is the divisor of a nonzero element.
example (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = 0 ↔ ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, (D : Divisor K F) v = v.ord f :=
  Pic0.mk_eq_zero_iff D

-- Two divisors of degree zero have the same class when they differ by a principal divisor.
example (D E : Divisor.degZero (K := K) (F := F))
    (h : Divisor.IsPrincipal ((D : Divisor K F) - (E : Divisor K F))) : Pic0.mk D = Pic0.mk E :=
  sub_eq_zero.mp ((Pic0.mk_eq_zero_iff (D - E)).mpr h)

-- The class map is additive, and the zero divisor has class zero.
example (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk (D + E) = Pic0.mk D + Pic0.mk E ∧ Pic0.mk (0 : Divisor.degZero (K := K) (F := F)) = 0 :=
  ⟨Pic0.mk_add D E, Pic0.mk_zero⟩

-- Every degree-zero class is the class of a divisor of degree zero.
example (x : Pic0 K F) : ∃ D : Divisor.degZero (K := K) (F := F), Pic0.mk D = x :=
  Pic0.mk_surjective x

end AlgebraicCurve.DivisorClassGroupTest
