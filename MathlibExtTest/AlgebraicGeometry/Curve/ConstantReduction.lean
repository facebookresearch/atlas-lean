/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.ConstantReduction

@[expose] public section

open IsLocalRing

namespace AlgebraicCurve

-- Consumer with the original binders for a constant reduction: reduction preserves degrees.
example {L : Type*} [Field L] (A : ValuationSubring L) (F : Type*) [Field F]
    [Algebra L F] (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (D : Divisor L F) :
    Divisor.degree (R.divMap D) = Divisor.degree D :=
  R.degree_divMap D

-- A constant reduction preserves principal divisors, with original binders.
example {L : Type*} [Field L] (A : ValuationSubring L) (F : Type*) [Field F]
    [Algebra L F] (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) {D : Divisor L F}
    (hD : D ∈ Divisor.principal (K := L) (F := F)) :
    R.divMap D ∈ Divisor.principal (K := ResidueField A) (F := Fbar) :=
  R.divMap_mem_principal hD

-- Good reduction is genus equality, with original binders.
example {L : Type*} [Field L] (A : ValuationSubring L) (F : Type*) [Field F]
    [Algebra L F] (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) :
    R.IsGood ↔ genusFF (ResidueField A) Fbar = genusFF L F :=
  R.isGood_iff

-- Scaling by a nonzero constant keeps the order.
example {L F : Type*} [Field L] [Field F] [Algebra L F] (P : Place L F) {c : L} (hc : c ≠ 0)
    (f : F) : P.ord (c • f) = P.ord f :=
  P.ord_smul_of_ne_zero hc f

section

variable {L : Type*} [Field L] (A : ValuationSubring L) (F : Type*) [Field F] [Algebra L F]
  (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar] (R : ConstantReduction A F Fbar)

-- A place reduces to a divisor, not necessarily a single place; the reduction of a divisor is the
-- sum of the reductions of its places, with multiplicities.
example (P : Place L F) (n : ℤ) : R.divMap (Finsupp.single P n) = n • R.placeDivisor P := by
  simp

example (D : Divisor L F) : R.divMap D = D.sum fun P n => n • R.placeDivisor P :=
  R.divMap_apply D

example (P Q : Place L F) :
    R.divMap (Finsupp.single P 1 + Finsupp.single Q 2) =
      R.placeDivisor P + (2 : ℤ) • R.placeDivisor Q := by
  simp

-- The reduction of a place is effective and has the degree of the place.
example (P : Place L F) :
    0 ≤ R.placeDivisor P ∧ Divisor.degree (R.placeDivisor P) = P.deg :=
  ⟨R.placeDivisor_nonneg P, R.degree_placeDivisor P⟩

example {D : Divisor L F} (hD : D ∈ Divisor.degZero (K := L) (F := F)) :
    R.divMap D ∈ Divisor.degZero (K := ResidueField A) (F := Fbar) :=
  R.divMap_mem_degZero hD

example (D : Divisor.degZero (K := L) (F := F)) :
    (R.degZeroMap D : Divisor (ResidueField A) Fbar) = R.divMap (D : Divisor L F) := by
  simp

example (D : Divisor.degZero (K := L) (F := F)) :
    R.pic0Map (Pic0.mk D) = Pic0.mk (R.degZeroMap D) :=
  R.pic0Map_mk D

end

end AlgebraicCurve
