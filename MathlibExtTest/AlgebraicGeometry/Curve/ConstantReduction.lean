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

-- Consumer with the original binders for a constant reduction.
example {L : Type*} [Field L] (A : ValuationSubring L) (F : Type*) [Field F]
    [Algebra L F] (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (D : Divisor L F) :
    Divisor.degree (Finsupp.mapDomain R.placeMap D) = Divisor.degree D :=
  R.degree_mapDomain D

-- A constant reduction preserves principal divisors, with original binders.
example {L : Type*} [Field L] (A : ValuationSubring L) (F : Type*) [Field F]
    [Algebra L F] (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) {D : Divisor L F}
    (hD : D ∈ Divisor.principal (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈
      Divisor.principal (K := ResidueField A) (F := Fbar) :=
  R.mapDomain_mem_principal hD

-- Good reduction is genus equality, with original binders.
example {L : Type*} [Field L] (A : ValuationSubring L) (F : Type*) [Field F]
    [Algebra L F] (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) :
    R.IsGood ↔ genusFF (ResidueField A) Fbar = genusFF L F :=
  R.isGood_iff

-- Constants have order zero at every place; the nonzero hypothesis matters,
-- as `0` is excluded by the statement of `ord_algebraMap`.
example {L F : Type*} [Field L] [Field F] [Algebra L F] (P : Place L F)
    {c : L} (hc : c ≠ 0) : P.ord (algebraMap L F c) = 0 :=
  ConstantReduction.ord_algebraMap P hc

end AlgebraicCurve
