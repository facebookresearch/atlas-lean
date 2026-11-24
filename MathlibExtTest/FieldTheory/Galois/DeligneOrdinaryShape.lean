/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.DeligneOrdinaryShape

@[expose] public section

namespace GaloisRepDeligneOrdinaryShapeTest

/-- Consumer with the original shape binders. -/
public theorem exactSource {A : Type*} [CommRing A] {H : Type*} [Group H]
    (ρloc : H →* Matrix.GeneralLinearGroup (Fin 2) A) (I : Subgroup H)
    (frob : H) (χ : H →* A) (k : ℕ) (ap εp : A)
    (h : GaloisRep.DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) A,
      (g * ρloc frob * g⁻¹).val 1 1 = ap :=
  GaloisRep.DeligneOrdinaryShape.exists_conj_frob_apply_one_one h

/-- Higher-universe consumer. -/
public theorem exactSourceTypeOne {A : Type 1} [CommRing A] {H : Type 1}
    [Group H] (ρloc : H →* Matrix.GeneralLinearGroup (Fin 2) A)
    (I : Subgroup H) (frob : H) (χ : H →* A) (k : ℕ) (ap εp : A)
    (h : GaloisRep.DeligneOrdinaryShape ρloc I frob χ k ap εp) (σ : H) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) A,
      (g * ρloc σ * g⁻¹).val 1 0 = 0 :=
  GaloisRep.DeligneOrdinaryShape.exists_conj_apply_one_zero h σ

/-- The trivial representation satisfies the shape. -/
public example {A : Type*} [CommRing A] {H : Type*} [Group H]
    (I : Subgroup H) (frob : H) (k : ℕ) :
    GaloisRep.DeligneOrdinaryShape (1 : H →* Matrix.GeneralLinearGroup
      (Fin 2) A) I frob 1 k 1 1 :=
  GaloisRep.deligneOrdinaryShape_one I frob k

/-- The shape forces the lower-left entry to vanish after conjugation;
without that clause, a representation need not be triangular in any
fixed basis asserted by the shape. -/
public example {A : Type*} [CommRing A] {H : Type*} [Group H]
    (ρloc : H →* Matrix.GeneralLinearGroup (Fin 2) A) (I : Subgroup H)
    (frob : H) (χ : H →* A) (k : ℕ) (ap εp : A)
    (h : GaloisRep.DeligneOrdinaryShape ρloc I frob χ k ap εp) (σ : H) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) A,
      (g * ρloc σ * g⁻¹).val 1 0 = 0 :=
  GaloisRep.DeligneOrdinaryShape.exists_conj_apply_one_zero h σ

end GaloisRepDeligneOrdinaryShapeTest
