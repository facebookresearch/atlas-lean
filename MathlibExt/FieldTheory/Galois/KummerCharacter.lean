/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_NumberField_KummerCharacter.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The Kummer character of an intermediate field

For a prime `p`, a chosen `p`-th root `kummerRoot` of a unit of an
intermediate field `F` of `AlgebraicClosure ℚ`, and an element `σ` of
the fixing subgroup of `F`, the ratio `σ(kummerRoot x) / kummerRoot x`
is a `p`-th root of unity. With a chosen primitive root `ζ`, the
Kummer character `kummerChar` records its exponent in `ZMod p`.
-/

@[expose] public noncomputable section

namespace NumberField.LevelArith

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ)
  (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ))

/-- A chosen `p`-th root of a unit of `F` in the algebraic closure. -/
public def kummerRoot (x : (↥F)ˣ) : AlgebraicClosure ℚ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    ((x : ↥F) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos)

/-- The chosen root really is a `p`-th root. -/
public theorem kummerRoot_pow (x : (↥F)ˣ) :
    kummerRoot p F x ^ p = ((x : ↥F) : AlgebraicClosure ℚ) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    ((x : ↥F) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos)

/-- The chosen root is nonzero. -/
public theorem kummerRoot_ne_zero (x : (↥F)ˣ) : kummerRoot p F x ≠ 0 :=
  fun h => by
    have hpow := kummerRoot_pow p F x
    rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hpow
    exact (Units.ne_zero x) (Subtype.ext (by exact_mod_cast hpow.symm))

/-- The Galois ratio of a Kummer root is a `p`-th root of unity. -/
public theorem div_kummerRoot_pow_eq_one (x : (↥F)ˣ)
    (σ : ↥F.fixingSubgroup) :
    ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (kummerRoot p F x) / kummerRoot p F x) ^ p = 1 := by
  rw [div_pow, ← map_pow, kummerRoot_pow, div_eq_one_iff_eq]
  · exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ (x : ↥F).2
  · exact_mod_cast (Units.ne_zero x : (x : ↥F) ≠ 0)

include hζ in
/-- The Galois ratio is a power of the chosen primitive root. -/
public theorem exists_kummerExp (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    ∃ i < p, ζ ^ i = (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (kummerRoot p F x) / kummerRoot p F x :=
  hζ.eq_pow_of_pow_eq_one (div_kummerRoot_pow_eq_one p F x σ)

include hζ in
/-- The Kummer character: the exponent of the Galois ratio as an
element of `ZMod p`. -/
public def kummerChar (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) : ZMod p :=
  (Classical.choose (exists_kummerExp p ζ hζ F x σ) : ℕ)

include hζ in
/-- The Galois action on a Kummer root is multiplication by the
corresponding power of `ζ`. -/
public theorem kummerChar_spec (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) =
      ζ ^ (kummerChar p ζ hζ F x σ).val * kummerRoot p F x := by
  obtain ⟨hi, h⟩ := Classical.choose_spec (exists_kummerExp p ζ hζ F x σ)
  rw [kummerChar, ZMod.val_natCast_of_lt hi, h,
    div_mul_cancel₀ _ (kummerRoot_ne_zero p F x)]

end NumberField.LevelArith
