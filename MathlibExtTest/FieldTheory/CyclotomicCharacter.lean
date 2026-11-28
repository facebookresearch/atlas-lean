/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.CyclotomicCharacter

/-! Tests for `MathlibExt.FieldTheory.CyclotomicCharacter`. -/

set_option autoImplicit false

#check @Field.ellAdicCyclotomicCharacter
#check @Field.ellAdicCyclotomicCharacter_spec
#check @Field.eq_ellAdicCyclotomicCharacter
#check @Field.continuous_ellAdicCyclotomicCharacter
#check @Field.CyclotomicPrime
#check @Field.CyclotomicPrime.fact_prime
#check @Field.cyclotomicCharacterProd
#check @Field.cyclotomicCharacterProd_spec
#check @Field.continuous_cyclotomicCharacterProd
#check @Representation.twistByCharacter
#check @Representation.twistByCharacter_apply
#check @Representation.twistByCharacter_zero
#check @Representation.twistByCharacter_twistByCharacter
#check @Field.tateTwistZl
#check @Field.tateTwistZl_apply
#check @Field.apply_pow_val_eq

/-- The `ℓ`-adic character over `ℚ` for `ℓ = 3` is defined, and fixes `1`. -/
example [Fact (Nat.Prime 3)] : Field.ellAdicCyclotomicCharacter ℚ 3 1 = 1 :=
  map_one _

/-- `ℤ_ℓ(0)` is the trivial representation. -/
example (ℓ : ℕ) [Fact ℓ.Prime] :
    Field.tateTwistZl ℚ ℓ 0 =
      Representation.trivial ℤ_[ℓ] (Field.absoluteGaloisGroup ℚ) ℤ_[ℓ] :=
  Representation.twistByCharacter_zero _ _

/-- `ℤ_ℓ(i)(j) = ℤ_ℓ(i + j)`. -/
example (ℓ : ℕ) [Fact ℓ.Prime] (i j : ℤ) :
    (Field.tateTwistZl ℚ ℓ i).twistByCharacter (Field.ellAdicCyclotomicCharacter ℚ ℓ) j =
      Field.tateTwistZl ℚ ℓ (i + j) :=
  Representation.twistByCharacter_twistByCharacter _ _ _ _

/-- Over `ℚ`, `(2 : ℚ) ≠ 0`, so the defining property applies to square roots of unity:
every automorphism sends `-1` to `(-1) ^ a`, with `a` the residue mod `2`. -/
example [Fact (Nat.Prime 2)] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ (-1) = (-1) ^ (PadicInt.toZModPow 1
      (Field.ellAdicCyclotomicCharacter ℚ 2 σ : ℤ_[2])).val :=
  Field.ellAdicCyclotomicCharacter_spec ℚ 2 (by norm_num) σ (by norm_num)

/-- The `5`-adic character of `ℚ` is continuous. -/
example [Fact (Nat.Prime 5)] : Continuous (Field.ellAdicCyclotomicCharacter ℚ 5) :=
  Field.continuous_ellAdicCyclotomicCharacter ℚ 5 (by norm_num)

#print axioms Field.ellAdicCyclotomicCharacter
#print axioms Field.CyclotomicPrime.fact_prime
#print axioms Field.ellAdicCyclotomicCharacter_spec
#print axioms Field.eq_ellAdicCyclotomicCharacter
#print axioms Field.continuous_ellAdicCyclotomicCharacter
#print axioms Field.cyclotomicCharacterProd
#print axioms Field.cyclotomicCharacterProd_spec
#print axioms Field.continuous_cyclotomicCharacterProd
#print axioms Representation.twistByCharacter
#print axioms Representation.twistByCharacter_zero
#print axioms Representation.twistByCharacter_twistByCharacter
#print axioms Field.tateTwistZl
#print axioms Field.tateTwistZl_apply
#print axioms Representation.twistByCharacter_apply
#print axioms Field.apply_pow_val_eq
