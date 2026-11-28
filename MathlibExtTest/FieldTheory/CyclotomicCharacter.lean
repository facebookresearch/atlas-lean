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
#check @Field.ellAdicCyclotomicCharacter_eq_one_of_natCast_eq_zero
#check @Field.continuous_ellAdicCyclotomicCharacter
#check @Field.CyclotomicPrime
#check @Field.CyclotomicPrime.fact_prime
#check @Field.cyclotomicCharacterProd
#check @Field.cyclotomicCharacterProd_spec
#check @Field.continuous_cyclotomicCharacterProd
#check @Field.tateTwistZl
#check @Field.tateTwistZl_apply
#check @Field.ellAdicCyclotomicCharacter_spec_pow_val

/-- `5` is prime, for the examples over `ZMod 5`. -/
private instance factPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

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
example : Continuous (Field.ellAdicCyclotomicCharacter ℚ 5) :=
  Field.continuous_ellAdicCyclotomicCharacter ℚ 5

/-- The `5`-adic character of `ZMod 5`, at the characteristic, is continuous too. -/
example : Continuous (Field.ellAdicCyclotomicCharacter (ZMod 5) 5) :=
  Field.continuous_ellAdicCyclotomicCharacter (ZMod 5) 5

/-- At the characteristic, the `ℓ`-adic character is trivial: the `5`-adic character of
`ZMod 5`. -/
example : Field.ellAdicCyclotomicCharacter (ZMod 5) 5 = 1 :=
  Field.ellAdicCyclotomicCharacter_eq_one_of_natCast_eq_zero (ZMod 5) 5 (ZMod.natCast_self 5)

/-- At the characteristic, every twist `ℤ_ℓ(i)` is the trivial representation: `ℤ_5(i)` over
`ZMod 5`. -/
example (i : ℤ) :
    Field.tateTwistZl (ZMod 5) 5 i =
      Representation.trivial ℤ_[5] (Field.absoluteGaloisGroup (ZMod 5)) ℤ_[5] := by
  rw [Field.tateTwistZl,
    Field.ellAdicCyclotomicCharacter_eq_one_of_natCast_eq_zero (ZMod 5) 5 (ZMod.natCast_self 5)]
  refine MonoidHom.ext fun σ => LinearMap.ext fun x => ?_
  simp [Representation.twistByCharacter_apply]

/-- Instance inference finds that each index of `Field.CyclotomicPrime ℚ` is prime. -/
example (ℓ : Field.CyclotomicPrime ℚ) : Fact ℓ.1.Prime := inferInstance

/-- Each component of the product character is the `ℓ`-adic character. -/
example (k : Type*) [Field k] (σ : Field.absoluteGaloisGroup k) (ℓ : Field.CyclotomicPrime k) :
    Field.cyclotomicCharacterProd k σ ℓ = Field.ellAdicCyclotomicCharacter k ℓ.1 σ :=
  rfl

/-- In characteristic `5`, the characteristic `5` is not an index of the product. -/
example : ¬ ∃ ℓ : Field.CyclotomicPrime (ZMod 5), ℓ.1 = 5 := by
  rintro ⟨⟨l, -, hl⟩, rfl⟩
  exact hl (ZMod.natCast_self 5)

/-- In characteristic `5`, the prime `2` is an index of the product. -/
example : ∃ ℓ : Field.CyclotomicPrime (ZMod 5), ℓ.1 = 2 :=
  ⟨⟨2, Nat.prime_two, by decide⟩, rfl⟩

/-- The defining property of the product character for `ζ = -1`, `n = 2` over `ℚ`, with
`a = 1`: the residue of `χ_cycl(σ)` modulo `2` is a unit of `ℤ/2ℤ`, hence `1`, so every
automorphism fixes `-1`. -/
example (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : σ (-1) = (-1) ^ (1 : ℤ) := by
  refine Field.cyclotomicCharacterProd_spec ℚ σ (n := 2) (by norm_num) (by norm_num) 1
    fun ℓ => ?_
  have hu : IsUnit (PadicInt.toZModPow (Nat.factorization 2 ℓ.1)
      (Field.cyclotomicCharacterProd ℚ σ ℓ : ℤ_[ℓ.1])) := (Units.isUnit _).map _
  generalize PadicInt.toZModPow (Nat.factorization 2 ℓ.1)
      (Field.cyclotomicCharacterProd ℚ σ ℓ : ℤ_[ℓ.1]) = x at hu ⊢
  have key : ∀ N : ℕ, N ∣ 2 → ∀ y : ZMod N, IsUnit y → ((1 : ℤ) : ZMod N) = y := by
    intro N hN y hy
    rcases (Nat.dvd_prime Nat.prime_two).1 hN with rfl | rfl
    · exact Subsingleton.elim _ _
    · fin_cases y
      · exact absurd hy not_isUnit_zero
      · rfl
  exact key _ (Nat.ordProj_dvd 2 ℓ.1) x hu

/-- Equivariance of `a ↦ ζ ^ a` for `ζ = -1`, `ℓ = 2`, `m = 1` over `ℚ`. -/
example [Fact (Nat.Prime 2)] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (a : ZMod (2 ^ 1)) :
    σ ((-1) ^ a.val) = (-1) ^ (PadicInt.toZModPow 1
      (Field.ellAdicCyclotomicCharacter ℚ 2 σ : ℤ_[2]) * a).val :=
  Field.ellAdicCyclotomicCharacter_spec_pow_val ℚ 2 (by norm_num) σ (by norm_num) a

#print axioms Field.ellAdicCyclotomicCharacter
#print axioms Field.CyclotomicPrime.fact_prime
#print axioms Field.ellAdicCyclotomicCharacter_spec
#print axioms Field.eq_ellAdicCyclotomicCharacter
#print axioms Field.ellAdicCyclotomicCharacter_eq_one_of_natCast_eq_zero
#print axioms Field.continuous_ellAdicCyclotomicCharacter
#print axioms Field.cyclotomicCharacterProd
#print axioms Field.cyclotomicCharacterProd_spec
#print axioms Field.continuous_cyclotomicCharacterProd
#print axioms Field.tateTwistZl
#print axioms Field.tateTwistZl_apply
#print axioms Field.ellAdicCyclotomicCharacter_spec_pow_val
