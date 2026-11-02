/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.Derivation.IteratedLeibniz
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Data.ZMod.Basic

@[expose] public section

private def sourceDerivation {B : Type*} [CommRing B] [Algebra ℚ B]
    (D : B →ₗ[ℚ] B) (hD : ∀ a b, D (a * b) = a * D b + D a * b) : Derivation ℚ B B :=
  Derivation.mk' D fun a b => by
    rw [hD]
    simp [smul_eq_mul, mul_comm]

private theorem source_iterate_mul {B : Type*} [CommRing B] [Algebra ℚ B]
    (D : B →ₗ[ℚ] B) (hD : ∀ a b, D (a * b) = a * D b + D a * b)
    (n : ℕ) (a b : B) :
    (D : B → B)^[n] (a * b) =
      ∑ p ∈ Finset.antidiagonal n,
        n.choose p.1 • ((D : B → B)^[p.1] a * (D : B → B)^[p.2] b) := by
  simpa [sourceDerivation] using (sourceDerivation D hD).iterate_mul n a b

private theorem source_iterate_mul_div {B : Type*} [CommRing B] [Algebra ℚ B]
    (D : B →ₗ[ℚ] B) (hD : ∀ a b, D (a * b) = a * D b + D a * b)
    (n : ℕ) (a b : B) :
    ((n.factorial : ℚ)⁻¹) • (D : B → B)^[n] (a * b) =
      ∑ p ∈ Finset.antidiagonal n,
        ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) •
          ((D : B → B)^[p.1] a * (D : B → B)^[p.2] b) := by
  simpa [sourceDerivation] using (sourceDerivation D hD).iterate_mul_div n a b

-- At order zero the canonical formula is the identity.
example {R B : Type*} [CommSemiring R] [CommRing B] [Algebra R B]
    (D : Derivation R B B) (a b : B) :
    (D : B → B)^[0] (a * b) = a * b := by
  rw [D.iterate_mul]
  simp

-- At order one it is the ordinary product rule.
example {R B : Type*} [CommSemiring R] [CommRing B] [Algebra R B]
    (D : Derivation R B B) (a b : B) :
    D (a * b) = a * D b + D a * b := by
  rw [D.leibniz]
  simp [smul_eq_mul, mul_comm]

-- A zero derivation has zero positive iterates.
example {R B : Type*} [CommSemiring R] [CommRing B] [Algebra R B] (a b : B) :
    ((0 : Derivation R B B) : B → B)^[3] (a * b) = 0 := by
  simp [Function.iterate_succ_apply']

private theorem derivative_product_order_two :
    (((Polynomial.derivative' : Derivation ℚ (Polynomial ℚ) (Polynomial ℚ)) :
      Polynomial ℚ → Polynomial ℚ)^[2])
        (Polynomial.X ^ 2 * Polynomial.X ^ 3) = 20 * Polynomial.X ^ 3 := by
  rw [← pow_add]
  norm_num [Function.iterate_succ_apply', Polynomial.derivative'_apply,
    Polynomial.derivative_X_pow]
  ring

-- Two derivatives of `X² * X³` give a populated polynomial.
example :
    (((Polynomial.derivative' : Derivation ℚ (Polynomial ℚ) (Polynomial ℚ)) :
      Polynomial ℚ → Polynomial ℚ)^[2])
        (Polynomial.X ^ 2 * Polynomial.X ^ 3) = 20 * Polynomial.X ^ 3 :=
  derivative_product_order_two

-- Dividing the same second derivative by `2!` gives `10X³`.
example :
    (((2 : ℕ).factorial : ℚ)⁻¹ •
      (((Polynomial.derivative' : Derivation ℚ (Polynomial ℚ) (Polynomial ℚ)) :
        Polynomial ℚ → Polynomial ℚ)^[2])
        (Polynomial.X ^ 2 * Polynomial.X ^ 3)) = 10 * Polynomial.X ^ 3 := by
  rw [derivative_product_order_two]
  ext n
  by_cases h : n = 3 <;>
    norm_num [Polynomial.coeff_smul, Polynomial.coeff_X_pow, h]

-- The fifth derivative reaches a nonzero constant; the sixth derivative vanishes.
example :
    (((Polynomial.derivative' : Derivation ℚ (Polynomial ℚ) (Polynomial ℚ)) :
      Polynomial ℚ → Polynomial ℚ)^[5])
        (Polynomial.X ^ 2 * Polynomial.X ^ 3) = 120 := by
  rw [← pow_add]
  norm_num [Function.iterate_succ_apply', Polynomial.derivative'_apply,
    Polynomial.derivative_X_pow]

example :
    (((Polynomial.derivative' : Derivation ℚ (Polynomial ℚ) (Polynomial ℚ)) :
      Polynomial ℚ → Polynomial ℚ)^[6])
        (Polynomial.X ^ 2 * Polynomial.X ^ 3) = 0 := by
  rw [← pow_add]
  norm_num [Function.iterate_succ_apply', Polynomial.derivative'_apply,
    Polynomial.derivative_X_pow]

private theorem polynomialDerivative_source_leibniz (a b : Polynomial ℚ) :
    Polynomial.derivative (a * b) =
      a * Polynomial.derivative b + Polynomial.derivative a * b := by
  rw [Polynomial.derivative_mul]
  ac_rfl

-- The source linear-map schema is recovered through `Derivation.mk'`.
example (n : ℕ) (a b : Polynomial ℚ) :
    (Polynomial.derivative : Polynomial ℚ → Polynomial ℚ)^[n] (a * b) =
      ∑ p ∈ Finset.antidiagonal n,
        n.choose p.1 •
          ((Polynomial.derivative : Polynomial ℚ → Polynomial ℚ)^[p.1] a *
            (Polynomial.derivative : Polynomial ℚ → Polynomial ℚ)^[p.2] b) :=
  source_iterate_mul Polynomial.derivative polynomialDerivative_source_leibniz n a b

example (n : ℕ) (a b : Polynomial ℚ) :
    (n.factorial : ℚ)⁻¹ •
        (Polynomial.derivative : Polynomial ℚ → Polynomial ℚ)^[n] (a * b) =
      ∑ p ∈ Finset.antidiagonal n,
        ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) •
          ((Polynomial.derivative : Polynomial ℚ → Polynomial ℚ)^[p.1] a *
            (Polynomial.derivative : Polynomial ℚ → Polynomial ℚ)^[p.2] b) :=
  source_iterate_mul_div Polynomial.derivative polynomialDerivative_source_leibniz n a b

-- In characteristic two the natural coefficient remains present; both sides become zero.
private noncomputable def zmodTwoDerivative :
    Derivation (ZMod 2) (Polynomial (ZMod 2)) (Polynomial (ZMod 2)) :=
  Polynomial.derivative'

example :
    ((zmodTwoDerivative : Polynomial (ZMod 2) → Polynomial (ZMod 2))^[2])
        (Polynomial.X * Polynomial.X) =
      ∑ p ∈ Finset.antidiagonal 2,
        (2 : ℕ).choose p.1 •
          ((zmodTwoDerivative : Polynomial (ZMod 2) → Polynomial (ZMod 2))^[p.1]
              Polynomial.X *
            (zmodTwoDerivative : Polynomial (ZMod 2) → Polynomial (ZMod 2))^[p.2]
              Polynomial.X) :=
  zmodTwoDerivative.iterate_mul 2 Polynomial.X Polynomial.X

example :
    ((zmodTwoDerivative : Polynomial (ZMod 2) → Polynomial (ZMod 2))^[2])
        (Polynomial.X * Polynomial.X) = 0 := by
  rw [← pow_two]
  norm_num [zmodTwoDerivative, Function.iterate_succ_apply', Polynomial.derivative'_apply,
    Polynomial.derivative_X_pow]
  exact CharP.cast_eq_zero (Polynomial (ZMod 2)) 2

example : (2 : ℕ) • (1 : Polynomial (ZMod 2)) = 0 := by
  norm_num
  exact CharP.cast_eq_zero (Polynomial (ZMod 2)) 2
