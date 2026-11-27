/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.DedekindFibre
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.NoZeroSMulDivisors.Pi
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.Degree

@[expose] public section

open Polynomial

-- Source statement with the original binders.
example {k : Type} [Field k] (B : Type) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B]
    [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hirr : Irreducible h) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ →
      Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) :=
  IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt B h hirr hsep hunr

-- Higher-universe consumer.
example {k : Type*} [Field k] (B : Type*) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B]
    [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hirr : Irreducible h) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ →
      Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) :=
  IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt B h hirr hsep hunr

-- General form: no Dedekind-domain hypothesis on `B`.
example {k : Type*} [Field k] (B : Type*) [CommRing B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B]
    [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hirr : Irreducible h) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ →
      Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) :=
  Algebra.etale_quotient_map_span_of_forall_isUnramifiedAt B h hirr hsep hunr

-- The general form applies to `Fin 2 → k[X]`, that is `k[X] × k[X]`, which is
-- not a domain; its fibre above `X` is `k × k`.
example {k : Type*} [Field k] :
    Algebra.Etale k ((Fin 2 → k[X]) ⧸
      Ideal.map (algebraMap k[X] (Fin 2 → k[X])) (Ideal.span {X})) :=
  Algebra.etale_quotient_map_span_of_forall_isUnramifiedAt (Fin 2 → k[X]) X irreducible_X
    separable_X fun _ _ _ _ => inferInstance

-- Boundary: separability cannot be dropped. Over the imperfect field `𝔽₂(t)`,
-- `X ^ 2 - t` is irreducible but inseparable. For `B = 𝔽₂(t)[X]`, a Dedekind
-- domain that is finite, torsion-free and unramified over itself, the fibre above
-- it is the purely inseparable extension `𝔽₂(√t)`, which is not étale.

-- `t` has odd degree, so it is not a square in `𝔽₂(t)`.
private theorem sq_ne_ratFuncX (b : RatFunc (ZMod 2)) : b ^ 2 ≠ RatFunc.X := by
  intro hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact RatFunc.X_ne_zero (by simpa using hb.symm)
  have hdeg := congrArg RatFunc.intDegree hb
  rw [pow_two, RatFunc.intDegree_mul hb0 hb0, RatFunc.intDegree_X] at hdeg
  omega

private theorem irreducible_X_sq_sub_ratFuncX :
    Irreducible (X ^ 2 - C RatFunc.X : (RatFunc (ZMod 2))[X]) :=
  irreducible_X_pow_sub_C_of_prime Nat.prime_two sq_ne_ratFuncX

private theorem not_separable_X_sq_sub_ratFuncX :
    ¬ (X ^ 2 - C RatFunc.X : (RatFunc (ZMod 2))[X]).Separable := by
  rw [separable_iff_derivative_ne_zero irreducible_X_sq_sub_ratFuncX, not_not,
    derivative_sub, derivative_X_pow, derivative_C, sub_zero]
  simp [CharTwo.two_eq_zero]

example : ¬ ∀ (k : Type) [Field k] (B : Type) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B]
    [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]), Irreducible h →
      (∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ →
        Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
        Algebra.IsUnramifiedAt k[X] P) →
      Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) := by
  intro H
  set h : (RatFunc (ZMod 2))[X] := X ^ 2 - C RatFunc.X
  have hEt := H (RatFunc (ZMod 2)) (RatFunc (ZMod 2))[X] h irreducible_X_sq_sub_ratFuncX
    fun _ _ _ _ => inferInstance
  rw [Algebra.algebraMap_self, Ideal.map_id] at hEt
  have : Fact (Irreducible h) := ⟨irreducible_X_sq_sub_ratFuncX⟩
  have : Algebra.Etale (RatFunc (ZMod 2)) (AdjoinRoot h) := hEt
  have := Algebra.FormallyUnramified.isSeparable (RatFunc (ZMod 2)) (AdjoinRoot h)
  have hroot : (minpoly (RatFunc (ZMod 2)) (AdjoinRoot.root h)).Separable :=
    Algebra.IsSeparable.isSeparable _ _
  rw [AdjoinRoot.minpoly_root irreducible_X_sq_sub_ratFuncX.ne_zero,
    (monic_X_pow_sub_C _ two_ne_zero).leadingCoeff, inv_one, C_1, mul_one] at hroot
  exact not_separable_X_sq_sub_ratFuncX hroot
