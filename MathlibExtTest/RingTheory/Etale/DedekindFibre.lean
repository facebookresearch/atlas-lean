/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.DedekindFibre
public import Mathlib.Data.Real.Basic

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

-- Boundary: without separability the fibre need not be étale; `X ^ 2` over
-- `ℝ` gives the non-reduced, hence non-étale, algebra `ℝ[X] ⧸ (X ^ 2)`.
example : ¬ Algebra.Etale ℝ (ℝ[X] ⧸ Ideal.span {(X ^ 2 : ℝ[X])}) := by
  intro hEt
  have hred : IsReduced (ℝ[X] ⧸ Ideal.span {(X ^ 2 : ℝ[X])}) :=
    Algebra.FormallyUnramified.isReduced_of_field ℝ _
  have hne : (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : ℝ[X])}) (X : ℝ[X])) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact fun hdvd => by
      have := Polynomial.degree_le_of_dvd hdvd (by norm_num)
      simp at this
  exact hne (IsReduced.eq_zero _ ⟨2, by
    show (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : ℝ[X])}) (X : ℝ[X])) ^ 2 = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]⟩)
