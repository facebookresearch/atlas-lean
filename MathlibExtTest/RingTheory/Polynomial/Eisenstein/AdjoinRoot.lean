/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.Eisenstein.AdjoinRoot
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (f : A[X]) (heis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A))
  (hf : f.Monic) (hdeg : 0 < f.natDegree)

-- The Eisenstein adjoint-root ring is local.
example : IsLocalRing (AdjoinRoot f) :=
  AdjoinRoot.isLocalRing_of_isEisensteinAt f heis hf hdeg

-- With that instance installed, the maximal-ideal equality is usable.
example : let _ := AdjoinRoot.isLocalRing_of_isEisensteinAt f heis hf hdeg
    IsLocalRing.maximalIdeal (AdjoinRoot f) =
    Ideal.span {AdjoinRoot.root f} := by
  dsimp only
  exact @AdjoinRoot.isLocalRing_maximalIdeal_eq_span_root _ _ _ _ f heis hf hdeg
    (AdjoinRoot.isLocalRing_of_isEisensteinAt f heis hf hdeg)

-- The exact DVR conclusion is usable, with its explicit domain instance.
example : @IsDiscreteValuationRing (AdjoinRoot f) _
    (AdjoinRoot.isDomain_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (heis.irreducible (IsLocalRing.maximalIdeal.isMaximal A).isPrime
          hf.isPrimitive hdeg))) :=
  AdjoinRoot.isDiscreteValuationRing_of_isEisensteinAt f heis hf hdeg

-- The root is irreducible (hence a uniformizer).
example : Irreducible (AdjoinRoot.root f) :=
  AdjoinRoot.irreducible_root_of_isEisensteinAt f heis hf hdeg

namespace ConcretePadicEisenstein

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev PadicA := ℤ_[2]

/-- The concrete Eisenstein polynomial `X² - 2` over the 2-adic integers. -/
noncomputable def padicEisenstein : PadicA[X] := X ^ 2 - C 2

lemma padicEisenstein_monic : padicEisenstein.Monic := by
  exact monic_X_pow_sub_C (2 : PadicA) (by decide)

lemma padicEisenstein_natDegree : padicEisenstein.natDegree = 2 := by
  exact natDegree_X_pow_sub_C _

lemma padicEisenstein_natDegree_pos : 0 < padicEisenstein.natDegree := by
  rw [padicEisenstein_natDegree]
  decide

lemma padicEisenstein_isEisenstein :
    padicEisenstein.IsEisensteinAt (IsLocalRing.maximalIdeal PadicA) := by
  refine padicEisenstein_monic.isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal PadicA).ne_top ?_ ?_
  · intro n hn
    rw [padicEisenstein_natDegree] at hn
    interval_cases n <;>
      simp [padicEisenstein, PadicInt.maximalIdeal_eq_span_p]
  · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    intro h
    have hnorm :=
      (PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) (-(2 : PadicA)) 2).mpr
        (by simpa [padicEisenstein] using h)
    have hnorm_two : ‖(2 : PadicA)‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
    rw [norm_neg, hnorm_two] at hnorm
    norm_num at hnorm

local instance padicEisenstein_isDomain : IsDomain (AdjoinRoot padicEisenstein) :=
  AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (padicEisenstein_isEisenstein.irreducible
        (IsLocalRing.maximalIdeal.isMaximal PadicA).isPrime
        padicEisenstein_monic.isPrimitive padicEisenstein_natDegree_pos))

local instance padicEisenstein_isLocalRing : IsLocalRing (AdjoinRoot padicEisenstein) :=
  AdjoinRoot.isLocalRing_of_isEisensteinAt
    padicEisenstein padicEisenstein_isEisenstein padicEisenstein_monic
      padicEisenstein_natDegree_pos

local instance padicEisenstein_isDVR :
    IsDiscreteValuationRing (AdjoinRoot padicEisenstein) :=
  AdjoinRoot.isDiscreteValuationRing_of_isEisensteinAt
    padicEisenstein padicEisenstein_isEisenstein padicEisenstein_monic
      padicEisenstein_natDegree_pos

-- The abstract maximal-ideal theorem computes the maximal ideal in this actual extension.
example : IsLocalRing.maximalIdeal (AdjoinRoot padicEisenstein) =
    Ideal.span {AdjoinRoot.root padicEisenstein} :=
  AdjoinRoot.isLocalRing_maximalIdeal_eq_span_root
    padicEisenstein padicEisenstein_isEisenstein padicEisenstein_monic
      padicEisenstein_natDegree_pos

-- The concrete extension is a DVR, and its root is a uniformizer.
example : IsDiscreteValuationRing (AdjoinRoot padicEisenstein) := inferInstance

example : Irreducible (AdjoinRoot.root padicEisenstein) :=
  AdjoinRoot.irreducible_root_of_isEisensteinAt
    padicEisenstein padicEisenstein_isEisenstein padicEisenstein_monic
      padicEisenstein_natDegree_pos

end ConcretePadicEisenstein
