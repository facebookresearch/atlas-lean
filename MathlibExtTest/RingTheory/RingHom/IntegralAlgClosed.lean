/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.RingHom.IntegralAlgClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

example (R S K : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Field K] [IsAlgClosed K] (χ : R →+* K)
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.comap (algebraMap R S) = RingHom.ker χ) :
    ∃ χ' : S →+* K, χ'.comp (algebraMap R S) = χ ∧ RingHom.ker χ' = Q :=
  RingHom.exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed χ Q hQ

example : ∃ χ' : ℤ →+* Complex, χ'.comp (algebraMap ℤ ℤ) = Int.castRingHom Complex ∧
    RingHom.ker χ' = ⊥ :=
  RingHom.exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
    (Int.castRingHom Complex) ⊥ (by
      rw [Algebra.algebraMap_self]
      ext a
      simp)
