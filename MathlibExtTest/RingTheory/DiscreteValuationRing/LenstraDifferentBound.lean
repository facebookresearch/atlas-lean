/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.LenstraDifferentBound
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Tests for Lenstra's bound for the different

These examples exercise
`IsDiscreteValuationRing.le_addVal_finrank_of_differentIdeal_eq_maximalIdeal_pow` and its
characteristic-zero form, for an arbitrary extension and for the trivial extension of the
`p`-adic integers, where `e = 1`, `r = 0` and `n = 1`.
-/

@[expose] public section

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The bound for an arbitrary finite torsion-free extension of discrete valuation rings with
separable fraction field extension. -/
example (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] (e r : ℕ)
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e)
    (hr : differentIdeal A B = maximalIdeal B ^ r) :
    (r : ℕ∞) ≤ ((e - 1 : ℕ) : ℕ∞) + e * IsDiscreteValuationRing.addVal A
      (Module.finrank (FractionRing A) (FractionRing B) : A) :=
  IsDiscreteValuationRing.le_addVal_finrank_of_differentIdeal_eq_maximalIdeal_pow A B e r he hr

/-- The trace of `1` is the degree. -/
example (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.IsTorsionFree A B] [Module.Finite A B] :
    Algebra.intTrace A B 1 = (Module.finrank (FractionRing A) (FractionRing B) : A) :=
  IsDiscreteValuationRing.intTrace_one_eq_finrank_fractionRing A B

/-- The trivial extension of `ℤ_[p]`, in characteristic zero: here `e = 1` and `n = 1`, so the
bound forces `r = 0`, that is, the different ideal is the unit ideal. -/
example (p : ℕ) [Fact p.Prime] : differentIdeal ℤ_[p] ℤ_[p] = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ℤ_[p]
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (differentIdeal_ne_bot (A := ℤ_[p]) (B := ℤ_[p])) hϖ
  have hr' : differentIdeal ℤ_[p] ℤ_[p] = maximalIdeal ℤ_[p] ^ r := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hr]
  have h :=
    IsDiscreteValuationRing.le_addVal_finrank_of_differentIdeal_eq_maximalIdeal_pow_of_charZero
      ℤ_[p] ℤ_[p] 1 r (by simp) hr'
  have hfin : @Module.finrank (FractionRing ℤ_[p]) (FractionRing ℤ_[p]) _ _
      (@Algebra.toModule _ _ _ _ (FractionRing.liftAlgebra ℤ_[p] (FractionRing ℤ_[p]))) = 1 := by
    rw [@finrank_eq_one_iff_of_ne_zero' _ _ _ _
      (@Algebra.toModule _ _ _ _ (FractionRing.liftAlgebra ℤ_[p] (FractionRing ℤ_[p])))
      (1 : FractionRing ℤ_[p]) one_ne_zero]
    intro w
    refine ⟨w, ?_⟩
    rw [@Algebra.smul_def _ _ _ _ (FractionRing.liftAlgebra ℤ_[p] (FractionRing ℤ_[p])), mul_one,
      FractionRing.algebraMap_liftAlgebra]
    exact IsLocalization.lift_id w
  rw [hfin] at h
  have hr0 : r = 0 := by simpa using h
  rw [hr', hr0, pow_zero, Ideal.one_eq_top]
