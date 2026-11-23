/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.FiniteFreeCofinality
public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreTranslationLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Regular-denominator fractions in the original row-projective model

The actual rank-one free object supplies a cofinal denominator in the integral
skeleton monoid algebra. Every localized module element is represented by a
power of this denominator. Equality of two such fractions is exactly equality
at a common regular-stabilization stage. The statements allow arbitrary module
carriers and arbitrary associative unital problem Rings, including zero and
non-IBN Rings. No homology comparison or injectivity before stabilization is
assumed.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.SInverseS

universe u v

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The actual skeleton monomial of the literal rank-one object in the existing
small row-idempotent model, as a denominator of its core translation ring. -/
public def finiteFreeRowRegularDenominator :
    coreTranslationDenominators (FGProjectiveCat.IdempotentModel R) :=
  coreTranslationDenominator (FGProjectiveCat.IdempotentModel R)
    (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)))

/-- The regular denominator has its original integral skeleton-monomial value. -/
private theorem finiteFreeRowRegularDenominator_val_computation07 :
    (finiteFreeRowRegularDenominator R :
      coreTranslationRing (FGProjectiveCat.IdempotentModel R)) =
      MonoidAlgebra.of ℤ (Multiplicative (Skeleton (FGProjectiveCat.IdempotentModel R)))
        (Multiplicative.ofAdd
          (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)))) := by
  unfold finiteFreeRowRegularDenominator
  rfl

public theorem finiteFreeRowRegularDenominator_val :
    (finiteFreeRowRegularDenominator R :
      coreTranslationRing (FGProjectiveCat.IdempotentModel R)) =
      MonoidAlgebra.of ℤ (Multiplicative (Skeleton (FGProjectiveCat.IdempotentModel R)))
        (Multiplicative.ofAdd
          (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)))) :=
  finiteFreeRowRegularDenominator_val_computation07 R

/-- Every original skeleton denominator has an actual complementary denominator
whose product is a regular power, by the derived finite-free cofinality. -/
public theorem finiteFreeRowDenominator_exists_complement
    (d : coreTranslationDenominators (FGProjectiveCat.IdempotentModel R)) :
    ∃ (n : ℕ) (e : coreTranslationDenominators (FGProjectiveCat.IdempotentModel R)),
      d * e = (finiteFreeRowRegularDenominator R) ^ n := by
  let C := FGProjectiveCat.IdempotentModel R
  let φ : Multiplicative (Skeleton C) →* coreTranslationRing C :=
    MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
  let s : Skeleton C :=
    toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ))
  obtain ⟨p, hp⟩ := MonoidHom.mem_mrange.mp d.property
  obtain ⟨n, q, hpq⟩ :=
    RingK0.idempotentRegularSkeletonClass_isCofinalElement R p.toAdd
  let e : coreTranslationDenominators C := coreTranslationDenominator C q
  refine ⟨n, e, Subtype.ext ?_⟩
  change (d : coreTranslationRing C) * φ (Multiplicative.ofAdd q) =
    (φ (Multiplicative.ofAdd s)) ^ n
  calc
    _ = φ p * φ (Multiplicative.ofAdd q) :=
      congrArg (fun a : coreTranslationRing C => a * φ (Multiplicative.ofAdd q)) hp.symm
    _ = φ (p * Multiplicative.ofAdd q) := (φ.map_mul _ _).symm
    _ = φ (Multiplicative.ofAdd (n • s)) := by
      apply congrArg φ
      change Multiplicative.ofAdd (p.toAdd + q) = Multiplicative.ofAdd (n • s)
      exact congrArg Multiplicative.ofAdd hpq
    _ = _ := by rw [ofAdd_nsmul, φ.map_pow]

/-- Every regular power is the denominator of the SAME literal finite free
object at that stage; this uses no uniqueness of the free rank. -/
public theorem finiteFreeRowRegularDenominator_pow_eq_free (n : ℕ) :
    (finiteFreeRowRegularDenominator R) ^ n =
      coreTranslationDenominator (FGProjectiveCat.IdempotentModel R)
        (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)) := by
  apply Subtype.ext
  change
    (MonoidAlgebra.of ℤ (Multiplicative (Skeleton (FGProjectiveCat.IdempotentModel R)))
      (Multiplicative.ofAdd (toSkeleton
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ))))) ^ n =
      MonoidAlgebra.of ℤ (Multiplicative (Skeleton (FGProjectiveCat.IdempotentModel R)))
        (Multiplicative.ofAdd (toSkeleton
          ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))
  rw [RingK0.idempotentFreeSkeletonClass_eq_nsmul_regular R n,
    ofAdd_nsmul, map_pow]

variable {V : Type v} [AddCommMonoid V]
  [Module (coreTranslationRing (FGProjectiveCat.IdempotentModel R)) V]

/-- Every element of the original module localization has a regular-power
fraction representative. The numerator uses the original module action. -/
public theorem finiteFreeRowLocalization_exists_regular_fraction
    (z : LocalizedModule (coreTranslationDenominators (FGProjectiveCat.IdempotentModel R)) V) :
    ∃ (n : ℕ) (x : V), z = LocalizedModule.mk x ((finiteFreeRowRegularDenominator R) ^ n) := by
  refine LocalizedModule.induction_on (fun x d => ?_) z
  obtain ⟨n, e, he⟩ := finiteFreeRowDenominator_exists_complement R d
  refine ⟨n, e • x, ?_⟩
  calc
    LocalizedModule.mk x d = LocalizedModule.mk (e • x) (d * e) :=
      (LocalizedModule.mk_cancel_common_right d e x).symm
    _ = _ := congrArg (fun t => LocalizedModule.mk (e • x) t) he

/-- Equality of two regular-power fractions is eventual equality under the SAME
regular action, with the exact cross-denominator stabilization exponents. -/
public theorem finiteFreeRowLocalization_mk_eq_iff_eventual
    (x y : V) (n m : ℕ) :
    LocalizedModule.mk x ((finiteFreeRowRegularDenominator R) ^ n) =
        LocalizedModule.mk y ((finiteFreeRowRegularDenominator R) ^ m) ↔
      ∃ k : ℕ,
        ((finiteFreeRowRegularDenominator R) ^ (k + m)) • x =
          ((finiteFreeRowRegularDenominator R) ^ (k + n)) • y := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := LocalizedModule.mk_eq.mp h
    obtain ⟨k, e, he⟩ := finiteFreeRowDenominator_exists_complement R d
    have h' := congrArg (fun z : V => e • z) hd
    have hCollapse (a : ℕ) (z : V) :
        e • (d • (((finiteFreeRowRegularDenominator R) ^ a) • z)) =
          ((finiteFreeRowRegularDenominator R) ^ (k + a)) • z := by
      rw [← mul_smul, mul_comm e d, he, ← mul_smul, ← pow_add]
    exact ⟨k, (hCollapse m x).symm.trans (h'.trans (hCollapse n y))⟩
  · rintro ⟨k, hk⟩
    apply LocalizedModule.mk_eq.mpr
    refine ⟨(finiteFreeRowRegularDenominator R) ^ k, ?_⟩
    simpa only [pow_add, mul_smul] using hk

/-- The same equality criterion with a common literal stage, as required by the
original regular-stabilization directed system. No unique free rank is used. -/
public theorem finiteFreeRowLocalization_mk_eq_iff_common_stage
    (x y : V) (n m : ℕ) :
    LocalizedModule.mk x ((finiteFreeRowRegularDenominator R) ^ n) =
        LocalizedModule.mk y ((finiteFreeRowRegularDenominator R) ^ m) ↔
      ∃ t : ℕ, n ≤ t ∧ m ≤ t ∧
        ((finiteFreeRowRegularDenominator R) ^ (t - n)) • x =
          ((finiteFreeRowRegularDenominator R) ^ (t - m)) • y := by
  rw [finiteFreeRowLocalization_mk_eq_iff_eventual]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + n + m, by omega, by omega, ?_⟩
    have hn : k + n + m - n = k + m := by omega
    have hm : k + n + m - m = k + n := by omega
    simpa only [hn, hm] using hk
  · rintro ⟨t, hn, hm, ht⟩
    have h := congrArg (fun z : V =>
      ((finiteFreeRowRegularDenominator R) ^ (n + m)) • z) ht
    have hLeft : n + m + (t - n) = t + m := by omega
    have hRight : n + m + (t - m) = t + n := by omega
    refine ⟨t, ?_⟩
    simpa only [← mul_smul, ← pow_add, hLeft, hRight] using h

end AlgebraicKTheory.StableGL
