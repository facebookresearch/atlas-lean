/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.HenselianFixedField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Padics.PadicNumbers

@[expose] public section

universe u

-- Exact-source consumer, with the original binders.
private theorem exactSource
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) :=
  ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn A I hI

-- The ring in the conclusion consists of the elements of `A` fixed by every element of `I`.
example {K L : Type u} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (x : L) :
    x ∈ A.toSubring ⊓ (IntermediateField.fixedField I).toSubring ↔
      x ∈ A ∧ ∀ σ ∈ I, σ x = x := by
  rw [Subring.mem_inf]
  exact and_congr Iff.rfl (IntermediateField.mem_fixedField_iff I x)

-- Higher-universe consumer: the fields live in `Type 1`.
example
    {K L : Type 1} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) :=
  ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn A I hI

-- Concrete instance: `ℚ̄ / ℚ`, with `I` the whole inertia subgroup of `A`, so the ring is the
-- valuation ring of `A` on the inertia field.
example (A : ValuationSubring (AlgebraicClosure ℚ)) :
    HenselianLocalRing ↥(A.toSubring ⊓
      (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)).toSubring) :=
  ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn A _ le_rfl

-- Boundary: for the trivial subgroup the fixed field is all of `L`, so the
-- intersection is the valuation subring itself, which is Henselian.
example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L) :
    HenselianLocalRing ↥A.toSubring := by
  have h := ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
    A (⊥ : Subgroup (L ≃ₐ[K] L)) bot_le
  have hsub : A.toSubring ⊓
      (IntermediateField.fixedField (⊥ : Subgroup (L ≃ₐ[K] L))).toSubring
      = A.toSubring := by
    ext x
    simp
  rwa [hsub] at h

-- Boundary: algebraic closedness cannot be dropped. For `L = K = ℚ` and `I = ⊥` the statement
-- without `IsAlgClosed L` fails: the `5`-adic valuation ring of `ℚ` is not Henselian, because
-- `X ^ 2 + 1` has the simple root `2` modulo `5` but no root in `ℚ`.
open Polynomial IsLocalRing in
example : ¬ ∀ (A : ValuationSubring ℚ) (I : Subgroup (ℚ ≃ₐ[ℚ] ℚ)), I ≤ A.inertiaSubgroupIn ℚ →
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) := by
  intro h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set A := (Rat.padicValuation 5).valuationSubring
  set S := A.toSubring ⊓ (IntermediateField.fixedField (⊥ : Subgroup (ℚ ≃ₐ[ℚ] ℚ))).toSubring
  have hS := h A ⊥ bot_le
  have hmem : ∀ x : ℚ, x ∈ S ↔ ¬ 5 ∣ x.den := fun x => by
    rw [Subring.mem_inf, IntermediateField.fixedField_bot]
    simp [A, Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff]
  obtain ⟨a, ha, -⟩ := hS.is_henselian (X ^ 2 + C 1) (monic_X_pow_add_C 1 two_ne_zero)
    ⟨2, (hmem 2).mpr (by simp)⟩
    (by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have h5 : ((u⁻¹ : Sˣ) : ℚ) * 5 = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        simp only [eval_add, eval_pow, eval_X, eval_C, Subring.coe_mul, Subring.coe_add,
          Subring.coe_pow, OneMemClass.coe_one] at this
        norm_num at this
        exact this
      have hu' : ((u⁻¹ : Sˣ) : ℚ) = 5⁻¹ := eq_inv_of_mul_eq_one_left h5
      have := (hmem _).mp ((u⁻¹ : Sˣ) : S).2
      rw [hu'] at this
      exact this (by simp))
    (by
      refine IsUnit.of_mul_eq_one (⟨4⁻¹, (hmem _).mpr (by simp)⟩ : S) (Subtype.ext ?_)
      simp
      norm_num)
  have h0 : (a : ℚ) ^ 2 + 1 = 0 := by
    have := congrArg Subtype.val ha.eq_zero
    simpa using this
  have : (0 : ℚ) < (a : ℚ) ^ 2 + 1 := by positivity
  linarith

-- Accordingly, the theorem does not apply over `ℚ`, which is not algebraically closed.
example : True := by
  fail_if_success
    have := ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
      (⊤ : ValuationSubring ℚ) (⊥ : Subgroup (ℚ ≃ₐ[ℚ] ℚ)) bot_le
  trivial
