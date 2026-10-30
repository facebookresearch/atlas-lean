/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.HeckeOperator

@[expose] public section

open MulAction AbstractHeckeOperator
open scoped Pointwise

noncomputable example (G : Type*) [Group G] (U V : Subgroup G) (g : G)
    (h : (QuotientGroup.mk '' (U * ({g} : Set G)) : Set (G ⧸ V)).Finite)
    (A : Type*) [AddCommMonoid A] [DistribMulAction G A] :
    fixedPoints V A →+ fixedPoints U A :=
  HeckeOperator_addMonoidHom h

noncomputable example (G : Type*) [Group G] (U V : Subgroup G) (g : G)
    (h : (QuotientGroup.mk '' (U * ({g} : Set G)) : Set (G ⧸ V)).Finite)
    (A : Type*) [AddCommMonoid A] [DistribMulAction G A]
    (R : Type*) [Semiring R] [Module R A] [SMulCommClass G R A] :
    fixedPoints V A →ₗ[R] fixedPoints U A :=
  HeckeOperator (R := R) g U V h

example (G : Type*) [Group G] (A : Type*) [AddCommMonoid A] [DistribMulAction G A]
    (a b : fixedPoints G A) : ((a + b : fixedPoints G A) : A) = (a : A) + b := by
  simp

example (G : Type*) [Group G] (A : Type*) [AddCommMonoid A] [DistribMulAction G A]
    (R : Type*) [Semiring R] [Module R A] [SMulCommClass G R A]
    (r : R) (a : fixedPoints G A) : ((r • a : fixedPoints G A) : A) = r • (a : A) := by
  simp

example (G : Type*) [Group G] (A : Type*) [AddCommMonoid A] [DistribMulAction G A]
    (R : Type*) [Semiring R] [Module R A] [SMulCommClass G R A]
    (r s : R) (a : fixedPoints G A) : (r + s) • a = r • a + s • a := by
  exact add_smul r s a

noncomputable example (G : Type*) [Group G] (A : Type*) [AddCommMonoid A]
    [DistribMulAction G A] (R : Type*) [Semiring R] [Module R A] [SMulCommClass G R A]
    (g : G) (a : fixedPoints (⊥ : Subgroup G) A) :
    ((HeckeOperator (R := R) g ⊥ ⊥ (by simp) a : fixedPoints (⊥ : Subgroup G) A) : A) =
      g • (a : A) := by
  rw [HeckeOperator_apply]
  simp
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (⊥ : Subgroup G) g
  have hva : (v : G) • (a : A) = a := a.2 v
  rw [hv, mul_smul, hva]

noncomputable example :
    ((HeckeOperator (R := ℕ) (1 : Units ℕ) ⊥ ⊥ (by simp)
      (⟨1, by simp⟩ : fixedPoints (⊥ : Subgroup (Units ℕ)) ℕ) :
        fixedPoints (⊥ : Subgroup (Units ℕ)) ℕ) : ℕ) = 1 := by
  rw [HeckeOperator_apply]
  simp
  change Quotient.out (QuotientGroup.mk (1 : Units ℕ) : Units ℕ ⧸ (⊥ : Subgroup (Units ℕ))) •
    (1 : ℕ) = 1
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (⊥ : Subgroup (Units ℕ)) (1 : Units ℕ)
  rw [hv]
  have hv1 : (v : Units ℕ) = 1 := Subgroup.mem_bot.mp v.2
  rw [hv1]
  simp
