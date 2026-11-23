/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.HeckeOperator
import Mathlib.Data.Set.Card

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

end

open MulAction AbstractHeckeOperator
open scoped Pointwise

namespace HeckeOperatorMultiCosetTest

private abbrev S3 := Equiv.Perm (Fin 3)

private abbrev Coordinates := Fin 3 → ℤ

private def swap01 : S3 := Equiv.swap 0 1

private def cycle012 : S3 := Equiv.swap 0 1 * Equiv.swap 1 2

local instance : SMul S3 Coordinates where
  smul σ a i := a (σ⁻¹ i)

local instance : DistribMulAction S3 Coordinates where
  one_smul a := by
    rfl
  mul_smul σ τ a := by
    rfl
  smul_zero σ := by
    rfl
  smul_add σ a b := by
    rfl

local instance : SMulCommClass S3 ℕ Coordinates where
  smul_comm σ n a := by
    rfl

private def U : Subgroup S3 where
  carrier := {1, swap01}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a = 1 ∨ a = swap01 at ha
    change b = 1 ∨ b = swap01 at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [swap01]
  inv_mem' := by
    intro a ha
    change a = 1 ∨ a = swap01 at ha
    rcases ha with rfl | rfl <;> simp [swap01]

private def input : Coordinates := fun i ↦ if i = 2 then 2 else 1

private abbrev expected : Coordinates := fun i ↦ if i = 2 then 2 else 3

private lemma swap01_fixed : swap01 • input = input := by
  decide

private def fixedInput : fixedPoints U Coordinates :=
  ⟨input, fun u ↦ by
    have hu := u.2
    change (u : S3) = 1 ∨ (u : S3) = swap01 at hu
    rcases hu with hu | hu
    · change (u : S3) • input = input
      rw [hu]
      exact one_smul S3 input
    · change (u : S3) • input = input
      rw [hu]
      exact swap01_fixed⟩

private lemma doubleCoset :
    (U : Set S3) * {cycle012} = {cycle012, swap01 * cycle012} := by
  ext x
  simp only [Set.mem_mul, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, hu, b, rfl, rfl⟩
    rcases hu with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨1, by simp [U], cycle012, rfl, one_mul _⟩
    · exact ⟨swap01, by simp [U], cycle012, rfl, rfl⟩

private lemma wrongOrientationDoubleCoset :
    ({cycle012} : Set S3) * U = {cycle012, cycle012 * swap01} := by
  ext x
  simp only [Set.mem_mul, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl, u, hu, rfl⟩
    rcases hu with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨cycle012, rfl, 1, by simp [U], mul_one _⟩
    · exact ⟨cycle012, rfl, swap01, by simp [U], rfl⟩

private lemma quotientImage :
    (QuotientGroup.mk (s := U)) '' ((U : Set S3) * {cycle012}) =
      {QuotientGroup.mk (s := U) cycle012,
        QuotientGroup.mk (s := U) (swap01 * cycle012)} := by
  rw [doubleCoset]
  simp

private lemma quotient_ne :
    (QuotientGroup.mk cycle012 : S3 ⧸ U) ≠
      QuotientGroup.mk (swap01 * cycle012) := by
  intro h
  have hm := QuotientGroup.eq.mp h
  change cycle012⁻¹ * (swap01 * cycle012) = 1 ∨
    cycle012⁻¹ * (swap01 * cycle012) = swap01 at hm
  rcases hm with hm | hm
  · have hn : cycle012⁻¹ * (swap01 * cycle012) ≠ (1 : S3) := by decide
    exact hn hm
  · have hn : cycle012⁻¹ * (swap01 * cycle012) ≠ swap01 := by decide
    exact hn hm

example :
    ((QuotientGroup.mk (s := U)) ''
      ((U : Set S3) * {cycle012}) : Set (S3 ⧸ U)).ncard = 2 := by
  rw [quotientImage, Set.ncard_pair]
  simp [quotient_ne]

example :
    ((QuotientGroup.mk (s := U)) ''
      (({cycle012} : Set S3) * U) : Set (S3 ⧸ U)).ncard = 1 := by
  rw [wrongOrientationDoubleCoset, Set.image_insert_eq, Set.image_singleton]
  rw [QuotientGroup.mk_mul_of_mem cycle012 (by simp [U])]
  simp

private lemma mk_bijOn : Set.BijOn (QuotientGroup.mk : S3 → S3 ⧸ U)
    {cycle012, swap01 * cycle012}
    (QuotientGroup.mk '' ((U : Set S3) * {cycle012})) := by
  rw [quotientImage]
  have hinj : Set.InjOn (QuotientGroup.mk : S3 → S3 ⧸ U)
      {cycle012, swap01 * cycle012} := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact (quotient_ne hxy).elim
    · exact (quotient_ne hxy.symm).elim
    · rfl
  simpa only [Set.image_insert_eq, Set.image_singleton] using hinj.bijOn_image

private lemma representative_ne : cycle012 ≠ swap01 * cycle012 := by
  decide

private lemma contribution_sum :
    cycle012 • input + (swap01 * cycle012) • input = expected := by
  decide

private lemma expected_ne_single_coset : expected ≠ cycle012 • input := by
  decide

example : (fun i : Fin 3 ↦ if i = 2 then 2 else 3) ≠ cycle012 • input := by
  simpa [expected] using expected_ne_single_coset

private lemma sum_value :
    ∑ᶠ gi ∈ Quotient.out ''
      ((QuotientGroup.mk (s := U)) '' ((U : Set S3) * {cycle012})),
      gi • input = expected := by
  calc
    _ = ∑ᶠ gi ∈ ({cycle012, swap01 * cycle012} : Set S3),
        gi • (fixedInput : Coordinates) :=
      (eq_finsum_quotient_out_of_bijOn' fixedInput mk_bijOn).symm
    _ = expected := by
      rw [finsum_mem_pair representative_ne]
      exact contribution_sum

noncomputable example :
    ((HeckeOperator_addMonoidHom (U := U) (V := U) (g := cycle012)
      (Set.toFinite _) fixedInput : fixedPoints U Coordinates) : Coordinates) =
      (fun i ↦ if i = 2 then 2 else 3) := by
  change ∑ᶠ gi ∈ Quotient.out ''
    ((QuotientGroup.mk (s := U)) '' ((U : Set S3) * {cycle012})),
    gi • input = fun i ↦ if i = 2 then 2 else 3
  simpa [expected] using sum_value

noncomputable example :
    ((HeckeOperator (R := ℕ) cycle012 U U (Set.toFinite _) fixedInput :
      fixedPoints U Coordinates) : Coordinates) =
      (fun i ↦ if i = 2 then 2 else 3) := by
  rw [HeckeOperator_apply]
  change ∑ᶠ gi ∈ Quotient.out ''
    ((QuotientGroup.mk (s := U)) '' ((U : Set S3) * {cycle012})),
    gi • input = fun i ↦ if i = 2 then 2 else 3
  simpa [expected] using sum_value

end HeckeOperatorMultiCosetTest
