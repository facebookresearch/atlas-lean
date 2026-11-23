/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AbstractHeckeOperator.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream FLT file is a port of, in whole,
`FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean`
from the FLT project — the Lean formalisation of Fermat's Last Theorem led
by Kevin Buzzard at Imperial College London
(https://github.com/ImperialCollegeLondon/FLT):
Copyright (c) 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang,
Matthew Jasper.
Released under the Apache License, Version 2.0.
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Abstract Hecke operators

For subgroups `U, V` of a group `G` and `g : G`, the Hecke operator
`T(g) : fixedPoints V A →ₗ[R] fixedPoints U A` sums a `V`-fixed vector
over representatives of the double coset `U g V`. Fixed points of a group
action on an additive commutative monoid carry the induced module
structure used here.
-/

@[expose] public section

namespace FixedPoints

open MulAction

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G}

instance : AddCommMonoid (fixedPoints G A) :=
  AddSubmonoid.toAddCommMonoid (FixedPoints.addSubmonoid G A)

@[simp, norm_cast]
lemma coe_zero : ((0 : fixedPoints G A) : A) = 0 := rfl

@[simp, norm_cast]
lemma coe_add (a b : fixedPoints G A) :
    ((a + b : fixedPoints G A) : A) = a + b := rfl

variable {R : Type*}

instance [SMul R A] [SMulCommClass G R A] :
    SMul R (fixedPoints G A) where
  smul r a := ⟨r • a.1, fun g ↦ by rw [smul_comm, a.2]⟩

@[simp, norm_cast]
lemma coe_smul [SMul R A] [SMulCommClass G R A] (r : R) (a : fixedPoints G A) :
    ((r • a : fixedPoints G A) : A) = r • a := rfl

instance [Monoid R] [MulAction R A] [SMulCommClass G R A] :
    MulAction R (fixedPoints G A) where
  one_smul a := by
    ext
    push_cast
    simp
  mul_smul r s a := by
    ext
    push_cast
    simp [mul_smul]

instance module [Semiring R] [Module R A] [SMulCommClass G R A] : Module R (fixedPoints G A) where
  one_smul a := one_smul _ _
  mul_smul r s a := mul_smul _ _ _
  smul_zero a := by
    ext
    exact smul_zero _
  smul_add r s a := by
    ext
    exact smul_add _ _ _
  add_smul r s a := by
    ext
    exact add_smul _ _ _
  zero_smul a := by
    ext
    exact zero_smul _ _

end FixedPoints

open scoped Pointwise

variable (G : Type*) [Group G] (U : Subgroup G) (X : Set G) {u : G} in
lemma Set.bijOn_smul (hu : u ∈ U) :
    Set.BijOn (fun x ↦ u • x) ((U : Set G) * X) (U * X) := by
  refine ⟨?_, Set.injOn_of_injective (MulAction.injective u), ?_⟩
  · rintro x ⟨u', hu', x, hx, rfl⟩
    exact ⟨u * u', mul_mem hu hu', x, hx, by simp [mul_assoc]⟩
  · rintro x ⟨u', hu', x, hx, rfl⟩
    exact ⟨(u⁻¹ * u') * x, ⟨u⁻¹ * u', mul_mem (inv_mem hu) hu', x, hx, rfl⟩, by simp [mul_assoc]⟩

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G} {U V : Subgroup G}

open MulAction

variable (h : (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)).Finite)

open ConjAct

namespace AbstractHeckeOperator

lemma eq_finsum_quotient_out_of_bijOn' (a : fixedPoints V A)
    {X : Set (G ⧸ V)}
    {s : Set G} (hs : s.BijOn (QuotientGroup.mk : G → G ⧸ V) X) :
    ∑ᶠ g ∈ s, g • (a : A) = ∑ᶠ g ∈ Quotient.out '' X, g • (a : A) := by
  let e (g : G) : G := Quotient.out (QuotientGroup.mk g : G ⧸ V)
  have he₀ : Set.BijOn e s (Quotient.out '' X) := by
    refine Set.BijOn.comp ?_ hs
    exact Set.InjOn.bijOn_image <| Set.injOn_of_injective Quotient.out_injective
  have he₁ : ∀ g ∈ s, g • (a : A) = (Quotient.out (QuotientGroup.mk g : G ⧸ V)) • a := by
    intro g hgs
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
    rw [hv, mul_smul, (show (v : G) • (a : A) = a from a.2 v)]
  exact finsum_mem_eq_of_bijOn e he₀ he₁

/-- The Hecke operator `T(g)` as a function on fixed points. -/
noncomputable def HeckeOperator_toFun (a : fixedPoints V A) : fixedPoints U A :=
  ⟨∑ᶠ gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)), gᵢ • a.1, by
  rintro ⟨u, huU⟩
  rw [smul_finsum_mem (h.image Quotient.out), ← eq_finsum_quotient_out_of_bijOn' a]
  · rw [finsum_mem_eq_of_bijOn (fun g ↦ u • g)]
    · exact Set.InjOn.bijOn_image <| Set.injOn_of_injective (MulAction.injective u)
    · simp [mul_smul]
  · apply (Set.bijOn_comp_iff (Set.injOn_of_injective (MulAction.injective u))).1
    change Set.BijOn ((fun xbar ↦ u • xbar) ∘ (QuotientGroup.mk : G → G ⧸ V)) _ _
    rw [Set.bijOn_comp_iff]
    · rw [← Set.image_comp]
      simp only [Function.comp_apply, Quotient.out_eq, Set.image_id']
      refine Set.bijOn_image_image (f := fun (x : G) ↦ u • x) (p₁ := (QuotientGroup.mk : G → G ⧸ V))
        (fun a ↦ rfl) ?_ (Set.injOn_of_injective (MulAction.injective u))
      apply Set.bijOn_smul _ _ _ huU
    · refine Set.InjOn.image_of_comp ?_
      simp only [Function.comp_def, Quotient.out_eq]
      exact Function.Injective.injOn Function.injective_id
    ⟩

/-- The Hecke operator `T(g)` as an additive monoid homomorphism. -/
noncomputable def HeckeOperator_addMonoidHom : fixedPoints V A →+ fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_zero' := by
    ext
    simp [HeckeOperator_toFun]
  map_add' a b := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_add, smul_add,
      finsum_mem_add_distrib (h.image Quotient.out)]

variable {R : Type*} [Semiring R] [Module R A] [SMulCommClass G R A]

variable (g U V) in
/-- The Hecke operator `T(g)` as a linear map on fixed points. -/
noncomputable def HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_add' a b := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_add, smul_add,
      finsum_mem_add_distrib (h.image Quotient.out)]
  map_smul' r a := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_smul, smul_comm,
      smul_finsum_mem (h.image Quotient.out), RingHom.id_apply]

lemma HeckeOperator_apply (a : fixedPoints V A) :
    (HeckeOperator (R := R) g U V h a : A) =
    ∑ᶠ (gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V))), gᵢ • (a : A) :=
  rfl

end AbstractHeckeOperator
