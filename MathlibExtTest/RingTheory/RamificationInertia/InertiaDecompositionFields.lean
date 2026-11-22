/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.RamificationInertia.InertiaDecompositionFields

/-!
# Inertia/decomposition field tests

Consumption tests for ATLAS `NumberTheoryI` Corollary 7.14: the generic
example restates the main theorem, the two one-direction examples apply its
components, and the finite-group example exercises the cardinality helper
`Subgroup.le_of_card_subgroupOf_eq` on permutations of a three-element type.
-/

open Ideal

/-- The cardinality helper: the full subgroup is contained in itself, proved
through the cardinality of its intersection with itself. -/
example : (⊤ : Subgroup (Equiv.Perm (Fin 3))) ≤ (⊤ : Subgroup (Equiv.Perm (Fin 3))) :=
  Subgroup.le_of_card_subgroupOf_eq
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv)

/-- Restatement of Corollary 7.14, applying the main theorem. -/
example {K L : Type*} [Field K] [Field L] [Algebra K L]
    {B : Type*} [CommRing B] [MulSemiringAction (L ≃ₐ[K] L) B]
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B] :
    (P_E.ramificationIdx A = 1 ↔
      E ≤ IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L))) ∧
    ((P_E.ramificationIdx A = 1 ∧ P_E.inertiaDeg A = 1) ↔
      E ≤ IntermediateField.fixedField
        (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P)) :=
  Ideal.ramificationIdx_inertiaDeg_eq_one_iff_le_inertiaField_decompositionField
    K L P p E C_E P_E

/-- From `e = 1`, the intermediate field lies below the inertia field. -/
example {K L : Type*} [Field K] [Field L] [Algebra K L]
    {B : Type*} [CommRing B] [MulSemiringAction (L ≃ₐ[K] L) B]
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (h : P_E.ramificationIdx A = 1) :
    E ≤ IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L)) :=
  (Ideal.ramificationIdx_inertiaDeg_eq_one_iff_le_inertiaField_decompositionField
    K L P p E C_E P_E).1.mp h

/-- From `e = f = 1`, the intermediate field lies below the decomposition field. -/
example {K L : Type*} [Field K] [Field L] [Algebra K L]
    {B : Type*} [CommRing B] [MulSemiringAction (L ≃ₐ[K] L) B]
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    (h : P_E.ramificationIdx A = 1 ∧ P_E.inertiaDeg A = 1) :
    E ≤ IntermediateField.fixedField
      (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P) :=
  (Ideal.ramificationIdx_inertiaDeg_eq_one_iff_le_inertiaField_decompositionField
    K L P p E C_E P_E).2.mp h
