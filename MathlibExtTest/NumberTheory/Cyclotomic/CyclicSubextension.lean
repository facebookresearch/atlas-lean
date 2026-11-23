/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.CyclicSubextension

@[expose] public section

open NumberField

universe u

-- exactSource consumer, with the original binders.
example (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (a : ℕ) :
    ∃ (k : ℕ) (L : IntermediateField K (CyclotomicField (p ^ k) K)),
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧ Module.finrank K L = p ^ a :=
  NumberField.exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow K p a

example :
    ∀ (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (a : ℕ),
      ∃ (k : ℕ) (L : IntermediateField K (CyclotomicField (p ^ k) K)),
        IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧ Module.finrank K L = p ^ a :=
  @NumberField.exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow

-- Higher-universe consumer.
example (K : Type u) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (a : ℕ) :
    ∃ (k : ℕ) (L : IntermediateField K (CyclotomicField (p ^ k) K)),
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧ Module.finrank K L = p ^ a :=
  NumberField.exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow K p a

-- Boundary case: `a = 0` asks for a degree-one (hence trivial) cyclic
-- Galois intermediate field.
example (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    ∃ (k : ℕ) (L : IntermediateField K (CyclotomicField (p ^ k) K)),
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧ Module.finrank K L = 1 := by
  simpa using
    NumberField.exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow K p 0
