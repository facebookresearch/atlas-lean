/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.MaximalEtaleSubalgebra

@[expose] public section

universe u v

private theorem exactSource
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A] :
    ∃ P : Subalgebra k A,
      Algebra.Etale k P ∧
      (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧
      (∀ x : A, ∃ (n : ℕ) (y : A), y ∈ P ∧ IsNilpotent (x ^ ringExpChar k ^ n - y)) :=
  Algebra.exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent k A

-- Higher-universe consumer.
example
    (k : Type (u + 1)) [Field k] (A : Type (v + 1)) [CommRing A] [Algebra k A]
    [Module.Finite k A] :
    ∃ P : Subalgebra k A,
      Algebra.Etale k P ∧
      (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧
      (∀ x : A, ∃ (n : ℕ) (y : A), y ∈ P ∧ IsNilpotent (x ^ ringExpChar k ^ n - y)) :=
  Algebra.exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent k A

-- Boundary: over an algebraically closed field the algebra itself is
-- maximal, witnessed here for the field itself.
example (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ P : Subalgebra k k,
      Algebra.Etale k P ∧
      (∀ S : Subalgebra k k, Algebra.Etale k S → S ≤ P) ∧
      (∀ x : k, ∃ (n : ℕ) (y : k), y ∈ P ∧ IsNilpotent (x ^ ringExpChar k ^ n - y)) :=
  Algebra.exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent k k
