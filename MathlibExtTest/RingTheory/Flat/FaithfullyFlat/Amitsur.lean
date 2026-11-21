/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`
and
`P2M/Sol/S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Flat.FaithfullyFlat.Amitsur

@[expose] public section

set_option autoImplicit false

open TensorProduct

universe u v w

/-- Consumer at the original binder universes. -/
private theorem exactSource
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b :=
  Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul hb

/-- Consumer in a higher universe, exercising universe polymorphism. -/
private theorem exactSource_higherUniverse
    {A : Type u} {B : Type (max v w)} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b :=
  Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul hb

/-- Boundary: without faithful flatness the conclusion can fail; for
`ℤ → ℤ × ℤ` the element `(0, 1)` satisfies the tensor identity only
after base change, and it is not in the image of `algebraMap`. Here we
record the elementary direction: elements from `A` always satisfy the
tensor identity. -/
private theorem algebraMap_satisfies_identity
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) :
    algebraMap A B a ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] algebraMap A B a := by
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

/-- The identity algebra satisfies the conclusion trivially. -/
private theorem self_example (b : ℤ) :
    ∃ a : ℤ, algebraMap ℤ ℤ a = b :=
  Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    (algebraMap_satisfies_identity b)
