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
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

@[expose] public section

set_option autoImplicit false

open TensorProduct

namespace Module.FaithfullyFlat

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

/-- **Amitsur exactness in degree zero.** Let `B` be a commutative `A`-algebra that is
faithfully flat as an `A`-module. If `b : B` satisfies `b ⊗ 1 = 1 ⊗ b` in `B ⊗[A] B`, then
`b = algebraMap A B a` for some `a : A`.

This is the elementwise form of Mathlib's `Algebra.IsEffective.of_faithfullyFlat`: for such `B`,
the sequence `A → B → B ⊗[A] B`, whose second map is `b ↦ b ⊗ 1 - 1 ⊗ b`, is exact. -/
public theorem exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b := by
  obtain ⟨a, ha⟩ := (Algebra.IsEffective.of_faithfullyFlat A B b).mp
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, hb, sub_self])
  exact ⟨a, ha⟩

end Module.FaithfullyFlat
