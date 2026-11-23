/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.NativeRingK0Models

/-!
# Relations of the ordinary ring `K₀`

Isomorphic finite projective modules have the same class, and a decomposition
`P ≅ Q ⊞ T` gives `[P] = [Q] + [T]`, with both summands on the right. The comparison map to
the `K₀` of the enhanced perfect category sends a module class to the class of its
selected perfect object.
-/

open CategoryTheory
open MathlibExt.AlgebraicGeometry.OrdinarySchemeModuleFamilies
open MathlibExt.AlgebraicGeometry.NativeRingK0Models

variable {A : OrdinaryAlgebras}

example (P Q : FiniteProjective A) (e : P.module ≅ Q.module) :
    moduleClass A P = moduleClass A Q := by
  rw [moduleClass, moduleClass, QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure (Or.inl ⟨P, Q, ⟨e⟩, rfl⟩)

example (P Q T : FiniteProjective A) (e : P.module ≅ Q.module ⊞ T.module) :
    moduleClass A P = moduleClass A Q + moduleClass A T := by
  rw [moduleClass, moduleClass, moduleClass, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← sub_sub]
  exact AddSubgroup.subset_closure (Or.inr ⟨P, Q, T, ⟨e⟩, rfl⟩)
