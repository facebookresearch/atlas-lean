/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.GroupClassesShared

open MathlibExt.GroupTheory.GroupClassesShared

-- The bottom subgroup of a finite group has finite index and a series of length zero.
example (G : Type*) [Group G] [Finite G] : IsAlmostPolycyclic G :=
  ⟨⊥, inferInstance, 0, fun _ ↦ ⊥, rfl, Subsingleton.elim _ _, Fin.elim0⟩
