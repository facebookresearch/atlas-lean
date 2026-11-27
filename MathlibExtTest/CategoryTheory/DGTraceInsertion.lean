/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.DGCalabiYauMapModels

/-!
# Placement of the identity in the trace insertion

For a two-object cyclic word `(a, b)` rooted at `u`, with `a : u → v` and `b : v → u`, the
inserted two-sided bar path runs through `[v, u]`. Deleting its first intermediate vertex leaves
`[u]`, the inserted path of the cyclic face `b ∘ a` rooted at `u`; deleting the second leaves `[v]`,
the inserted path of the closing cyclic face `a ∘ b` rooted at `v`. A prepended identity would
instead match the first bar face with a composition by the identity.
-/

namespace MathlibExtTest.CategoryTheory.DGTraceInsertion

open MathlibExt.CategoryTheory.DGModelContracts MathlibExt.CategoryTheory.DGBarDiagonalModels
open MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
open MathlibExt.CategoryTheory.DGCalabiYauMapModels

variable (C : DGCat ℚ) (u v : C)

example : (tracePathVertices (⟨u, ![v]⟩ : CyclicObjects C 1)).val = [v, u] := rfl

/-- The objects of the closing face: rotation makes `v` the root and the head face deletes `u`. -/
example : (⟨(rotatedObjects C 1 ⟨u, ![v]⟩).root,
    Fin.tail (rotatedObjects C 1 ⟨u, ![v]⟩).tail⟩ : CyclicObjects C 0) = ⟨v, ![]⟩ := by
  simp only [rotatedObjects, CyclicObjects.mk.injEq]
  exact ⟨rfl, funext fun i : Fin 0 ↦ i.elim0⟩

/-- Bar face `0` matches cyclic face `0`: root `u`, empty tail. -/
example : (deletedVertices C 0 (tracePathVertices (⟨u, ![v]⟩ : CyclicObjects C 1)) 0).val =
    (tracePathVertices (⟨u, ![]⟩ : CyclicObjects C 0)).val := rfl

/-- Bar face `1` matches the closing cyclic face: root `v`, empty tail. -/
example : (deletedVertices C 0 (tracePathVertices (⟨u, ![v]⟩ : CyclicObjects C 1)) 1).val =
    (tracePathVertices (⟨v, ![]⟩ : CyclicObjects C 0)).val := rfl

end MathlibExtTest.CategoryTheory.DGTraceInsertion
