/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DoublyTransitiveCyclicStabilizerKourovka10Problem63

open MathlibExt.GroupTheory.DoublyTransitiveCyclicStabilizerKourovka10Problem63Wanted

-- Both the original existential definition and the new proof are usable from a module import.
example {G X : Type} [Group G] [MulAction G X] [FaithfulSMul G X]
    (h₂ : MulAction.IsMultiplyPretransitive G X 2) (x : X) :
    ¬ Nonempty (MulAction.stabilizer G x ≃* Multiplicative ℤ) := by
  intro h
  exact doublyTransitiveInfiniteCyclicStabilizer_refuted
    ⟨G, X, inferInstance, inferInstance, inferInstance, h₂, x, h⟩

-- On two points, the full permutation group really is faithful and doubly transitive.
example : ¬ Nonempty (MulAction.stabilizer (Equiv.Perm (Fin 2)) (0 : Fin 2) ≃* Multiplicative ℤ) :=
  fun h ↦ doublyTransitiveInfiniteCyclicStabilizer_refuted
    ⟨Equiv.Perm (Fin 2), Fin 2, inferInstance, inferInstance, inferInstance,
      Equiv.Perm.isMultiplyPretransitive (Fin 2) 2, 0, h⟩

-- With no pair of distinct points the two-transitivity condition is vacuous.
example (x : Fin 1) :
    ¬ Nonempty (MulAction.stabilizer (Equiv.Perm (Fin 1)) x ≃* Multiplicative ℤ) :=
  fun h ↦ doublyTransitiveInfiniteCyclicStabilizer_refuted
    ⟨Equiv.Perm (Fin 1), Fin 1, inferInstance, inferInstance, inferInstance,
      Equiv.Perm.isMultiplyPretransitive (Fin 1) 2, x, h⟩
