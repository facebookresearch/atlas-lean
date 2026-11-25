/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

import MathlibExt.AlgebraicTopology.ModelCategory.ActionProjective

/-!
# Public clients of the projective action-model factory

The original cardinal and bottom are retained. The tests select the actual
public model and its complete created classes, including permutation arity zero.
-/

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace MathlibExtTest.ActionProjective

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

example : ModelCategory (Action C (Equiv.Perm (Fin 0))) :=
  HomotopicalAlgebra.ActionProjective.modelCategory d (Equiv.Perm (Fin 0))

example :
    letI := HomotopicalAlgebra.ActionProjective.modelCategory d (Equiv.Perm (Fin 0))
    weakEquivalences (Action C (Equiv.Perm (Fin 0))) =
      (weakEquivalences C).inverseImage (Action.forget C (Equiv.Perm (Fin 0))) :=
  HomotopicalAlgebra.ActionProjective.weakEquivalences_eq d (Equiv.Perm (Fin 0))

example :
    letI := HomotopicalAlgebra.ActionProjective.modelCategory d (Equiv.Perm (Fin 0))
    trivialFibrations (Action C (Equiv.Perm (Fin 0))) =
      (trivialFibrations C).inverseImage (Action.forget C (Equiv.Perm (Fin 0))) :=
  HomotopicalAlgebra.ActionProjective.trivialFibrations_eq d (Equiv.Perm (Fin 0))

example (n : ℕ) :
    letI := HomotopicalAlgebra.ActionProjective.modelCategory d (Equiv.Perm (Fin n))
    fibrations (Action C (Equiv.Perm (Fin n))) =
      (fibrations C).inverseImage (Action.forget C (Equiv.Perm (Fin n))) :=
  HomotopicalAlgebra.ActionProjective.fibrations_eq d (Equiv.Perm (Fin n))

example (n : ℕ) {X Y : Action C (Equiv.Perm (Fin n))} (f : X ⟶ Y) :
    letI := HomotopicalAlgebra.ActionProjective.modelCategory d (Equiv.Perm (Fin n))
    WeakEquivalence f ↔ WeakEquivalence f.hom := by
  let := HomotopicalAlgebra.ActionProjective.modelCategory d (Equiv.Perm (Fin n))
  rw [weakEquivalence_iff, weakEquivalence_iff,
    HomotopicalAlgebra.ActionProjective.weakEquivalences_eq d (Equiv.Perm (Fin n))]
  rfl

end MathlibExtTest.ActionProjective
