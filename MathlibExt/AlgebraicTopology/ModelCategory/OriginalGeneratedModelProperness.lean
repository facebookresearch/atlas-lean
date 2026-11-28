/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Properness prerequisites from the actual I/K weak factorization systems

The original K-left class is stable under cobase change and the original
I-right class under base change. The exact recognition equations identify
these with the constructed model's trivial classes. These closure statements
are prerequisites for properness arguments; they do not assert preservation
of every weak equivalence by a pushout or pullback.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.OriginalGeneratedModel

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [HasFiniteColimits C]
  (I K W : MorphismProperty C)
  (hW : W.HasTwoOutOfThreeProperty) (hRight : I.rlp = K.rlp ⊓ W)
  (hAcyclic : K.rlp.llp ≤ W)
  (givenI : FunctorialFactorizationData I.rlp.llp I.rlp)
  (givenK : FunctorialFactorizationData K.rlp.llp K.rlp)

/-- The actual constructed trivial-left class inherits the original K-left closure. -/
theorem trivialCofibrations_stableUnderCobaseChange :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (trivialCofibrations C).IsStableUnderCobaseChange := by
  change (I.rlp.llp ⊓ W).IsStableUnderCobaseChange
  rw [← left_class_eq I K W hW hRight hAcyclic givenK]
  infer_instance

/-- The actual constructed trivial-right class inherits the original I-right closure. -/
theorem trivialFibrations_stableUnderBaseChange :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (trivialFibrations C).IsStableUnderBaseChange := by
  change (K.rlp ⊓ W).IsStableUnderBaseChange
  rw [← hRight]
  infer_instance

omit [HasFiniteLimits C] [HasFiniteColimits C] in
include hAcyclic in
/-- A pushout of a genuine original K-left map remains in the candidate weak class. -/
theorem weak_of_pushout_of_original_K_left
    {A B X Y : C} {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (square : IsPushout i a b j) (hi : K.rlp.llp i) : W j :=
  hAcyclic _ ((K.rlp.llp).of_isPushout square.flip hi)

omit [HasFiniteLimits C] [HasFiniteColimits C] in
include hRight in
/-- A pullback of an original I-right map remains weak by the necessary right-class law. -/
theorem weak_of_pullback_of_original_I_right
    {A B X Y : C} {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (square : IsPullback i a b j) (hj : I.rlp j) : W i := by
  have hi : I.rlp i := (I.rlp).of_isPullback square.flip hj
  have h : (K.rlp ⊓ W) i := by rwa [← hRight]
  exact h.2

end HomotopicalAlgebra.OriginalGeneratedModel
