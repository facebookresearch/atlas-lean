/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeHomSequence
import Batteries.Tactic.Lint

/-!
# Public clients of the unbounded chosen Puppe Hom sequence

The clients express actual image/kernel equality as an equality of sets,
apply third exactness to prove a full restriction-surjectivity criterion,
and compose the full source and target actions at an arbitrary stage.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OrdinaryHoChosenPuppe OrdinaryHoChosenPuppeHomSequence

namespace HomotopicalAlgebra.OrdinaryHoChosenPuppeHomSequencePublicClients

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  (Z : C) (hZ : IsZero Z) (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone ((ι).app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

local notation "Q" => (MorphismProperty.Q (weakEquivalences C))

example (F : Arrow C) [IsCofibrant F.right]
    [Cofibration ((ι).app F.left)] [Cofibration ((ι).app F.right)]
    (E : C) [IsFibrant E]
    (hCone : weakEquivalences C (toZero Z hZ ((cone).obj F.right))) :
    Function.Surjective (OrdinaryHoPuppeCofiberNull.precomposition
      (suspensionMap cone ι c hc Z hZ F.hom) E) ↔
      ∀ g : (Q).obj (suspensionCone cone ι c Z hZ F.left).pt ⟶ (Q).obj E,
        (Q).map (boundary cone ι c hc Z hZ F) ≫ g =
          OrdinaryHoCofiberKernel.nullHom (c F).pt E := by
  constructor
  · intro h g
    exact (third_exact Z hZ cone ι c hc F E hCone g).mp (h g)
  · intro h g
    exact (third_exact Z hZ cone ι c hc F E hCone g).mpr (h g)

example (n : ℕ) (F : Arrow C) [IsCofibrant F.left] [IsCofibrant F.right]
    (hι : ∀ X : C, IsCofibrant X → cofibrations C ((ι).app X))
    (hCone : ∀ X : C, IsCofibrant X → weakEquivalences C (toZero Z hZ ((cone).obj X)))
    (E : C) [IsFibrant E] :
    Set.range (restriction cone ι c hc (n + 1) F E) =
      {g | restriction cone ι c hc n F E g =
        OrdinaryHoCofiberKernel.nullHom (term cone ι c hc n F) E} := by
  ext g
  exact exact_at Z hZ cone ι c hc hι hCone n F E g

example (n : ℕ) {F G : Arrow C} (q : F ⟶ G) {E E' : C} (p : E ⟶ E')
    (g : homTerm cone ι c hc (n + 1) G E) :
    restriction cone ι c hc n F E'
        (sourceAction cone ι c hc (n + 1) q E'
          (targetAction cone ι c hc (n + 1) G p g)) =
      targetAction cone ι c hc n F p
        (sourceAction cone ι c hc n q E (restriction cone ι c hc n G E g)) := by
  have hs := congrFun (restriction_source cone ι c hc n q E')
    (targetAction cone ι c hc (n + 1) G p g)
  have ht := congrFun (restriction_target cone ι c hc n G p) g
  have hst := congrFun (sourceAction_target cone ι c hc n q p)
    (restriction cone ι c hc n G E g)
  exact hs.trans ((congrArg (sourceAction cone ι c hc n q E') ht).trans hst)

#print axioms HomotopicalAlgebra.OrdinaryHoChosenPuppeHomSequence.third_exact
#print axioms HomotopicalAlgebra.OrdinaryHoChosenPuppeHomSequence.exact_at
#print axioms HomotopicalAlgebra.OrdinaryHoChosenPuppeHomSequence.signed_shift_square

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeRotation
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeHomSequence

end HomotopicalAlgebra.OrdinaryHoChosenPuppeHomSequencePublicClients
