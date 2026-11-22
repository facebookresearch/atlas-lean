/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.AmbientTensorHom
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# The full original ambient tensor-cotensor parametrized adjunction

The tensor coefficient variable is the original ambient category; both
module variables are the actual associative A-module category.  The literal
coordinate pre-map, original tensor-coordinate map and their whole mate
equation produce the complete parametrized adjunction.  The actual Leibniz
pushout/pullback adjunction follows from those same original maps.

No model, weak-preservation or derived-action conclusion is assumed here.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w w'

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.HomogeneousLocalization.AmbientTensorHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] (A : C) [MonObj A]

/-- All three original variables belong to the same actual ambient tensor-Hom adjunction. -/
def parametrizedAdjunction : leftBifunctor A ⊣₂ rightBifunctor A :=
  ParametrizedAdjunction.mk' (adjunction A) (by
    intro U V a M N f
    change (adjunction A U).homEquiv M N (Mod.AmbientTensor.map A a (𝟙 M) ≫ f) =
      (adjunction A V).homEquiv M N f ≫ preMap A a N
    rw [adjunction_homEquiv, adjunction_homEquiv]
    exact (coordinate_mate A a M N f).symm)

section Leibniz

variable [HasPushouts (Mod C A)]

/-- The full actual ambient/module pushout-product uses the original curried tensor functor. -/
def ambientPushoutProduct : Arrow C ⥤ Arrow (Mod C A) ⥤ Arrow (Mod C A) :=
  (leftBifunctor A).leibnizPushout

variable [HasPullbacks (Mod C A)]

/-- The whole ambient pushout-product/internal-Hom pullback adjunction is the original Leibniz adjunction. -/
def ambientLeibnizAdjunction (f : Arrow C) :
    (ambientPushoutProduct A).obj f ⊣ (rightBifunctor A).leibnizPullback.obj (op f) :=
  Functor.LeibnizAdjunction.adj (leftBifunctor A) (rightBifunctor A) (parametrizedAdjunction A) f

/-- Every original independent source colimit is preserved by the same whole ambient corner functor. -/
theorem ambientPushoutProduct_preservesColimits (f : Arrow C) :
    PreservesColimitsOfSize.{w', w} ((ambientPushoutProduct A).obj f) :=
  (ambientLeibnizAdjunction A f).leftAdjoint_preservesColimits

end Leibniz

end CategoryTheory.HomogeneousLocalization.AmbientTensorHom
