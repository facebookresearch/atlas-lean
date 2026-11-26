/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Category
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Transport

/-!
# Homology of bracket-presented Chevalley–Eilenberg models

Let `R` be a commutative ring. A bracket-presented CE model has exterior-power chain terms and
its bracket differential with square zero. Taking homology of the associated chain complex
gives a functor in each nonnegative degree.

A model morphism induces the homology map of its chain map, and a model isomorphism induces a
homology isomorphism. The scalar-ring and model-carrier universes are independent.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

namespace Model

variable {R : Type u} [CommRing R]

/-- The homology module of a bracket-presented CE model.

For a model `X` and degree `n`, take degree-`n` homology of the chain complex defined by its
bracket data. -/
abbrev H (X : Model.{u, v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  X.data.toChainData.complex.homology n

/-- The fixed-degree homology functor on CE models.

Send each model to homology of its chain complex in degree `n` and each model morphism to the
induced homology map. -/
abbrev homologyFunctor (R : Type u) [CommRing R] (n : ℕ) :
    Model.{u, v} R ⥤ ModuleCat.{max u v} R :=
  complexFunctor R ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n

/-- The object formula for the CE model homology functor.

At a model `X`, the degree-`n` homology functor has value `X.H n`. -/
theorem homologyFunctor_obj (X : Model.{u, v} R) (n : ℕ) :
    (homologyFunctor R n).obj X = X.H n :=
  rfl

/-- The morphism formula for the CE model homology functor.

A model morphism maps to the degree-`n` homology map of its associated chain map. -/
theorem homologyFunctor_map
    {X Y : Model.{u, v} R} (f : X ⟶ Y) (n : ℕ) :
    (homologyFunctor R n).map f =
      HomologicalComplex.homologyMap ((complexFunctor R).map f) n :=
  rfl

/-- The homology isomorphism induced by a CE model isomorphism.

Applying the degree-`n` homology functor to a model isomorphism gives an isomorphism of the
corresponding homology modules. -/
def homologyIso {X Y : Model.{u, v} R} (e : X ≅ Y) (n : ℕ) :
    X.H n ≅ Y.H n :=
  (homologyFunctor R n).mapIso e

/-- The forward map of a CE model homology isomorphism.

The forward homology map is induced by the forward model chain map. -/
@[simp]
theorem homologyIso_hom {X Y : Model.{u, v} R}
    (e : X ≅ Y) (n : ℕ) :
    (homologyIso e n).hom =
      HomologicalComplex.homologyMap ((complexFunctor R).map e.hom) n :=
  rfl

/-- The inverse map of a CE model homology isomorphism.

The inverse homology map is induced by the inverse model chain map. -/
@[simp]
theorem homologyIso_inv {X Y : Model.{u, v} R}
    (e : X ≅ Y) (n : ℕ) :
    (homologyIso e n).inv =
      HomologicalComplex.homologyMap ((complexFunctor R).map e.inv) n :=
  rfl

end Model

end ChevalleyEilenberg
