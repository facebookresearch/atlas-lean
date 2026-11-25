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

The homology functor on chain complexes restricts to bracket-presented Chevalley–Eilenberg
models. Model morphisms induce homology maps, and model isomorphisms induce homology
isomorphisms in every degree.
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

/-- Degree-`n` homology of a lawful CE model. -/
abbrev H (X : Model.{u, v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  X.data.toChainData.complex.homology n

/-- Fixed-degree CE homology as a functor on lawful models. -/
abbrev homologyFunctor (R : Type u) [CommRing R] (n : ℕ) :
    Model.{u, v} R ⥤ ModuleCat.{max u v} R :=
  complexFunctor R ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n

theorem homologyFunctor_obj (X : Model.{u, v} R) (n : ℕ) :
    (homologyFunctor R n).obj X = X.H n :=
  rfl

theorem homologyFunctor_map
    {X Y : Model.{u, v} R} (f : X ⟶ Y) (n : ℕ) :
    (homologyFunctor R n).map f =
      HomologicalComplex.homologyMap ((complexFunctor R).map f) n :=
  rfl

/-- A model isomorphism induces an isomorphism on fixed-degree CE homology. -/
def homologyIso {X Y : Model.{u, v} R} (e : X ≅ Y) (n : ℕ) :
    X.H n ≅ Y.H n :=
  (homologyFunctor R n).mapIso e

@[simp]
theorem homologyIso_hom {X Y : Model.{u, v} R}
    (e : X ≅ Y) (n : ℕ) :
    (homologyIso e n).hom =
      HomologicalComplex.homologyMap ((complexFunctor R).map e.hom) n :=
  rfl

@[simp]
theorem homologyIso_inv {X Y : Model.{u, v} R}
    (e : X ≅ Y) (n : ℕ) :
    (homologyIso e n).inv =
      HomologicalComplex.homologyMap ((complexFunctor R).map e.inv) n :=
  rfl

end Model

end ChevalleyEilenberg
