/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Basic

/-!
# The category of Chevalley–Eilenberg chain models

An object is a Lie algebra together with a square-zero exterior-power
differential presented by the canonical bracket formula. A morphism is a Lie
algebra homomorphism compatible with the two differentials. Each model has an
underlying nonnegative chain complex.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

/-- A Lie algebra equipped with the canonical bracket-presented CE chain
data. -/
structure Model (R : Type u) [CommRing R] where
  /-- The underlying Lie algebra carrier. -/
  carrier : Type v
  [lieRing : LieRing carrier]
  [lieAlgebra : LieAlgebra R carrier]
  /-- The bracket-presented chain data on the carrier. -/
  data : PresentedData R carrier (bracketBoundary R carrier)

attribute [instance] Model.lieRing Model.lieAlgebra

namespace Model

variable {R : Type u} [CommRing R]

/-- A morphism of CE models is a differential-compatible Lie algebra map. -/
structure Hom (X Y : Model R) where
  /-- The underlying Lie algebra homomorphism. -/
  lieHom : X.carrier →ₗ⁅R⁆ Y.carrier
  comm : ChainData.Hom (R := R) (L := X.carrier)
    X.data.toChainData Y.data.toChainData lieHom

/-- Every Lie algebra map between canonical CE models induces a model
morphism. -/
def Hom.ofLieHom (X Y : Model R) (f : X.carrier →ₗ⁅R⁆ Y.carrier) : Hom X Y where
  lieHom := f
  comm := ChainData.homOfBoundaryNatural
    (R := R) (L := X.carrier) X.data Y.data f
      (ChainData.bracketBoundary_natural R X.carrier f)

@[ext]
theorem Hom.ext {X Y : Model R} (f g : Hom X Y)
    (h : f.lieHom = g.lieHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphism of a CE model. -/
def Hom.id (X : Model R) : Hom X X where
  lieHom := LieHom.id
  comm := ChainData.Hom.id R X.carrier X.data.toChainData

/-- Composition of CE-model morphisms. -/
def Hom.comp {X Y Z : Model R} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  lieHom := g.lieHom.comp f.lieHom
  comm := f.comm.comp (R := R) (L := X.carrier) g.comm

instance : Category (Model R) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext _ _ (by simp [Hom.id, Hom.comp])
  comp_id f := Hom.ext _ _ (by simp [Hom.id, Hom.comp])
  assoc f g h := Hom.ext _ _ (by rfl)

/-- The underlying chain complex of a CE model. -/
abbrev complexFunctor (R : Type u) [CommRing R] :
    Model.{u, v} R ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ where
  obj := fun X => X.data.toChainData.complex
  map := fun {X _Y} f =>
    ChainData.map (R := R) (L := X.carrier) f.lieHom f.comm
  map_id := fun X => ChainData.map_id R X.carrier X.data.toChainData
  map_comp := fun {X _Y _Z} f g =>
    (ChainData.map_comp R X.carrier f.comm g.comm).symm

@[simp]
theorem complexFunctor_obj (X : Model R) :
    (complexFunctor R).obj X = X.data.toChainData.complex :=
  rfl

@[simp]
theorem complexFunctor_map_f {X Y : Model R} (f : X ⟶ Y) (n : ℕ) :
    ((complexFunctor R).map f).f n =
      chainObjectMap R X.carrier f.lieHom n :=
  rfl

end Model

end ChevalleyEilenberg
