/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Basic

/-!
# The category of bracket-presented exterior chain models

Over a commutative ring R, an object consists of an R-Lie algebra L
and square-zero maps d_n:Λ_R^{n+1}L→Λ_R^nL presented by the
canonical bracket formula. A morphism is an R-Lie homomorphism f
whose exterior maps commute with the differentials.

Naturality of the bracket formula makes every Lie homomorphism between
these models compatible. Identity and composition are those of Lie
homomorphisms. Sending a model to its exterior chain complex defines
a functor to ChainComplex(ModuleCat R,ℕ), in carrier height max{u,v}.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

/-- For a commutative ring R:Type u, a CE model consists of a Lie algebra
carrier L:Type v, its R-Lie structure, and square-zero exterior
differential data satisfying the canonical bracket prescription. -/
structure Model (R : Type u) [CommRing R] where
  /-- For a CE model over a commutative ring R, the carrier is a type L
with a Lie ring structure and an R-Lie algebra structure.
Its carrier universe v is independent of the scalar universe u. -/
  carrier : Type v
  [lieRing : LieRing carrier]
  [lieAlgebra : LieAlgebra R carrier]
  /-- For a CE model over a commutative ring R with carrier L, the chain
data are R-linear d_n:Λ_R^{n+1}L→Λ_R^nL, square zero and
satisfying d_n(x_0∧⋯∧x_n)=β_n(x) for the canonical bracket prescription. -/
  data : PresentedData R carrier (bracketBoundary R carrier)

attribute [instance] Model.lieRing Model.lieAlgebra

namespace Model

variable {R : Type u} [CommRing R]

/-- Let R be commutative and X,Y bracket-presented CE models.
A model morphism consists of an R-Lie homomorphism f:X.carrier→Y.carrier
with d_Y Λ^{n+1}f=Λ^n f d_X in every degree. -/
structure Hom (X Y : Model R) where
  /-- For models X,Y over a commutative ring R, the underlying map of
a model morphism is an R-Lie homomorphism f:X.carrier→Y.carrier.
Its exterior powers commute with the two model differentials. -/
  lieHom : X.carrier →ₗ⁅R⁆ Y.carrier
  comm : ChainData.Hom (R := R) (L := X.carrier)
    X.data.toChainData Y.data.toChainData lieHom

/-- Let R be commutative and X,Y models presented by the canonical
bracket formula. Every R-Lie homomorphism between their carriers
induces a model morphism, by naturality of that formula. -/
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

/-- For a CE model X over a commutative ring R, the identity model
morphism has identity Lie map and identity exterior components. -/
def Hom.id (X : Model R) : Hom X X where
  lieHom := LieHom.id
  comm := ChainData.Hom.id R X.carrier X.data.toChainData

/-- For composable model morphisms f:X→Y and g:Y→Z over a
commutative ring R, their composite has Lie map g∘f and exterior
components Λ^n(g∘f). -/
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

/-- For a commutative ring R:Type u, the functor from CE models
with carrier universe v to nonnegative R-module chain complexes
sends X to its exterior differential complex and a model morphism
f to Λ_R^n f in each degree, in height max{u,v}. -/
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
