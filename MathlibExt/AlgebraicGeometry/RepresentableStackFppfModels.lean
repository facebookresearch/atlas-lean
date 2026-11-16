/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.InfiniteDenominatorRoots
public import MathlibExt.AlgebraicGeometry.StackFibreModels
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Representable fppf charts with arbitrary fibred stack domains

A chart domain is an arbitrary native relative stack, with no Artin,
finite-type or diagonal assumption on that domain. Representability,
flatness and local finite presentation are tested on the whole native
two-fibre category over every scheme point of the target stack.

Arrows retain their native cartesian functor and invertible triangle.
The ordinary site uses the literal quotient by compatible native
invertible modifications. It does not discard the source triangle.

Source: Talpo--Vistoli arXiv:1410.1164v2, Section4.1 and Definition6.2.
Representable maps into an fppf stack satisfy source descent; that
ordinary source-integration assertion is separate from the site comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RepresentableStackFppfModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry _root_.AlgebraicGeometry.StackFibreModels
open InfiniteDenominatorRoots

variable {S : Scheme.{0}}

local instance modificationCategory (A B : Stack S) : Category (StackHom A B) :=
  Pseudofunctor.StrongTrans.homCategory (F := A.toPseudofunctor) (G := B.toPseudofunctor)

/-- Native whole two-fibre representability and the actual fppf test maps. -/
def HasFppfFibres {A B : Stack S} (f : StackHom A B) : Prop :=
  ∀ (T : Over S) (y : B.Fibre T), ∃ m : SchemeFibreModel f T y,
    Flat m.scheme.hom ∧ LocallyOfFinitePresentation m.scheme.hom

/-- Definition6.2 chart; the domain is allowed to be another infinite root stack. -/
structure Chart (R : Stack S) where
  domain : Stack S
  projection : StackHom domain R
  fppf : HasFppfFibres projection

/-- Native cartesian functor with the full invertible triangle over R. -/
structure RawHom {R : Stack S} (A B : Chart R) where
  map : StackHom A.domain B.domain
  triangle : Pseudofunctor.StrongTrans.vcomp map B.projection ≅ A.projection

/-- Exactly the triangle-compatible relative two-isomorphisms. -/
def Related {R : Stack S} {A B : Chart R} (f g : RawHom A B) : Prop :=
  ∃ e : f.map ≅ g.map, ∀ (T : Over S) (x : A.domain.Fibre T),
    (componentIso f.triangle T).hom.app x =
      (InfiniteDenominatorRoots.component B.projection T).map ((componentIso e T).hom.app x) ≫
        (componentIso g.triangle T).hom.app x

abbrev QuotientHom {R : Stack S} (A B : Chart R) := Quot (@Related S R A B)

/-- Raw category operations are fixed on their cartesian functors and
all triangle components; generic bicategorical assembly is deferred. -/
structure RawOperations (R : Stack S) where
  identity : ∀ A : Chart R, RawHom A A
  identity_map : ∀ A : Chart R,
    (identity A).map = Pseudofunctor.StrongTrans.id A.domain.toPseudofunctor
  identity_triangle : ∀ (A : Chart R) (T : Over S) (x : A.domain.Fibre T),
    HEq ((componentIso (identity A).triangle T).hom.app x)
      (𝟙 ((InfiniteDenominatorRoots.component A.projection T).obj x))
  compose : ∀ {A B C : Chart R}, RawHom A B → RawHom B C → RawHom A C
  compose_map : ∀ {A B C : Chart R} (f : RawHom A B) (g : RawHom B C),
    (compose f g).map = Pseudofunctor.StrongTrans.vcomp f.map g.map
  compose_triangle : ∀ {A B C : Chart R} (f : RawHom A B) (g : RawHom B C)
      (T : Over S) (x : A.domain.Fibre T),
    HEq ((componentIso (compose f g).triangle T).hom.app x)
      ((componentIso g.triangle T).hom.app ((InfiniteDenominatorRoots.component f.map T).obj x) ≫
        (componentIso f.triangle T).hom.app x)

end MathlibExt.AlgebraicGeometry.RepresentableStackFppfModels
