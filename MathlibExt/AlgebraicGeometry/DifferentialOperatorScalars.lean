/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DifferentialOperatorSheaves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# The actual coefficient action in the local differential-operator sheaf

Multiplication by a section acts on every subopen through actual restriction.
It has order zero, hence belongs to the finite-order operator presheaf.
Native sheafification supplies O→D, and native restriction of scalars
supplies the underlying O-module functor. No coefficient embedding or
forgetful functor is selected as an unconstrained parameter.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DifferentialOperatorScalars

open CategoryTheory Opposite TopologicalSpace DifferentialOperatorSheaves
open MathlibExt.RingTheory.GeometricDifferentialOperators

variable (k : Type) [CommRing k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)

theorem restriction_comp {U V W : Opens M} (h : V ≤ U) (j : W ≤ V)
    (a : O.obj (op U)) :
    (O.map (homOfLE j).op).hom ((O.map (homOfLE h).op).hom a) =
      (O.map (homOfLE (j.trans h)).op).hom a := by
  change (((O.map (homOfLE h).op) ≫ (O.map (homOfLE j).op)).hom) a = _
  rw [← O.map_comp]
  rfl

def multiplicationNatural (U : Opens M) (a : O.obj (op U)) : naturalOperators k M O U :=
  ⟨fun V ↦ Algebra.lsmul k k (O.obj (op V.val))
    ((O.map (homOfLE V.property).op).hom a), by
    intro V W h
    ext x
    change (O.map (homOfLE h).op).hom
      (((O.map (homOfLE V.property).op).hom a) * x) =
      ((O.map (homOfLE W.property).op).hom a) * (O.map (homOfLE h).op).hom x
    rw [map_mul, restriction_comp]
    ⟩

def scalarNatural (U : Opens M) : O.obj (op U) →+* naturalOperators k M O U where
  toFun := multiplicationNatural k M O U
  map_zero' := by ext V x; simp [multiplicationNatural]
  map_one' := by ext V x; simp [multiplicationNatural]
  map_add' a b := by ext V x; simp [multiplicationNatural]
  map_mul' a b := by ext V x; simp [multiplicationNatural]

def scalarFinite (U : Opens M) : O.obj (op U) →+* finiteOperatorRing k M O U :=
  (scalarNatural k M O U).codRestrict _ (fun a ↦
    Subring.subset_closure ⟨0, fun V ↦
      multiplication_orderZero k (O.obj (op V.val))
        ((O.map (homOfLE V.property).op).hom a)⟩)

def coefficientPresheaf : (Opens M)ᵒᵖ ⥤ RingCat.{0} :=
  O ⋙ forget₂ (CommAlgCat.{0} k) CommRingCat.{0} ⋙
    forget₂ CommRingCat.{0} RingCat.{0}

def scalarPresheafMap : coefficientPresheaf k M O ⟶ operatorPresheaf k M O where
  app U := RingCat.ofHom (scalarFinite k M O U.unop)
  naturality := by
    intro U V f
    ext a
    apply Subtype.ext
    apply Subtype.ext
    funext W
    apply LinearMap.ext
    intro x
    change ((O.map (homOfLE W.property).op).hom ((O.map f).hom a)) * x =
      ((O.map (homOfLE (W.property.trans f.unop.le)).op).hom a) * x
    congr 1
    exact restriction_comp k M O f.unop.le W.property a

def coefficientSheaf [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}] :
    Sheaf (Opens.grothendieckTopology M) RingCat.{0} :=
  (presheafToSheaf (Opens.grothendieckTopology M) RingCat.{0}).obj
    (coefficientPresheaf k M O)

def scalarSheafMap [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}] :
    coefficientSheaf k M O ⟶ differentialRing k M O :=
  (presheafToSheaf (Opens.grothendieckTopology M) RingCat.{0}).map
    (scalarPresheafMap k M O)

def underlyingO [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}] :
    DModule k M O ⥤ SheafOfModules.{0} (coefficientSheaf k M O) :=
  SheafOfModules.restrictScalars (scalarSheafMap k M O)

end MathlibExt.AlgebraicGeometry.DifferentialOperatorScalars

