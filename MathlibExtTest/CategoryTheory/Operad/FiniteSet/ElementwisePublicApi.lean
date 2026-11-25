/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import MathlibExt.CategoryTheory.Operad.FiniteSet.Elementwise

/-!
# Focused O7E elementwise accessors public-contract packet

Pins the stable downstream-facing contracts for elementwise
set-operad accessors: the empty tensor and unit elements,
substitution data with total arity, full elementwise
substitution, source-map evaluations at outer/inner factors,
naturality in elementwise form, and the associativity routes
equation.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u

-- The unit element applies the unit morphism to the empty element.
example (O : SetOperad.{u}) :
    SetOperad.unitElement O =
      O.unit SetOperad.emptyTensorElement :=
  rfl

-- Substitution data packages outer and inner arities.
example (I : FintypeCat) (J : I → FintypeCat) :
    SetOperad.substitutionData I J =
      { index := I, obj := fun i => ⟨J i⟩ } :=
  rfl

-- Total arity is the substitution total object.
example (I : FintypeCat) (J : I → FintypeCat) :
    SetOperad.totalArity I J =
      substitutionTotalObj
        (SetOperad.substitutionData I J) :=
  rfl

-- Full substitution applies subst to the option-indexed family.
example (O : SetOperad.{u}) {I : FintypeCat}
    {J : I → FintypeCat}
    (outer : O.toCollection.eval I)
    (inner : (i : I) → O.toCollection.eval (J i)) :
    O.fullSubstitution outer inner =
      (O.subst.app (SetOperad.substitutionData I J))
        (fun o => match o with
          | none => outer
          | some i => inner i) :=
  rfl

-- Source maps evaluate at the outer factor.
example (O : SymmetricCollection (Type u))
    {X Y : SubstitutionData} (f : X ⟶ Y)
    (fam : (substitutionSource O).obj X) :
    ((substitutionSource O).map f fam) none =
      ((substitutionFactors O).map f).hom none
        (fam none) :=
  SetOperad.substitutionSource_map_apply_none O f fam

-- Source maps evaluate at inner factors.
example (O : SymmetricCollection (Type u))
    {X Y : SubstitutionData} (f : X ⟶ Y)
    (fam : (substitutionSource O).obj X) (i : X.index) :
    ((substitutionSource O).map f fam) (some (f.equiv i)) =
      ((substitutionFactors O).map f).hom (some i)
        (fam (some i)) :=
  SetOperad.substitutionSource_map_apply_some O f fam i

-- Elementwise naturality of substitution.
example (O : SetOperad.{u})
    {X Y : SubstitutionData} (f : X ⟶ Y)
    (fam : (substitutionSource O.toCollection).obj X) :
    O.subst.app Y
          ((substitutionSource O.toCollection).map f fam) =
      (substitutionTarget O.toCollection).map f
        (O.subst.app X fam) :=
  SetOperad.subst_naturality_apply O f fam

-- The two associativity routes agree elementwise.
example (O : SetOperad.{u}) (d : AssocData) :
    associativityRouteA O.toCollection O.subst d =
      associativityRouteB O.toCollection O.subst d :=
  SetOperad.associativity_routes O d

-- The empty tensor element eliminates the empty family.
example : SetOperad.emptyTensorElement =
    (fun e => e.elim :
      operadUnitSource (V := Type u)) :=
  rfl

-- Source maps evaluate through the factor maps.
example (O : SymmetricCollection (Type u))
    {X Y : SubstitutionData} (f : X ⟶ Y)
    (fam : (substitutionSource O).obj X)
    (i : Option X.index) :
    ((substitutionSource O).map f fam)
        (((substitutionFactors O).map f).equiv i) =
      ((substitutionFactors O).map f).hom i (fam i) :=
  SetOperad.substitutionSource_map_apply O f fam i
