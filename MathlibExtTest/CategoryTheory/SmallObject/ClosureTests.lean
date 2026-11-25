/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.SmallObject.Closure

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

noncomputable section

universe w t vC vD uC uD

section IndependentUniverses

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) (P : MorphismProperty C) (Q : MorphismProperty D)
  (hPQ : P ≤ Q.inverseImage F)
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun (_ : T) => P.homFamily) f)
  [PreservesColimitsOfSize.{w, w} F]
  [PreservesColimitsOfShape T F]
  [PreservesWellOrderContinuousOfShape T F]

include P hPQ c

-- The mapped complex retains the actual endpoint, diagram and cocone.
example : RelativeCellComplex.{w} (fun (_ : T) => Q.homFamily) (F.map f) :=
  c.mapOfLE F P Q hPQ

example : (c.mapOfLE F P Q hPQ).F = c.F ⋙ F := rfl

example : (c.mapOfLE F P Q hPQ).incl =
    Functor.whiskerRight c.incl F ≫ (Functor.constComp _ _ _).hom := rfl

example : IsColimit
    (Cocone.mk (F.obj Y)
      (Functor.whiskerRight c.incl F ≫ (Functor.constComp _ _ _).hom)) :=
  (c.mapOfLE F P Q hPQ).isColimit

variable [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]

-- This actual endpoint client has only closure of the supplied shape T.
example [Q.IsStableUnderTransfiniteCompositionOfShape T] : Q (F.map f) :=
  c.map_mem_of_le F P Q hPQ

-- The interval transition client retains the actual given arrow phi.
example [Q.IsStableUnderTransfiniteComposition.{t}] {a b : T} (φ : a ⟶ b) :
    Q (F.map (c.F.map φ)) :=
  c.map_map_mem_of_le F P Q hPQ φ

end IndependentUniverses

section SmallChainLargeAmbient

variable {C : Type (uC + 1)} [Category.{vC + 1} C]
  {D : Type (uD + 1)} [Category.{vD + 1} D]
  (F : C ⥤ D) (P : MorphismProperty C) (Q : MorphismProperty D)
  (hPQ : P ≤ Q.inverseImage F)
  {T : Type} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w + 1} (fun (_ : T) => P.homFamily) f)
  [PreservesColimitsOfSize.{w + 1, w + 1} F]
  [PreservesColimitsOfShape T F]
  [PreservesWellOrderContinuousOfShape T F]
  [Q.IsStableUnderCoproducts.{w + 1}] [Q.IsStableUnderCobaseChange]

include P hPQ c

example [Q.IsStableUnderTransfiniteCompositionOfShape T] : Q (F.map f) :=
  c.map_mem_of_le F P Q hPQ

example [Q.IsStableUnderTransfiniteComposition.{0}] {a b : T} (φ : a ⟶ b) :
    Q (F.map (c.F.map φ)) :=
  c.map_map_mem_of_le F P Q hPQ φ

end SmallChainLargeAmbient

#print axioms HomotopicalAlgebra.RelativeCellComplex.map_mem_of_le
#print axioms HomotopicalAlgebra.RelativeCellComplex.map_map_mem_of_le
