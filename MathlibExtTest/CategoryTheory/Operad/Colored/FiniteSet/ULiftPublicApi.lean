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

import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.ULift

/-!
# Focused O7E universe-lift public-contract packet

Pins the stable downstream-facing contracts for universe
lifts of set operads: collection/unit/substitution
projections, law preservation, the operad assembly with
operation equivalences, and the one-color lift with its
operation equivalence.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v

variable {Color : Type u}

-- Lifted relabeling projects to relabeling.
example (O : ColoredSetOperad.{u, 0} Color)
    {P Q : ColoredProfile Color} (f : P ⟶ Q)
    (x : (ColoredSetOperad.liftCollection.{u, v} O).obj
      P) :
    ((ColoredSetOperad.liftCollection.{u, v} O).map f
      x).down =
      O.toCollection.map f x.down :=
  ColoredSetOperad.liftCollection_map_down O f x

-- Lifted units project to units.
example (O : ColoredSetOperad.{u, 0} Color) (c : Color)
    (x : operadUnitSource (V := Type v)) :
    ((ColoredSetOperad.liftUnit.{u, v} O) c x).down =
      ColoredSetOperad.unitElement O c :=
  ColoredSetOperad.liftUnit_down O c x

-- Lifted substitution projects to substitution.
example (O : ColoredSetOperad.{u, 0} Color)
    (d : ColoredSubstitutionData Color)
    (ops : (ColoredOperadObj.substitutionSource
      (ColoredSetOperad.liftCollection.{u, v} O)).obj d) :
    ((ColoredSetOperad.liftSubstitution.{u, v} O).app d
      ops).down =
      O.subst.app d (fun o ↦ (ops o).down) :=
  ColoredSetOperad.liftSubstitution_down O d ops

-- The lifted operad projects to its collection.
example (O : ColoredSetOperad.{u, 0} Color) :
    (ColoredSetOperad.liftOperad.{u, v} O).toCollection =
      ColoredSetOperad.liftCollection.{u, v} O :=
  rfl

-- Projecting a lifted operation recovers it.
example (O : ColoredSetOperad.{u, 0} Color)
    (P : ColoredProfile Color)
    (x : (ColoredSetOperad.liftOperad.{u, v}
      O).toCollection.obj P) :
    ColoredSetOperad.liftOperationEquiv O P x = x.down :=
  ColoredSetOperad.liftOperationEquiv_apply O P x

-- Lifting wraps operations in `ULift`.
example (O : ColoredSetOperad.{u, 0} Color)
    (P : ColoredProfile Color)
    (x : O.toCollection.obj P) :
    (ColoredSetOperad.liftOperationEquiv O P).symm x =
      ⟨x⟩ :=
  ColoredSetOperad.liftOperationEquiv_symm_apply O P x

-- One-color lifted operations project down.
noncomputable example (O : SetOperad.{0})
    (I : FintypeCat)
    (x : (SetOperad.ulift.{v} O).toCollection.eval I) :
    SetOperad.uliftOperationEquiv O I x = x.down :=
  SetOperad.uliftOperationEquiv_apply O I x

-- One-color lifting wraps in `ULift`.
noncomputable example (O : SetOperad.{0})
    (I : FintypeCat) (x : O.toCollection.eval I) :
    (SetOperad.uliftOperationEquiv.{v} O I).symm x = ⟨x⟩ :=
  SetOperad.uliftOperationEquiv_symm_apply O I x
