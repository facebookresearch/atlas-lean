/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal

/-!
# Focused O7E small-core monoidal public-contract packet

Pins the stable downstream-facing contracts for the small
finite-bijection groupoid: the block-sum object length
computation, the equivalence functor object/map projections, the
block-sum hom equiv computation, the braiding equiv computation,
and restriction of symmetric collections with object/map laws.
-/

open CategoryTheory
open CategoryTheory.Operad
open scoped MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C]

-- Block sums add lengths.
example (X Y : SmallFinBijGroupoid) :
    (SmallFinBijGroupoid.blockSumObj X Y).of.len =
      X.of.len + Y.of.len :=
  SmallFinBijGroupoid.blockSumObj_len X Y

-- The equivalence functor acts on objects by inclusion.
example (X : SmallFinBijGroupoid) :
    (smallFinBijEquivalence.functor.obj X).of =
      FintypeCat.Skeleton.incl.obj X.of :=
  smallFinBijEquivalence_functor_obj X

-- The equivalence functor acts on maps by inclusion.
example {X Y : SmallFinBijGroupoid} (f : X ⟶ Y) :
    (smallFinBijEquivalence.functor.map f).iso =
      FintypeCat.Skeleton.incl.mapIso f.iso :=
  smallFinBijEquivalence_functor_map f

-- The braiding exposes fin-add-flip through ulift.
example (X Y : SmallFinBijGroupoid) :
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map (β_ X Y).hom) =
      Equiv.ulift.trans (finAddFlip.trans Equiv.ulift.symm) :=
  SmallFinBijGroupoid.braiding_equivOfHom X Y

-- Restriction acts on objects by precomposition.
example (X : SymmetricCollection C)
    (A : SmallFinBijGroupoid) :
    X.restrictSmall.obj A =
      X.obj (smallFinBijEquivalence.functor.obj A) :=
  X.restrictSmall_obj A

-- Restriction acts on maps by precomposition.
example (X : SymmetricCollection C)
    {A B : SmallFinBijGroupoid} (f : A ⟶ B) :
    X.restrictSmall.map f =
      X.map (smallFinBijEquivalence.functor.map f) :=
  X.restrictSmall_map f
