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

import MathlibExt.KTheory.Exact.Quillen.SpanFlagGroupoid

/-!
# Fixed-span Quillen flag groupoid tests

These clients exercise the material universal-property comparison, the
derived final-square law, unique flag morphisms, material projection
isomorphisms, and categorical contractibility of a fixed-span fiber.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory

noncomputable section

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanFlagGroupoidTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {X Y : C} {S : QuillenSpan X Y}

example (A B : QuillenSpanFlagData S) : A ⟶ B :=
  QuillenSpanFlagHom.canonical A B

example (A B : QuillenSpanFlagData S) :
    (QuillenSpanFlagHom.canonical A B).kernelHom ≫ B.kernelι =
      A.kernelι :=
  (QuillenSpanFlagHom.canonical A B).kernelHom_kernelι

example (A B : QuillenSpanFlagData S) :
    A.sourceToPushout ≫
        (QuillenSpanFlagHom.canonical A B).pushoutHom =
      B.sourceToPushout :=
  (QuillenSpanFlagHom.canonical A B).sourceToPushout_naturality

example (A B : QuillenSpanFlagData S) :
    A.targetToPushout ≫
        (QuillenSpanFlagHom.canonical A B).pushoutHom =
      B.targetToPushout :=
  (QuillenSpanFlagHom.canonical A B).targetToPushout_naturality

example (A B : QuillenSpanFlagData S) :
    A.quotientπ ≫ (QuillenSpanFlagHom.canonical A B).quotientHom =
      B.quotientπ :=
  (QuillenSpanFlagHom.canonical A B).quotientπ_quotientHom

example (A B : QuillenSpanFlagData S) (f : A ⟶ B) :
    A.pushoutToQuotient ≫ f.quotientHom =
      f.pushoutHom ≫ B.pushoutToQuotient :=
  f.pushoutToQuotient_naturality

example (A B : QuillenSpanFlagData S) : Unique (A ⟶ B) :=
  inferInstance

example (A B : QuillenSpanFlagData S) (f : A ⟶ B) : IsIso f :=
  inferInstance

example (A B : QuillenSpanFlagData S) (f : A ⟶ B) :
    IsIso ((quillenSpanFlagKernelFunctor S).map f) :=
  inferInstance

example (A B : QuillenSpanFlagData S) (f : A ⟶ B) :
    IsIso ((quillenSpanFlagPushoutFunctor S).map f) :=
  inferInstance

example (A B : QuillenSpanFlagData S) (f : A ⟶ B) :
    IsIso ((quillenSpanFlagQuotientFunctor S).map f) :=
  inferInstance

example (S : QuillenSpan X Y) :
    QuillenSpanFlagData S ≌ Discrete PUnit.{1} :=
  quillenSpanFlagFiberEquivalencePUnit S

example (S : QuillenSpan X Y) : IsConnected (QuillenSpanFlagData S) :=
  inferInstance

end MathlibExtTest.KTheory.Categorical.QuillenSpanFlagGroupoidTests
