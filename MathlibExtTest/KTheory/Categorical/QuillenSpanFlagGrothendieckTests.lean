/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.KTheory.Exact.Quillen.SpanFlagGrothendieck

/-!
# Flagged-span Grothendieck construction tests

These tests pin strict representative transport, the material components of
the transport functor, its Core-valued composition orientation, and the
equivalence/groupoid properties of the Grothendieck projection.  They make
no quotient-composition, all-degree grid, realization, additivity, or Q/S
claim.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory

noncomputable section

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanFlagGrothendieckTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {X Y : C} {S S' S'' : QuillenSpan X Y}

example (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData.transport (Iso.refl S) A = A :=
  QuillenSpanFlagData.transport_refl A

example (e : S ≅ S') (e' : S' ≅ S'')
    (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData.transport (e ≪≫ e') A =
      QuillenSpanFlagData.transport e'
        (QuillenSpanFlagData.transport e A) :=
  QuillenSpanFlagData.transport_trans e e' A

example (e : S ≅ S') {A B : QuillenSpanFlagData S} (f : A ⟶ B) :
    ((QuillenSpanFlagData.transportFunctor e).map f).kernelHom =
      f.kernelHom := by
  simp
  rfl

example (e : S ≅ S') {A B : QuillenSpanFlagData S} (f : A ⟶ B) :
    ((QuillenSpanFlagData.transportFunctor e).map f).pushoutHom =
      f.pushoutHom := by
  simp
  rfl

example (e : S ≅ S') {A B : QuillenSpanFlagData S} (f : A ⟶ B) :
    ((QuillenSpanFlagData.transportFunctor e).map f).quotientHom =
      f.quotientHom := by
  simp
  rfl

example :
    QuillenSpanFlagData.transportFunctor (Iso.refl S) =
      Functor.id (QuillenSpanFlagData S) :=
  QuillenSpanFlagData.transportFunctor_refl

example (e : S ≅ S') (e' : S' ≅ S'') :
    QuillenSpanFlagData.transportFunctor (e ≪≫ e') =
      QuillenSpanFlagData.transportFunctor e ⋙
        QuillenSpanFlagData.transportFunctor e' :=
  QuillenSpanFlagData.transportFunctor_trans e e'

example (T : Core (QuillenSpan X Y)) :
    (quillenSpanFlagFiberFunctor X Y).map (𝟙 T) =
      𝟙 ((quillenSpanFlagFiberFunctor X Y).obj T) :=
  (quillenSpanFlagFiberFunctor X Y).map_id T

example {T T' T'' : Core (QuillenSpan X Y)}
    (e : T ⟶ T') (e' : T' ⟶ T'') :
    (quillenSpanFlagFiberFunctor X Y).map (e ≫ e') =
      (quillenSpanFlagFiberFunctor X Y).map e ≫
        (quillenSpanFlagFiberFunctor X Y).map e' :=
  (quillenSpanFlagFiberFunctor X Y).map_comp e e'

example : (quillenSpanFlagProjection X Y).Full :=
  inferInstance

example : (quillenSpanFlagProjection X Y).Faithful :=
  inferInstance

example : (quillenSpanFlagProjection X Y).EssSurj :=
  inferInstance

example : (quillenSpanFlagProjection X Y).IsEquivalence :=
  inferInstance

example : QuillenSpanFlagTotal X Y ≌ Core (QuillenSpan X Y) :=
  quillenSpanFlagTotalEquivalenceCore X Y

example : IsGroupoid (QuillenSpanFlagTotal X Y) :=
  inferInstance

example (A B : QuillenSpanFlagTotal X Y) (f : A ⟶ B) : IsIso f :=
  inferInstance

example (T : Core (QuillenSpan X Y)) (A : QuillenSpanFlagData T.of) :
    (quillenSpanFlagProjection X Y).obj
        (⟨T, A⟩ : QuillenSpanFlagTotal X Y) = T :=
  rfl

example {A B : QuillenSpanFlagTotal X Y} (f : A ⟶ B) :
    (quillenSpanFlagProjection X Y).map f = f.base :=
  rfl

end MathlibExtTest.KTheory.Categorical.QuillenSpanFlagGrothendieckTests
