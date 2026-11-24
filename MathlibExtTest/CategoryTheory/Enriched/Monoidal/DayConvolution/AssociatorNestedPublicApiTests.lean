/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorNested

/-!
# Original nested Day presentation clients

Both orientations use five independent plain enriched index categories. The
chosen inner, outer and simultaneous coends are the original source families;
the two public generator formulas retain the same selected quotient values.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uC1 uC2 uK uE uM
open CategoryTheory MonoidalCategory Limits Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorNestedPublicClients

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C1 : Type uC1} [EnrichedCategory V C1]
  {C2 : Type uC2} [EnrichedCategory V C2]
  {K : Type uK} [EnrichedCategory V K]
  {E : Type uE} [EnrichedCategory V E]
  {M : Type uM} [EnrichedCategory V M]

section Left

variable (T : EnrichedFunctor V (C1 × C2) K)
  (U : EnrichedFunctor V (K × E) M)
  (F1 : EnrichedFunctor V C1 V) (F2 : EnrichedFunctor V C2 V)
  (H : EnrichedFunctor V E V) (m : M)

variable
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.objects T U F1 F2 H m p)]
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.innerRelations T U F1 F2 H m p)]
  [∀ p : K × E, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap T U F1 F2 H m p)
    (AssociatorFaces.Left.innerRightMap T U F1 F2 H m p)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F1 F2 k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F1 F2 k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 k)
    (EnrichedDayKernel.rightMap T F1 F2 k)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Left.relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Left.relationRelations T U F1 F2 H m pq)]
  [∀ pq, HasCoequalizer (AssociatorPresentation.Left.relationLeftMap T U F1 F2 H m pq)
    (AssociatorPresentation.Left.relationRightMap T U F1 F2 H m pq)]

variable [HasCoproduct (AssociatorPresentation.Left.innerObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorPresentation.Left.outerRelations T U F1 F2 H m)]
  [HasCoproduct (AssociatorNested.Left.actualObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorNested.Left.actualRelations T U F1 F2 H m)]

variable [HasCoequalizer (AssociatorPresentation.Left.outerLeftMap T U F1 F2 H m)
    (AssociatorPresentation.Left.outerRightMap T U F1 F2 H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U (Output.functor T F1 F2) H m)
    (EnrichedDayKernel.rightMap U (Output.functor T F1 F2) H m)]

variable [HasCoproduct (AssociatorPresentation.Left.simultaneousObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousRelations T U F1 F2 H m)]
  [HasCoequalizer (AssociatorPresentation.Left.simultaneousLeftMap T U F1 F2 H m)
    (AssociatorPresentation.Left.simultaneousRightMap T U F1 F2 H m)]

example (p : K × E) (i : C1 × C2) :
    AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i ≫
        (AssociatorNested.Left.simultaneousIso T U F1 F2 H m).hom =
      AssociatorPresentation.Left.simultaneousProjection T U F1 F2 H m p i :=
  AssociatorNested.Left.nestedGenerator_simultaneousIso_hom T U F1 F2 H m p i

example (p : K × E) (i : C1 × C2) :
    AssociatorPresentation.Left.simultaneousProjection T U F1 F2 H m p i ≫
        (AssociatorNested.Left.simultaneousIso T U F1 F2 H m).inv =
      AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i :=
  AssociatorNested.Left.simultaneousProjection_simultaneousIso_inv T U F1 F2 H m p i

end Left

section Right

variable (T : EnrichedFunctor V (C1 × C2) K)
  (U : EnrichedFunctor V (E × K) M)
  (F1 : EnrichedFunctor V C1 V) (F2 : EnrichedFunctor V C2 V)
  (H : EnrichedFunctor V E V) (m : M)

variable
  [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.objects T U F1 F2 H m p)]
  [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.innerRelations T U F1 F2 H m p)]
  [∀ p : E × K, HasCoequalizer
    (AssociatorFaces.Right.innerLeftMap T U F1 F2 H m p)
    (AssociatorFaces.Right.innerRightMap T U F1 F2 H m p)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F1 F2 k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F1 F2 k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 k)
    (EnrichedDayKernel.rightMap T F1 F2 k)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Right.relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Right.relationRelations T U F1 F2 H m pq)]
  [∀ pq, HasCoequalizer (AssociatorPresentation.Right.relationLeftMap T U F1 F2 H m pq)
    (AssociatorPresentation.Right.relationRightMap T U F1 F2 H m pq)]

variable [HasCoproduct (AssociatorPresentation.Right.innerObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorPresentation.Right.outerRelations T U F1 F2 H m)]
  [HasCoproduct (AssociatorNested.Right.actualObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorNested.Right.actualRelations T U F1 F2 H m)]

variable [HasCoequalizer (AssociatorPresentation.Right.outerLeftMap T U F1 F2 H m)
    (AssociatorPresentation.Right.outerRightMap T U F1 F2 H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U H (Output.functor T F1 F2) m)
    (EnrichedDayKernel.rightMap U H (Output.functor T F1 F2) m)]

variable [HasCoproduct (AssociatorPresentation.Right.simultaneousObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorPresentation.Right.simultaneousRelations T U F1 F2 H m)]
  [HasCoequalizer (AssociatorPresentation.Right.simultaneousLeftMap T U F1 F2 H m)
    (AssociatorPresentation.Right.simultaneousRightMap T U F1 F2 H m)]

example (p : E × K) (i : C1 × C2) :
    AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i ≫
        (AssociatorNested.Right.simultaneousIso T U F1 F2 H m).hom =
      AssociatorPresentation.Right.simultaneousProjection T U F1 F2 H m p i :=
  AssociatorNested.Right.nestedGenerator_simultaneousIso_hom T U F1 F2 H m p i

example (p : E × K) (i : C1 × C2) :
    AssociatorPresentation.Right.simultaneousProjection T U F1 F2 H m p i ≫
        (AssociatorNested.Right.simultaneousIso T U F1 F2 H m).inv =
      AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i :=
  AssociatorNested.Right.simultaneousProjection_simultaneousIso_inv T U F1 F2 H m p i

end Right

end CategoryTheory.EnrichedDayKernel.AssociatorNestedPublicClients
