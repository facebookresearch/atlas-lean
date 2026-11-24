/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendTransport
import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendIso
import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendMapped
import MathlibExtTest.CategoryTheory.Enriched.Limits.WeightedCoendTransportTests
import MathlibExtTest.CategoryTheory.Enriched.Limits.WeightedCoendMappedTests
import MathlibExtTest.CategoryTheory.Enriched.Monoidal.BasicTests
import MathlibExtTest.CategoryTheory.Enriched.Monoidal.FunctorTransportPublicApiTests
import MathlibExtTest.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorPrerequisitesTests
import MathlibExtTest.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorNestedPublicApiTests

/-!
# Weighted-coend and Day public client coimports

The new braided transport clients coexist with the original mapped-coend,
product, value-transport and nested Day public clients. The original graded
weight-isomorphism API remains available with its original hypotheses.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uA
open CategoryTheory MonoidalCategory Limits Opposite
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {W W' : EnrichedFunctorCat V Aᵒᵖ}
  (F : EnrichedFunctor V A V) (e : W ≅ W')
  [HasCoproduct (Enriched.weightedCoend.relations W.toEnrichedFunctor F)]
  [HasCoproduct (Enriched.weightedCoend.objects W.toEnrichedFunctor F)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W.toEnrichedFunctor F)
    (Enriched.weightedCoend.rightMap W.toEnrichedFunctor F)]
  [HasCoproduct (Enriched.weightedCoend.relations W'.toEnrichedFunctor F)]
  [HasCoproduct (Enriched.weightedCoend.objects W'.toEnrichedFunctor F)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W'.toEnrichedFunctor F)
    (Enriched.weightedCoend.rightMap W'.toEnrichedFunctor F)]

example (a : A) :
    Enriched.weightedCoend.ι W.toEnrichedFunctor F a ≫
        (Enriched.weightedCoend.weightIso F e).hom =
      (EnrichedFunctorCat.component e.hom (op a) ⊗ₘ 𝟙 (F.obj a)) ≫
        Enriched.weightedCoend.ι W'.toEnrichedFunctor F a := by
  fail_if_success haveI : SymmetricCategory V := inferInstance
  exact Enriched.weightedCoend.weightIso_gen_hom F e a
