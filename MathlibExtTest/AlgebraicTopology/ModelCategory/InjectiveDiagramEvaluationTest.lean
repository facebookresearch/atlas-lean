/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.InjectiveDiagramEvaluation

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w uK vK uM vM

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable (K : Type uK) [Category.{vK} K] [LocallySmall.{w} K]
  (M : Type uM) [Category.{vM} M] [ModelCategory M] [HasCoproducts.{w} M]

private theorem injectiveEvaluationClient1 : ((trivialCofibrations M).functorCategory K).rlp ≤
    (fibrations M).functorCategory K :=
  (injectiveDiagram_rightClasses_le_pointwise K M).1

private theorem injectiveEvaluationClient2 : ((cofibrations M).functorCategory K).rlp ≤
    (trivialFibrations M).functorCategory K :=
  (injectiveDiagram_rightClasses_le_pointwise K M).2

private theorem injectiveEvaluationClient3 : ((cofibrations M).functorCategory K).rlp ≤
    (weakEquivalences M).functorCategory K :=
  injectiveDiagram_cofibrations_rlp_le_weak K M
