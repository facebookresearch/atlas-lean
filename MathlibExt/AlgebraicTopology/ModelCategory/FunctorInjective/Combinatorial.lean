/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalInjectiveGenerationAndFactors

/-!
# Combinatoriality of the constructed ordinary injective model

The common regular rank, original generating families and source eligibility
are constructed by `originalInjectiveGenerationAndFactors`. At that same rank
the original functor category is locally presentable. These actual outputs
witness combinatoriality of the exact `originalSmithModelCategory`.

This is the combinatoriality conclusion of Lurie's *Higher Topos Theory*,
Proposition A.2.8.2, in the author version of April 9, 2017, printed page 830
(PDF page 848). No functor model or chosen target generation is a premise.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

namespace HomotopicalAlgebra.FunctorInjective

open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)

/-- The actual common-rank generators and local-presentability witness make
the constructed model on the unchanged original functor category combinatorial. -/
theorem originalInjectiveModel_isCombinatorial :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
    IsCombinatorialModelCategory.{w} (D ⥤ C) := by
  let : ModelCategory (D ⥤ C) := originalSmithModelCategory d kappaLP s
  let g := originalInjectiveGenerationAndFactors d kappaLP s
  let : Fact g.cardinal.IsRegular := g.regular
  let : OrderBot g.cardinal.ord.ToType := g.bottom
  exact
    { exists_cardinal :=
        ⟨g.cardinal, g.regular, g.bottom, g.locallyPresentable, ⟨g.generationData⟩⟩ }

end HomotopicalAlgebra.FunctorInjective
