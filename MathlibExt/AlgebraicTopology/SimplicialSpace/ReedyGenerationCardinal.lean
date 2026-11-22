/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGeneratingFamilies
import MathlibExt.AlgebraicTopology.SimplicialSpace.Presentable
import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial

/-!
# A common cardinal for the literal Reedy small-object arguments

The original boundary and horn families share one regular cardinal with local
presentability and both actual native small-object eligibility certificates.
The retained functorial factorizations use their literal LLP/RLP classes.
No model, cardinal or eligibility witness is supplied by the caller.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra CategoryTheory.MorphismProperty
namespace SimplicialSpace.ReedyGeneratingFamilies

/-- A same-u regular cardinal and the exact two native SOA factorizations. -/
theorem exists_generation_cardinal :
    ∃ (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular)
      (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      IsCardinalLocallyPresentable SimplicialSpace.{u} κ ∧
        ∃ (hI : I.{u}.IsCardinalForSmallObjectArgument κ)
          (hJ : J.{u}.IsCardinalForSmallObjectArgument κ),
          letI : I.{u}.IsCardinalForSmallObjectArgument κ := hI
          letI : J.{u}.IsCardinalForSmallObjectArgument κ := hJ
          ∃ (dI : FunctorialFactorizationData I.{u}.rlp.llp I.{u}.rlp)
            (dJ : FunctorialFactorizationData J.{u}.rlp.llp J.{u}.rlp),
            dI = SmallObject.functorialFactorizationData I.{u} κ ∧
            dJ = SmallObject.functorialFactorizationData J.{u} κ := by
  let _ : IsLocallyPresentable.{u} SimplicialSpace.{u} :=
    SimplicialSpace.isLocallyPresentable
  let _ : I.{u}.IsSmall.{u} := isSmall_I
  let _ : J.{u}.IsSmall.{u} := isSmall_J
  let _ : I.{u}.HasSmallObjectArgument.{u} := hasSmallObjectArgument_of_isSmall I
  let _ : J.{u}.HasSmallObjectArgument.{u} := hasSmallObjectArgument_of_isSmall J
  obtain ⟨κ, hκ, hbot, hC, hI, hJ⟩ := exists_common_generation_cardinal I.{u} J.{u}
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  refine ⟨κ, hκ, hbot, hC, hI, hJ, ?_⟩
  let _ : I.{u}.IsCardinalForSmallObjectArgument κ := hI
  let _ : J.{u}.IsCardinalForSmallObjectArgument κ := hJ
  exact ⟨SmallObject.functorialFactorizationData I.{u} κ,
    SmallObject.functorialFactorizationData J.{u} κ, rfl, rfl⟩

end SimplicialSpace.ReedyGeneratingFamilies
