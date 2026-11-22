/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- True global local powers and original all-arrow product weakness.
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.RepresentableProductsViaFreeCells
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CartesianTensorHomIso
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanCartesian
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen

/-!
# Local exponentials and products from representable tests

For a working-small localizing family on a working-small, locally small site, suppose that the
product of every localizing arrow with every representable presheaf is a local weak
equivalence. Exponentials into local fibrant objects are then local fibrant, and taking either
product with an arbitrary presheaf preserves every local weak-equivalence arrow.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory MonoidalClosed HomotopicalAlgebra Opposite
open scoped SimplicialPresheaf.InjectiveKan SSet.modelCategoryQuillen MonoidalCategory
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan
variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]
attribute [local instance] originalLocalEquivalences_isStableUnderRetracts

/-- Actual global baseline fibrancy and original S-locality of the TRUE exponential. -/
theorem originalRepresentableCriterion_powerLocalFibrant
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ a d, originalLocalEquivalences S ((S a).hom ▷ discreteYoneda.obj d))
    (A Z : SimplicialPresheaf.{u} D) (hZ : isOriginalLocalFibrant S Z) :
    isOriginalLocalFibrant S (exponential A Z) := by
  have hBase : IsFibrant (exponential A Z) := by
    let _ : IsCofibrant A := (data D).all_cofibrant A
    let _ : IsClosedSymmetricMonoidalModelCategory (SimplicialPresheaf.{u} D) :=
      cartesian_isClosedSymmetricMonoidalModelCategory
    let _ : Adjunction.IsQuillenAdjunction (underHomAdjunction A) :=
      ihomAdjunction_isQuillenAdjunction_of_isCofibrant A
    let _ : Adjunction.IsQuillenAdjunction (exponentialAdjunction A) := by
      change Adjunction.IsQuillenAdjunction
        ((underHomAdjunction A).ofNatIsoRight (underExponentialIso A))
      infer_instance
    exact (Adjunction.IsQuillenAdjunction.preservesFibrantObjects
      (adj := exponentialAdjunction A)) hZ.1
  refine ⟨hBase, ?_⟩
  apply (isRawLocal_exponential_iff S A Z).mpr
  intro a
  exact (originalRepresentableCriterion_allProductWeak S hCriterion a A).2.2 Z hZ

/-- Every original local weak map is preserved by either fixed product, without Mono/Fib
hypotheses. -/
theorem originalRepresentableCriterion_allArrowProductWeak
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (hCriterion : ∀ a d, originalLocalEquivalences S ((S a).hom ▷ discreteYoneda.obj d))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (hf : originalLocalEquivalences S f) (A : SimplicialPresheaf.{u} D) :
    originalLocalEquivalences S (A ◁ f) ∧ originalLocalEquivalences S (f ▷ A) := by
  have hr : originalLocalEquivalences S (f ▷ A) := by
    intro Z hZ
    exact (cartesianTensorHom_weak_iff A f Z).mp
      (hf (exponential A Z) (originalRepresentableCriterion_powerLocalFibrant S hCriterion A Z hZ))
  let e : Arrow.mk (f ▷ A) ≅ Arrow.mk (A ◁ f) :=
    Arrow.isoMk (β_ X A) (β_ Y A) (by ext d n x; rfl)
  exact ⟨((originalLocalEquivalences S).arrow_mk_iso_iff e).mp hr, hr⟩

end SimplicialPresheaf.InjectiveKan
