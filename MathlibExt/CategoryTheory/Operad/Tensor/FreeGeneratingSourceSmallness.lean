/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.FreeGeneratingSourcePresentability
import MathlibExt.CategoryTheory.Operad.Tensor.FreeAlgebra
import MathlibExt.CategoryTheory.Presentable.FunctorCategory
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Original tensor-operadic free generating source smallness

The original tensor free algebra adjunction and creation of filtered colimits
give accessibility of its actual forgetful functor at every regular source
rank. Presentability of the original colored generator endpoints therefore
gives presentability and relative-cell smallness of their actual free images.
For a locally presentable source coefficient category, a common rank is
constructed for both complete original families without changing their maps.
-/

noncomputable section
set_option autoImplicit false

universe u v w us uJ vJ

namespace CategoryTheory.Operad.Tensor

open Limits Opposite MorphismProperty SmallObject FreeGeneratingSource

variable (S : SourceContext.{u, v, w, us})
/-- Use the source's finite tensor structure for its algebra operations. -/
local instance sourceFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, w, us} S.C := S.finiteTensorPreservation
local instance (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C := S.profileColimits d

/-- The actual tensor algebra forgetful functor preserves the source-sized
filtered colimits by A1's created original carrier cocones. -/
theorem SourceContext.operadicForgetAccessible (O : ColoredOperadObj S.W S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] : (Algebra.forget O).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    let : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
    let : CreatesColimitsOfShape J (Algebra.forget O) := S.operadicCreatesFilteredColimits O
    let : HasColimitsOfShape J (S.W → S.C) := inferInstance
    exact preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape (Algebra.forget O)

/-- Local presentability on the original small color family category is
transported through its actual discrete-diagram equivalence. -/
theorem SourceContext.coloredCarrierLocallyPresentable [IsLocallyPresentable.{us} S.C] :
    IsLocallyPresentable.{us} (S.W → S.C) := by
  let : EssentiallySmall.{us} (Discrete S.W) := Discrete.essentiallySmallOfSmall
  obtain ⟨κ, hκ, hC⟩ := IsLocallyPresentable.exists_cardinal.{us} S.C
  let : Fact κ.IsRegular := hκ
  let : IsCardinalLocallyPresentable S.C κ := hC
  let : IsCardinalLocallyPresentable (Discrete S.W ⥤ S.C) κ :=
    Functor.isCardinalLocallyPresentable_of_essentiallySmall κ
  let : IsLocallyPresentable.{us} (Discrete S.W ⥤ S.C) := ⟨κ, hκ, inferInstance⟩
  exact (piEquivalenceFunctorDiscrete S.W S.C).symm.isLocallyPresentable

/-- Both original colored generator source and target families are carried
to presentable free tensor-algebra endpoints at the supplied regular rank. -/
theorem SourceContext.operadicFreeEndpointsPresentable (O : ColoredOperadObj S.W S.C)
    (I J : MorphismProperty (S.W → S.C)) (κ : Cardinal.{us}) [Fact κ.IsRegular]
    (h : ∀ s, IsCardinalPresentable (endpoint I J s) κ) :
    ∀ s, IsCardinalPresentable ((freeAlgebraFunctor O).obj (endpoint I J s)) κ := by
  let : (Algebra.forget O).IsCardinalAccessible κ := S.operadicForgetAccessible O κ
  exact freeEndpoints_presentable (S.operadicAdjunction O) I J κ h

/-- The original locally presentable coefficient category and both small
colored generator families give a genuine common regular free-source rank. -/
theorem SourceContext.exists_operadicFreeEndpointRank (O : ColoredOperadObj S.W S.C)
    [IsLocallyPresentable.{us} S.C]
    (I J : MorphismProperty (S.W → S.C)) [I.IsSmall.{us}] [J.IsSmall.{us}]
    (κ₀ : Cardinal.{us}) [Fact κ₀.IsRegular] :
    ∃ (κ : Cardinal.{us}) (_ : Fact κ.IsRegular), κ₀ ≤ κ ∧
      (Algebra.forget O).IsCardinalAccessible κ ∧
      (∀ s, IsCardinalPresentable (endpoint I J s) κ) ∧
      (∀ s, IsCardinalPresentable ((freeAlgebraFunctor O).obj (endpoint I J s)) κ) := by
  let : IsLocallyPresentable.{us} (S.W → S.C) := S.coloredCarrierLocallyPresentable
  let : (Algebra.forget O).IsCardinalAccessible κ₀ := S.operadicForgetAccessible O κ₀
  exact exists_common_free_endpoint_rank (S.operadicAdjunction O) I J κ₀

/-- Both actual free I/J images have complete uniform relative-cell source
smallness at a constructed rank; no free source arrow or cell class is changed. -/
theorem SourceContext.exists_operadicUniformFreeSourceSmallness (O : ColoredOperadObj S.W S.C)
    [IsLocallyPresentable.{us} S.C]
    (I J : MorphismProperty (S.W → S.C)) [I.IsSmall.{us}] [J.IsSmall.{us}]
    (κ₀ : Cardinal.{us}) [Fact κ₀.IsRegular] :
    ∃ (κ : Cardinal.{us}) (_ : Fact κ.IsRegular), κ₀ ≤ κ ∧
      (∀ s, IsCardinalPresentable ((freeAlgebraFunctor O).obj (endpoint I J s)) κ) ∧
      UniformRelativeSourceSmallness.{us} (I.strictMap (freeAlgebraFunctor O)) ∧
      UniformRelativeSourceSmallness.{us} (J.strictMap (freeAlgebraFunctor O)) := by
  let : IsLocallyPresentable.{us} (S.W → S.C) := S.coloredCarrierLocallyPresentable
  let : (Algebra.forget O).IsCardinalAccessible κ₀ := S.operadicForgetAccessible O κ₀
  exact exists_common_uniform_free_source_smallness (S.operadicAdjunction O) I J κ₀

/-- Hom from the original free algebra preserves every original sufficiently
filtered diagram, with independent diagram object and Hom universes. -/
theorem SourceContext.operadicFreeSourcePreserves (O : ColoredOperadObj S.W S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] (X : S.W → S.C) [IsCardinalPresentable X κ]
    (J : Type uJ) [Category.{vJ} J] [EssentiallySmall.{us} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op (freeAlgebra O X))) := by
  let : (Algebra.forget O).IsCardinalAccessible κ := S.operadicForgetAccessible O κ
  exact freeSource_preservesColimitsOfShape (S.operadicAdjunction O) κ X J

/-- The actual original relative-cell endpoint cocone remains colimiting
after Hom from the original free tensor algebra source. -/
def SourceContext.operadicFreeRelativeMappedCocone (O : ColoredOperadObj S.W S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (X : S.W → S.C) [IsCardinalPresentable X κ]
    (P : MorphismProperty (Algebra O)) {A B : Algebra O} {f : A ⟶ B}
    (c : HomotopicalAlgebra.RelativeCellComplex.{us}
      (fun _ : κ.ord.ToType => P.homFamily) f) :
    IsColimit ((coyoneda.obj (op (freeAlgebra O X))).mapCocone (Cocone.mk B c.incl)) := by
  let : (Algebra.forget O).IsCardinalAccessible κ := S.operadicForgetAccessible O κ
  exact freeSourceRelativeComplexMappedCocone (S.operadicAdjunction O) κ X P c

/-- Every map from the actual free source to the original cell endpoint
factors through one of that supplied complex's original stages. -/
theorem SourceContext.operadicFreeRelativeExistsStage (O : ColoredOperadObj S.W S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (X : S.W → S.C) [IsCardinalPresentable X κ]
    (P : MorphismProperty (Algebra O)) {A B : Algebra O} {f : A ⟶ B}
    (c : HomotopicalAlgebra.RelativeCellComplex.{us}
      (fun _ : κ.ord.ToType => P.homFamily) f) (g : freeAlgebra O X ⟶ B) :
    ∃ j, ∃ h : freeAlgebra O X ⟶ c.F.obj j, h ≫ c.incl.app j = g := by
  let : (Algebra.forget O).IsCardinalAccessible κ := S.operadicForgetAccessible O κ
  exact freeSource_relativeComplex_exists_stage (S.operadicAdjunction O) κ X P c g

end CategoryTheory.Operad.Tensor
