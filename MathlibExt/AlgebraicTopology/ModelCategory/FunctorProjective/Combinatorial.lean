/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import Mathlib.CategoryTheory.Presentable.Presheaf
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.EssentialIndex
import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
import MathlibExt.CategoryTheory.Functor.SmallIndex

/-!
# Combinatoriality of the original ordinary projective model

The existing essential-index factory supplies actual representative generating
families at the original coefficient cardinal. Local presentability on the
unchanged functor category follows through the same full small-index equivalence.
Together these are witnesses of combinatoriality for that actual model.

This is the projective combinatoriality conclusion of *Higher Topos Theory*,
Proposition A.2.8.2, author version of April 9, 2017, printed page 830
(PDF page 848). The diagram model and its generation are outputs.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

namespace HomotopicalAlgebra.FunctorProjective

open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  [IsCardinalLocallyPresentable C kappa] (s : Functor.EssentialIndexData.{w} D C)

/-- The original generation and local-presentability witnesses at the same
coefficient cardinal make the actual essential-index model combinatorial. -/
theorem originalProjectiveModel_isCombinatorial :
    letI : LocallySmall.{w} s.index := locallySmall_self s.index
    letI : ModelCategory (D ⥤ C) := EssentialIndex.modelCategory s.equivalence d
    IsCombinatorialModelCategory.{w} (D ⥤ C) := by
  let : LocallySmall.{w} s.index := locallySmall_self s.index
  let : ModelCategory (D ⥤ C) := EssentialIndex.modelCategory s.equivalence d
  have hPresentable : IsCardinalLocallyPresentable (D ⥤ C) kappa := by
    let : SmallCategory s.index := s.indexCategory
    let : IsCardinalLocallyPresentable (s.indexᵒᵖᵒᵖ ⥤ C) kappa := inferInstance
    let : IsCardinalLocallyPresentable (s.index ⥤ C) kappa :=
      ((opOpEquivalence s.index).congrLeft (E := C)).isCardinalLocallyPresentable kappa
    exact (s.equivalence.congrLeft (E := C)).symm.isCardinalLocallyPresentable kappa
  exact
    { exists_cardinal :=
        ⟨kappa, inferInstance, inferInstance, hPresentable,
          ⟨EssentialIndex.generationData s.equivalence d⟩⟩ }

end HomotopicalAlgebra.FunctorProjective
