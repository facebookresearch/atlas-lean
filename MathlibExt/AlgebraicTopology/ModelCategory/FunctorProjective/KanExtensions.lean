/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Restriction
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.LeftKanExtensions
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# The actual native projective left Kan Quillen adjunction

The functor and adjunction are the existing `u.lan` and `u.lanAdjunction`.
The fixed-data entry derives the required original comma dictionaries
from dD and retains both original projective models and cardinals.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM wD wE
open CategoryTheory Functor

namespace HomotopicalAlgebra.FunctorProjective.KanExtensions

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]

/-- The actual native Lan adjunction is Quillen for the prescribed original right classes. -/
theorem isQuillen_of_pointwise_right_classes (u : D ⥤ E)
    [∀ F : D ⥤ M, u.HasLeftKanExtension F]
    [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]
    (hFD : fibrations (D ⥤ M) = (fibrations M).functorCategory D)
    (hFE : fibrations (E ⥤ M) = (fibrations M).functorCategory E)
    (hTD : trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D)
    (hTE : trivialFibrations (E ⥤ M) = (trivialFibrations M).functorCategory E) :
    (u.lanAdjunction M).IsQuillenAdjunction := by
  have h := Restriction.preserves_right_classes_of_eqs hFD hFE hTD hTE u
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (adj := u.lanAdjunction M) h.1 h.2

variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  [Small.{wD} D] [LocallySmall.{wD} D] [Small.{wE} E] [LocallySmall.{wE} E]
  [LocallySmall.{wD} E]

/-- Actual dD comma colimits and the two original independent data give the same native Lan. -/
theorem isQuillen (dD : CofibrantGenerationData M κD)
    (dE : CofibrantGenerationData M κE) (u : D ⥤ E) :
    letI : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (u.lanAdjunction M).IsQuillenAdjunction := by
  let _ : ∀ F : D ⥤ M, u.HasLeftKanExtension F := fun F => dD.hasLeftKanExtension u F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact isQuillen_of_pointwise_right_classes u
    (FunctorProjective.fibrations_eq.{wD} dD) (FunctorProjective.fibrations_eq.{wE} dE)
    (FunctorProjective.trivialFibrations_eq.{wD} dD)
    (FunctorProjective.trivialFibrations_eq.{wE} dE)

end HomotopicalAlgebra.FunctorProjective.KanExtensions
