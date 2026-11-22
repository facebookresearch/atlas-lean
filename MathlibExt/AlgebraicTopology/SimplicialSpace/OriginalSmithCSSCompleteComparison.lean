/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSmithCSSReplacement
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalLevelwiseIntrinsicDK
import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessHorelComparison

/-!
# Smith replacement of complete Segal spaces

For a complete Segal space, the Smith Rezk replacement unit is a realization weak equivalence in
every outer degree. It consequently gives an intrinsic Dwyer–Kan equivalence between the input
and its complete Segal replacement.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra Opposite
open scoped Simplicial
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialSpace.OriginalSmithCSS

/-- On an already complete input, the actual Smith unit is weak in every original row. -/
theorem unit_levelwise_weak_of_complete (W : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (n : ℕ) :
    SSet.realizationWeakEquivalences ((unit.app W).hom.app (op ⦋n⦌)) := by
  have hWlocal :=
    (SimplicialPresheaf.OriginalRezkLocalizer.coefficientLocalFibrant_iff_completeSegalSpaces
      W.diagram).mpr hW
  have hRlocal := SimplicialPresheaf.OriginalLocalDerived.localR_isOriginalLocalFibrant
    SSet.Rezk.localizingMap.{u} W.diagram
  have h :=
    (SimplicialPresheaf.InjectiveKan.originalLocalEquivalence_iff_weakEquivalence_of_localFibrant
      SSet.Rezk.localizingMap.{u}
      ((SimplicialPresheaf.OriginalLocalDerived.localRUnit
          SSet.Rezk.localizingMap.{u}).app W.diagram)
      hWlocal hRlocal).mp
        (SimplicialPresheaf.OriginalLocalDerived.localRUnit_localTrivialCofibration
          SSet.Rezk.localizingMap.{u} W.diagram).2
  change
      (SimplicialPresheaf.InjectiveKan.data.{u}
        SimplexCategory).model.categoryWithWeakEquivalences.weakEquivalences
    ((SimplicialPresheaf.OriginalLocalDerived.localRUnit SSet.Rezk.localizingMap.{u}).app
        W.diagram) at h
  rw [(SimplicialPresheaf.InjectiveKan.data.{u} SimplexCategory).weakEquivalences_eq] at h
  exact h (op ⦋n⦌)

/-- This same native unit is intrinsically DK at complete endpoints. -/
theorem unit_intrinsicDK_of_complete (W : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) :
    IntrinsicDK.isEquivalence (unit.app W)
      (((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1)
      (((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete
        (replacement.obj W)).mp (replacement_completeSegal W)).1) :=
  IntrinsicDK.of_levelwiseWeak (unit.app W)
    (((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1)
    (((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete
      (replacement.obj W)).mp (replacement_completeSegal W)).1)
    (unit_levelwise_weak_of_complete W hW)

end SimplicialSpace.OriginalSmithCSS
