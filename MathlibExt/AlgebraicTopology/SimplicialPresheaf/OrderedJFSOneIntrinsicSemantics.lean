/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- External complete proof draft; Root Source review and native dispatch precede execution.
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneCoordinateData
import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessHorelComparison

/-!
# Intrinsic completeness at one simplex coordinate

Intrinsic completeness of a one-coordinate diagram consists of Reedy fibrancy of its
designated simplicial space, weakness of every native Segal homotopy-pullback comparison, and
weakness of the equivalence-identity map. These conditions are equivalent to the finite
complete Segal-space condition and to the complete Segal-space predicate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialPresheaf.OrderedJFS

/-- The original intrinsic one-fold condition: genuine Reedy fibrancy of Phi1(X),
weakness of every actual finite homotopy-pullback Segal comparison, and weakness of
the original equivalence-identity map. The Segal witness is derived internally
from those RF and comparison fields; no locality or completion outcome is an input. -/
def oneIntrinsicComplete (X : Original.{u} 1) : Prop :=
  let W := oneDesignatedEquivalence.{u}.functor.obj X
  letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  ∃ (hRF : IsFibrant W)
    (hComparisons : ∀ (n : ℕ) (hn : 2 ≤ n),
      SSet.realizationWeakEquivalences (SimplicialSpace.segalNativeHomotopyComparison W n hn)),
    SSet.realizationWeakEquivalences
      (SimplicialSpace.SegalHomotopy.equivalenceIdentity W
        ((SimplicialSpace.segalSpaces_iff_nativeHomotopyPullbackComparisons W).mpr
          ⟨hRF, hComparisons⟩))

private theorem oneIntrinsicComplete_iff_finite (X : Original.{u} 1) :
    oneIntrinsicComplete X ↔
      SimplicialSpace.FiniteCompletenessHorel.finiteCompleteSegalSpaces
        (oneDesignatedEquivalence.{u}.functor.obj X) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let W := oneDesignatedEquivalence.{u}.functor.obj X
  change (∃ (hRF : IsFibrant W)
      (hComparisons : ∀ (n : ℕ) (hn : 2 ≤ n),
        SSet.realizationWeakEquivalences (SimplicialSpace.segalNativeHomotopyComparison W n hn)),
      SSet.realizationWeakEquivalences
        (SimplicialSpace.SegalHomotopy.equivalenceIdentity W
          ((SimplicialSpace.segalSpaces_iff_nativeHomotopyPullbackComparisons W).mpr
            ⟨hRF, hComparisons⟩))) ↔
    (SimplicialSpace.segalSpaces W ∧
      SSet.realizationWeakEquivalences
        (SimplicialSpace.FiniteCompletenessMapping.restriction W
          SSet.Rezk.FiniteCompleteness.kappa))
  constructor
  · rintro ⟨hRF, hComparisons, hIdentity⟩
    let hSegal := (SimplicialSpace.segalSpaces_iff_nativeHomotopyPullbackComparisons W).mpr
      ⟨hRF, hComparisons⟩
    exact ⟨hSegal,
      (SimplicialSpace.FiniteCompletenessHorel.completeness_tests_iff W hSegal).2.2.2.mpr
        hIdentity⟩
  · rintro ⟨hSegal, hKappa⟩
    have hFields := (SimplicialSpace.segalSpaces_iff_nativeHomotopyPullbackComparisons W).mp hSegal
    refine ⟨hFields.1, hFields.2, ?_⟩
    exact (SimplicialSpace.FiniteCompletenessHorel.completeness_tests_iff W hSegal).2.2.2.mp
      hKappa

/-- The independently defined original intrinsic condition is exactly scalar CSS.
The finite/full Horel theorem is reused under its actual RF and Segal hypotheses;
the kappa and source-zero arrows are not identified as an Arrow isomorphism. -/
theorem oneIntrinsicComplete_iff_completeSegalSpaces (X : Original.{u} 1) :
    oneIntrinsicComplete X ↔
      SimplicialSpace.completeSegalSpaces
        (oneDesignatedEquivalence.{u}.functor.obj X) :=
  (oneIntrinsicComplete_iff_finite X).trans
    (SimplicialSpace.FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete
      (oneDesignatedEquivalence.{u}.functor.obj X)).symm

end SimplicialPresheaf.OrderedJFS
