/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.AllFiniteSkeletalIncoming
import MathlibExt.AlgebraicTopology.SimplicialSet.AllSimplexSequentialCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# Sharpness of bisimplicial diagonal maps

A bisimplicial map with sharp rows and weak pullback comparisons for every simplex operator induces a sharp diagonal map. Its finite skeletal invariants and incoming homotopy cartesian squares establish the full simplex comparison criterion for the diagonal through the skeletal colimit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalColimit
open SharpComparisonDraft RezkAllSkeletalInvariants RezkAllFiniteSkeletalIncoming

/-- Original Rezk6.1 diagonal Sharpness, using the EXISTING actual native
skeletal functor, cocones, IsColimit and natural map. Finite Sharp/allincoming
are derived from original rows and ALL operator comparisons. Every simplex
and delta, including m>a, uses one actual finite lift stage. Total Sharp is
concluded after the complete criterion, never assumed in a basechange. -/
theorem all_simplex_and_diagonal_sharp_from_original_operators
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f)) :
    SharpSaturation.allSimplexComparisons (simplicialDiagonalFunctor.map eta) ∧
      Sharp (simplicialDiagonalFunctor.map eta) := by
  have finite := all_skeletal_sharp_and_cell_incoming eta hrows hoperators
  apply RezkAllSimplexSequential.all_simplex_and_sharp_of_actual_finite_tail
    (diagonalFiltrationNatTrans eta) (diagonalFiltrationCocone X) (diagonalFiltrationCocone Y)
    (simplicialDiagonalFunctor.map eta)
  · intro n
    exact (diagonalFiltrationNatMap_ι eta n).symm
  · exact diagonalFiltrationCoconeIsColimit X
  · exact diagonalFiltrationCoconeIsColimit Y
  · intro i j f
    change Mono (diagonalFiltrationMap X (leOfHom f))
    infer_instance
  · intro n
    exact (finite n).1
  · intro n k
    exact all_finite_skeletal_incoming_hc eta hrows hoperators n (n + k) (Nat.le_add_right n k)

end SSet.RezkSkeletalColimit
