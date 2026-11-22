/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original whole coefficient-diagonal evaluation from the raw completeness proof.
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCorePowerDiagonalSelector
import MathlibExt.AlgebraicTopology.SimplicialSpace.FullEEquivalenceTrivialFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# Forward-edge evaluation on the diagonal core

For a Segal space, evaluating maps from the walking isomorphism on its forward edge defines a
natural map from the coefficient-power mapping diagram to the core-power diagram. The levelwise
trivial-fibration comparisons imply that the induced simplicial diagonal map is a realization
weak equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
    HomotopicalAlgebra
open scoped Simplicial MonoidalCategory SimplicialSpace.Inner SimplicialSpace.Cartesian
    SSet.modelCategoryQuillen
namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw SegalHomotopy WalkingEUnit

/-- The diagram of mapping spaces from `coherentSpace` into the coefficient powers of `W`. -/
def originalFullEEndDiagram (W : SimplicialSpace.{u}) : SimplicialObject SSet.{u} :=
  powerDiagram W ⋙ innerHomFunctor.obj (op coherentSpace)


/-- Evaluate the full walking isomorphism on its forward edge in each coefficient power. -/
def originalFullEForwardEvaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    originalFullEEndDiagram W ⟶ corePowerDiagram W hW where
  app n := FullEEquivalence.evaluation ((powerDiagram W).obj n)
    (powerDiagram_segal W hW n) SSet.coherentIso.forwardMap
  naturality n m δ :=
    FullEEquivalence.evaluation_naturality_target ((powerDiagram W).map δ)
      (powerDiagram_segal W hW n) (powerDiagram_segal W hW m)
      SSet.coherentIso.forwardMap


theorem originalFullEForwardEvaluation_diagonal_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map (originalFullEForwardEvaluation W hW)) := by
  apply SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences
  intro n
  exact (FullEEquivalence.forwardEvaluation_trivialFibration
    ((powerDiagram W).obj (op ⦋n⦌))
      (powerDiagram_segal W hW (op ⦋n⦌))).2


end SimplicialSpace.RezkCompletionCoreDiagonal
