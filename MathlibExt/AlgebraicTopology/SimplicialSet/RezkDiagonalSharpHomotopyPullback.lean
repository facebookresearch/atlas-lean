/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalColimitAndFullSimplexSharp

/-!
# Diagonal sharpness and native homotopy pullback comparisons

Rezk's *Fibrations and Homotopy Colimits of Simplicial Sheaves* (1998),
Theorem 6.1 (p. 11), concludes that the diagonal map is sharp from row
sharpness and homotopy cartesian operator squares. The second conjunct
below records that conclusion. The first conjunct is the all-simplex
criterion returned by the formal diagonal-sharpness proof; the third
is a further project consequence for native homotopy pullbacks.

For each ordinal `n` and vertex `v`, the comparison has source `Xₙ` and
target the homotopy pullback of `diag X → diag Y ← Yₙ`. Its right leg is
`EquifibredDiagonal.rowVertexToDiagonal Y n v`, with domain the whole row
`Yₙ`; `v` selects a vertex of the ordinal `n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkOriginal61
open SharpComparisonDraft

/-- The native comparison from `Xₙ` to the homotopy pullback of
`diag X → diag Y ← Yₙ`, whose right leg uses the vertex `v` of `n`.
It composes the original ordinary pullback lift with the canonical
homotopy pullback comparison. -/
def kappa {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :=
  EquifibredDiagonal.vertexDiagonalPullbackComparison eta n v ≫
    comparison (simplicialDiagonalFunctor.map eta) (EquifibredDiagonal.rowVertexToDiagonal Y n v)

/-- The native comparison is the literal ordinary pullback lift followed
by the canonical homotopy pullback comparison, for every vertex `v`. -/
theorem kappa_actual_original_lift {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    kappa eta n v =
      pullback.lift (EquifibredDiagonal.rowVertexToDiagonal X n v) (eta.app (op n))
        (EquifibredDiagonal.rowVertexToDiagonal_naturality eta n v) ≫
        (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
          (cospan (simplicialDiagonalFunctor.map eta)
              (EquifibredDiagonal.rowVertexToDiagonal Y n v)) := rfl

/-- Row sharpness and operator-relative weak equivalences give diagonal
sharpness, its formal all-simplex criterion, and native homotopy pullback
weak equivalences for every ordinal `n` and vertex `v`.

The second conjunct is the conclusion of Rezk's *Fibrations and Homotopy
Colimits of Simplicial Sheaves* (1998), Theorem 6.1. The first conjunct
records the criterion returned by the formal diagonal-sharpness proof.
The third is a project corollary: the ordinary vertex comparison and the
native comparison supplied by diagonal sharpness are weak equivalences. -/
theorem all_simplex_sharp_and_native_homotopy_pullback
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ n : SimplexCategory, Sharp (eta.app (op n)))
    (hoperators : ∀ {n m : SimplexCategory} (f : n ⟶ m),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f)) :
    SharpSaturation.allSimplexComparisons (simplicialDiagonalFunctor.map eta) ∧
      Sharp (simplicialDiagonalFunctor.map eta) ∧
      ∀ (n : SimplexCategory) (v : Fin (n.len + 1)), WeakEquivalence (kappa eta n v) := by
  have diagonal := RezkSkeletalColimit.all_simplex_and_diagonal_sharp_from_original_operators
    eta hrows hoperators
  refine ⟨diagonal.1, diagonal.2, ?_⟩
  intro n v
  have ordinary :
      WeakEquivalence (EquifibredDiagonal.vertexDiagonalPullbackComparison eta n v) := by
    apply (HomotopicalAlgebra.weakEquivalence_iff _).2
    apply EquifibredDiagonal.realizationWeak_vertexDiagonalPullbackComparison eta
    intro a b f
    exact (HomotopicalAlgebra.weakEquivalence_iff _).1 (hoperators f)
  let := ordinary
  let : WeakEquivalence
      (comparison (simplicialDiagonalFunctor.map eta)
          (EquifibredDiagonal.rowVertexToDiagonal Y n v)) :=
    diagonal.2 _ _
  dsimp only [kappa]
  infer_instance

end SSet.RezkOriginal61
