/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCorePowerDiagonalSelector
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkPowerCoreRelativeComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.RezkDiagonalSharpHomotopyPullback
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Original whole core-endpoint diagram and Rezk 6.1 hypotheses

The diagram consists of the actual equivalence cores of ALL original full-J
powers, over their ordered source/target object pairs. Its row Sharpness is
derived from the genuine core endpoint fibrations and scalar right properness.
Every original operator-relative comparison is the existing total core-relative
map whose weakness is internally derived from the original MF/EF comparisons.
The caller supplies no Sharp, operator-WE, kappa-WE or completion outcome.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw
open SSet.SharpComparisonDraft

/-- The ordered object pairs of EVERY same original coefficient power. -/
def originalCorePairDiagram (W : SimplicialSpace.{u}) : SimplicialObject SSet.{u} where
  obj n := (((powerDiagram W).obj n).diagram _⦋0⦌) ⨯
    (((powerDiagram W).obj n).diagram _⦋0⦌)
  map f := prod.map (((powerDiagram W).map f).hom.app (op ⦋0⦌))
    (((powerDiagram W).map f).hom.app (op ⦋0⦌))
  map_id n := by
    rw [(powerDiagram W).map_id]
    change prod.map (𝟙 _) (𝟙 _) = 𝟙 _
    apply prod.hom_ext <;> simp
  map_comp f g := by
    rw [(powerDiagram W).map_comp]
    change prod.map (_ ≫ _) (_ ≫ _) = prod.map _ _ ≫ prod.map _ _
    exact (prod.map_map _ _ _ _).symm

set_option linter.unusedVariables false in
/-- The literal original source-first/target-second core endpoint diagram. -/
def originalCoreEndpointDiagram (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    corePowerDiagram W hW ⟶ originalCorePairDiagram W where
  app n := SegalHomotopy.coreEndpoint ((powerDiagram W).obj n)
    (powerDiagram_segal W hW n)
  naturality n m f :=
    RezkPowerCoreRelativeComparison.coreMap_endpoint f.unop W hW

/-- Each actual row projection is a fibration through the original Reedy
endpoint and the genuine equivalence component-union inclusion. -/
theorem originalCoreEndpointDiagram_row_fibration (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (n : SimplexCategory) :
    Fibration ((originalCoreEndpointDiagram W hW).app (op n)) :=
  SegalHomotopy.coreEndpoint_fibration ((powerDiagram W).obj (op n))
    (powerDiagram_segal W hW (op n))

/-- Row Sharpness follows from actual fibrations and native right properness;
every original base-change test is retained. -/
theorem originalCoreEndpointDiagram_row_sharp (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (n : SimplexCategory) :
    Sharp ((originalCoreEndpointDiagram W hW).app (op n)) := by
  let : Fibration ((originalCoreEndpointDiagram W hW).app (op n)) :=
    originalCoreEndpointDiagram_row_fibration W hW n
  intro T t
  let : Fibration ((cospan ((originalCoreEndpointDiagram W hW).app (op n)) t).map
      WalkingCospan.Hom.inl) := originalCoreEndpointDiagram_row_fibration W hW n
  exact HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_rightProper_inl
    (cospan ((originalCoreEndpointDiagram W hW).app (op n)) t)

/-- The operator-relative comparison is the literal original full pullback
lift with the same total and ordered pair projections. -/
theorem originalCoreEndpointDiagram_relativeComparison (W : SimplicialSpace.{u})
    (hW : segalSpaces W) {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.EquifibredDiagonal.relativeComparison (originalCoreEndpointDiagram W hW) f =
      RezkPowerCoreRelativeComparison.relativeMap f W hW := rfl

/-- All relative weaknesses are derived internally from the original power
MF and selected-component EF comparison proof, including maps that move zero. -/
theorem originalCoreEndpointDiagram_relativeComparison_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {n m : SimplexCategory} (f : n ⟶ m) :
    WeakEquivalence
      (SSet.EquifibredDiagonal.relativeComparison (originalCoreEndpointDiagram W hW) f) := by
  have h : WeakEquivalence (RezkPowerCoreRelativeComparison.relativeMap f W hW) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).2
      (RezkPowerCoreRelativeComparison.relativeMap_weak f W hW)
  exact (originalCoreEndpointDiagram_relativeComparison W hW f).symm ▸ h

/-- Rezk's Theorem 6.1 gives diagonal sharpness for this original core-endpoint
diagram. The project corollary supplies all native homotopy pullback
comparisons; both hypothesis families are derived above. -/
theorem originalCoreEndpointDiagram_all_simplex_and_homotopy_pullback (W : SimplicialSpace.{u})
    (hW : segalSpaces W) :
    SSet.SharpSaturation.allSimplexComparisons
        (SSet.simplicialDiagonalFunctor.map (originalCoreEndpointDiagram W hW)) ∧
      Sharp (SSet.simplicialDiagonalFunctor.map (originalCoreEndpointDiagram W hW)) ∧
      ∀ (n : SimplexCategory) (v : Fin (n.len + 1)),
        WeakEquivalence (SSet.RezkOriginal61.kappa (originalCoreEndpointDiagram W hW) n v) :=
  SSet.RezkOriginal61.all_simplex_sharp_and_native_homotopy_pullback
    (originalCoreEndpointDiagram W hW) (originalCoreEndpointDiagram_row_sharp W hW)
    (originalCoreEndpointDiagram_relativeComparison_weak W hW)

/-- The full original PB lift before native homotopy comparison is retained
for every ordinal and vertex, without replacing eta by a constant diagram. -/
theorem originalCoreEndpointDiagram_kappa_actual_lift (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (n : SimplexCategory) (v : Fin (n.len + 1)) :
    SSet.RezkOriginal61.kappa (originalCoreEndpointDiagram W hW) n v =
      pullback.lift (SSet.EquifibredDiagonal.rowVertexToDiagonal (corePowerDiagram W hW) n v)
        ((originalCoreEndpointDiagram W hW).app (op n))
        (SSet.EquifibredDiagonal.rowVertexToDiagonal_naturality
          (originalCoreEndpointDiagram W hW) n v) ≫
        (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app
          (cospan (SSet.simplicialDiagonalFunctor.map (originalCoreEndpointDiagram W hW))
            (SSet.EquifibredDiagonal.rowVertexToDiagonal (originalCorePairDiagram W) n v)) :=
  SSet.RezkOriginal61.kappa_actual_original_lift (originalCoreEndpointDiagram W hW) n v

end SimplicialSpace.RezkCompletionCoreDiagonal
