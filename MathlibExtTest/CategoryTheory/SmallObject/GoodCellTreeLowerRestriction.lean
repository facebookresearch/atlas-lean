/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerRestriction
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramActionCapture

/-!
# Literal original lower-subtree semantic checks

The tree and chosen lower data are the actual original fold presentation at
source label seven. The restricted index remains the literal original lower
subtype, and its root still has the actual chosen cardinal. Both empty and
nonempty original supports retain full predecessor, cell and endpoint maps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t w u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  CellTreeLowerRestriction BoundedLowerSupport

namespace OriginalLowerCellTreeExamples

open GoodCellTreeDataExamples DiagramActionConstraintBoundExamples
  OriginalDiagramActionCaptureExamples

/-- The exact original component tree at its original source label seven. -/
abbrev originalTree : CellTree foldFamily.{t} (originalSource.obj sourceSeven)
    (P := originalLabels sourceSeven) := (originalTrees.{t}.component sourceSeven).tree

/-- Its chosen original all-lower colimits, fixed before any restriction. -/
abbrev originalL : LowerSetColimitData originalTree.{t}.diagram := originalLower.{t} sourceSeven

/-- The actual original nonempty support at source seven, with its original label family. -/
abbrev originalSupport : LowerSet (originalLabels sourceSeven) := (nonemptySeeds.{t} sourceSeven).1

/-- Invoke the full original lower-subtree constructor on the same literal support. -/
def actualRestrictedTree : CellTree foldFamily.{t} (originalSource.obj sourceSeven)
    (P := originalSupport.{t}) := tree originalTree.{t} originalL.{t} originalSupport.{t}

/-- The complete original vertex function is unchanged at every literal original selected label. -/
theorem actualRestrictedTree_vertex_function :
    (fun a : originalSupport.{t} => actualRestrictedTree.{t}.vertex a) =
      (fun a : originalSupport.{t} => originalTree.{t}.vertex a.1) := rfl

/-- Every actual original comparison map retains the original underlying label morphism. -/
theorem actualRestrictedTree_map_function :
    (fun (a b : originalSupport.{t}) (f : a ⟶ b) => actualRestrictedTree.{t}.diagram.map f) =
      (fun (a b : originalSupport.{t}) (f : a ⟶ b) =>
        originalTree.{t}.diagram.map (homOfLE (leOfHom f))) := rfl

/-- Every original attaching generator label is literally the same at the original selected label. -/
theorem actualRestrictedTree_label_function :
    actualRestrictedTree.{t}.label = (fun a : originalSupport.{t} => originalTree.{t}.label a.1) := rfl

/-- The entire actual original cell function is unchanged, on all original dependent coefficient types. -/
theorem actualRestrictedTree_cell_function :
    (fun a : originalSupport.{t} => actualRestrictedTree.{t}.cell a) =
      (fun a : originalSupport.{t} => originalTree.{t}.cell a.1) := rfl

/-- The selected endpoint is the SAME original chosen lower object under its original root. -/
theorem actualRestrictedTree_endpoint :
    actualRestrictedTree.{t}.endpointObj = originalL.{t}.obj originalSupport.{t} := rfl

/-- The actual root function into that chosen original lower endpoint is unchanged. -/
theorem actualRestrictedTree_root :
    actualRestrictedTree.{t}.hom = (originalL.{t}.obj originalSupport.{t}).hom := rfl

/-- Every original selected lower-cocone leg is retained as an entire function. -/
theorem actualRestrictedTree_endpoint_leg_function :
    (fun a : originalSupport.{t} => actualRestrictedTree.{t}.inclusion a) =
      (fun a : originalSupport.{t} => originalL.{t}.ι originalSupport.{t} a) := rfl

/-- Goodness is proved from the original generator endpoints and predecessor bounds. -/
theorem actualRestrictedTree_good : actualRestrictedTree.{t}.IsGood chi :=
  tree_good originalTree.{t} originalL.{t} originalSupport.{t} chi (originalTrees_good.{t} sourceSeven)

/-- The original root still has its actual direct-rank cardinal, independently of support size. -/
theorem actualRestrictedTree_original_root_boundary :
    ¬ HasCardinalLT (originalSource.obj sourceSeven) chi :=
  OriginalDiagramActionCoherenceExamples.originalSourceRoot_not_cardinalLT

/-- The actual original seed point remains a literal label of the restricted tree. -/
def originalSeedLabel : originalSupport.{t} :=
  ⟨⟨originalRootPoint sourceSeven⟩, nonemptySeeds_contains.{t} sourceSeven⟩

/-- Its actual predecessor-to-vertex map is the SAME original selected map. -/
theorem actualRestrictedTree_predecessorMap :
    actualRestrictedTree.{t}.predecessorMap originalSeedLabel.{t} =
      originalTree.{t}.predecessorMap originalSeedLabel.{t}.1 :=
  predecessorMap originalTree.{t} originalSupport.{t} originalSeedLabel.{t}

/-- The actual empty lower restriction keeps the original initial under-root endpoint. -/
def actualEmptyTree : CellTree foldFamily.{t} (originalSource.obj sourceSeven)
    (P := (⊥ : LowerSet (originalLabels sourceSeven))) :=
  tree originalTree.{t} originalL.{t} ⊥

/-- The empty tree endpoint is still the same original chosen empty L object. -/
theorem actualEmptyTree_endpoint : actualEmptyTree.{t}.endpointObj = originalL.{t}.obj ⊥ := rfl

/-- The actual original empty-root comparison is the given original empty lower isomorphism. -/
def actualEmptyTreeOriginalRootIso : actualEmptyTree.{t}.endpointObj ≅
    Under.mk (𝟙 (originalSource.obj sourceSeven)) := originalTree.{t}.emptyLowerIso originalL.{t}

section IndependentOriginalUniverses

variable {P : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  {alpha : Type t} {s : alpha → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram) (B : LowerSet P)

/-- The full constructor keeps every original label, coefficient, root and generator universe. -/
theorem independentOriginalRestrictionEndpoint : (tree T L B).endpointObj = L.obj B := rfl

/-- The full original coefficient Hom function retains every actual label comparison. -/
theorem independentOriginalRestrictionMaps :
    (fun (a b : B) (f : a ⟶ b) => (tree T L B).diagram.map f) =
      (fun (a b : B) (f : a ⟶ b) => T.diagram.map (homOfLE (leOfHom f))) := rfl

end IndependentOriginalUniverses

end OriginalLowerCellTreeExamples
