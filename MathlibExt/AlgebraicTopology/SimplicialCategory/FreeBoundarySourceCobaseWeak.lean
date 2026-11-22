/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeBoundaryFactorizationSequence
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectSequentialSourcePushoutWeak
import MathlibExt.CategoryTheory.Limits.TransfiniteSourceUnder

/-!
# Genuine weak cobase change along the SAME whole original boundary factorization

The original actual boundary-factorization cell source is reindexed by
its canonical omega stages and lifted under its SAME original source.
Its full terminal under-root colimit is the original native boundary
left map. The proved sequential source comparison therefore gives weak
cobase change along that SAME whole original map, for any supplied
fixed-object arrow and any honestly Homwise weak source map.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
variable {O : Type u} {C X D : FixedObjects O} (p : C ⟶ X)

/-- The SAME full original sequential boundary cells retain their native under-source diagram. -/
abbrev sequentialBoundaryUnder : ℕ ⥤ Under C :=
  (sequentialBoundaryCells p).toTransfiniteCompositionOfShape.sourceUnderDiagram

/-- The SAME first original under-source map retains the native bottom isomorphism. -/
instance sequentialBoundaryUnder_zero_isIso : IsIso ((sequentialBoundaryUnder p).obj 0).hom :=
  TransfiniteCompositionOfShape.sourceUnderDiagram_bot_isIso
    (sequentialBoundaryCells p).toTransfiniteCompositionOfShape

/-- Every whole original successor attachment is the SAME supplied native boundary-cell occurrence family. -/
def sequentialBoundaryUnderCells (n : ℕ) :
    AttachCells.{u} (boundaryFamily O).homFamily
      ((SequentialSourcePushout.source (sequentialBoundaryUnder p)).map (homOfLE (n.le_add_right 1))) :=
  (sequentialBoundaryCells p).attachCells n (not_isMax n)

/-- The SAME whole original boundary-factorization source gives genuine weak cobase change. -/
theorem boundarySource_cobase_weak (F : C ⟶ D) (hF : FixedObjectModel.weakEquivalences O F) :
    FixedObjectModel.weakEquivalences O (pushout.inl (boundary p).i F) :=
  SequentialSourcePushout.terminal_comparison_weak (sequentialBoundaryUnder p) F
    (sequentialBoundaryUnderCells p) hF
    ((sequentialBoundaryCells p).toTransfiniteCompositionOfShape.sourceUnderCocone)
    ((sequentialBoundaryCells p).toTransfiniteCompositionOfShape.sourceUnderIsColimit)

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
