/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerRelativeCyBarCounitSquare

/-!
# Postcomposition of the relative Calabi-Yau bar-counit square

The two bar-counit composites remain equal after postcomposition by a module map.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, Theorems 6.1 and 6.2,
Definition 4.11 and diagrams 6.5--6.7. The ground ring is a field; this
composition theorem has no characteristic-zero restriction.
-/

namespace MathlibExtTest.AlgebraicGeometry.DGRelativeCYDiagramLedgerRelativeCyBarCounitSquare

open CategoryTheory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger
open MathlibExt.Algebra.Homology.DGCategoryTraceModels
open WantedExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerWanted

universe u

example (k : Type u) [Field k] (P : Cospan (k := k)) (S : NegativeTraceSystem k)
    (n : ℤ) (D : ModuleData P S n) (K : InductionData D)
    (N : RightModule k (enveloping P.Z P.Z)) (a : D.DZ.bar.module ⟶ N) :
    K.topCounit ≫ D.I.counit.map ≫ a = K.leftCounit ≫ D.J.counit.map ≫ a := by
  exact (Category.assoc K.topCounit D.I.counit.map a).symm.trans
    ((congrArg (fun b => b ≫ a) (relative_cy_bar_counit_square k P S n D K).comm).trans
      (Category.assoc K.leftCounit D.J.counit.map a))

end MathlibExtTest.AlgebraicGeometry.DGRelativeCYDiagramLedgerRelativeCyBarCounitSquare
