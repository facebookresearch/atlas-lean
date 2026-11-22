/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingFibreStandardLoop

/-!
# The actual continuous standard diagonal edge-loop map

The original whole mapping parameter and original ordinal interval define
a continuous based loop family. Its full pointwise formula is the original
realized row-simplex cylinder, with the original interval identification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The whole original endomorphism mapping fibre has its actual standard continuous edge-loop map. -/
def standardDiagonalLoopMap (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.toTop.obj (mappingFibre W x x) ⟶
      TopCat.of (LoopSpace (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram))
        (realizedDiagonalPoint W x)) :=
  TopCat.ofHom {
    toFun := standardDiagonalLoopValue W x
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z : SSet.toTop.obj (mappingFibre W x x) × unitInterval =>
        mappingFibreDiagonalPathFamily W x x z.1 (TopCat.I.homeomorph.symm z.2))
      exact continuous_eval.comp
        (((mappingFibreDiagonalPathFamily W x x).hom.continuous.comp continuous_fst).prodMk
          (TopCat.I.homeomorph.symm.continuous.comp continuous_snd)) }

/-- Every original point and time retains the actual whole interval-family formula. -/
theorem standardDiagonalLoopMap_apply (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (z : SSet.toTop.obj (mappingFibre W x x)) (t : unitInterval) :
    standardDiagonalLoopMap W x z t =
      mappingFibreDiagonalPathFamily W x x z (TopCat.I.homeomorph.symm t) := rfl

end SimplicialSpace.LeftDecalageObject
