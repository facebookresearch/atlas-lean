/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.DiagonalRowSimplexVertices
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidLoopComparison
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# The actual interval cylinder of an original mapping fibre

The original whole mapping edge evaluates against the actual ordinal
interval. Its zero and one restrictions are the same prescribed source
and target points in the original diagonal. This is the original edge
family that will identify the native bar loop map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The original mapping fibre evaluated against the whole original ordinal interval. -/
def mappingFibreDiagonalCylinder (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingFibre W x y ⊗ (Δ[1] : SSet.{u})) ⟶ SSet.simplicialDiagonalFunctor.obj W.diagram :=
  (mappingFibre.fst W x y ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫
    SSet.EquifibredDiagonal.rowSimplexEvaluation W.diagram (SimplexCategory.mk 1)

/-- The whole original mapping-fibre point map to its prescribed diagonal source. -/
def mappingFibreDiagonalSource (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ SSet.simplicialDiagonalFunctor.obj W.diagram :=
  mappingFibre.snd W x y ≫ diagonalPoint W x

/-- The whole original mapping-fibre point map to its prescribed diagonal target. -/
def mappingFibreDiagonalTarget (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ SSet.simplicialDiagonalFunctor.obj W.diagram :=
  mappingFibre.snd W x y ≫ diagonalPoint W y

set_option backward.isDefEq.respectTransparency false in
/-- The source end of the original interval cylinder is the original prescribed source point. -/
theorem mappingFibreDiagonalCylinder_zero (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.ι₀ ≫ mappingFibreDiagonalCylinder W x y = mappingFibreDiagonalSource W x y := by
  apply NatTrans.ext
  funext e
  apply ConcreteCategory.hom_ext
  intro z
  change (W.diagram.map (SSet.stdSimplex.objEquiv
    ((SSet.ι₀ (X := mappingFibre W x y)).app e z).2).op).app e
      ((mappingFibre.fst W x y).app e z) = _
  have he : SSet.stdSimplex.objEquiv
      ((SSet.ι₀ (X := mappingFibre W x y)).app e z).2 =
      SimplexCategory.const e.unop (SimplexCategory.mk 1) 0 := rfl
  rw [he]
  have hc : SimplexCategory.const e.unop (SimplexCategory.mk 1) 0 =
      SimplexCategory.const e.unop (SimplexCategory.mk 0) 0 ≫ SimplexCategory.δ (1 : Fin 2) := by
    ext i
    rfl
  rw [hc, op_comp, W.diagram.map_comp]
  have hs := types_congr_hom (congrArg (fun q => q.app e) (mappingFibre.source_eq W x y)) z
  change (W.diagram.δ (1 : Fin 2)).app e ((mappingFibre.fst W x y).app e z) =
    (SSet.yonedaEquiv.symm x).app e ((mappingFibre.snd W x y).app e z) at hs
  change (W.diagram.map (SimplexCategory.const e.unop (SimplexCategory.mk 0) 0).op).app e
    ((W.diagram.δ (1 : Fin 2)).app e ((mappingFibre.fst W x y).app e z)) = _
  rw [hs]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The target end of the original interval cylinder is the original prescribed target point. -/
theorem mappingFibreDiagonalCylinder_one (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.ι₁ ≫ mappingFibreDiagonalCylinder W x y = mappingFibreDiagonalTarget W x y := by
  apply NatTrans.ext
  funext e
  apply ConcreteCategory.hom_ext
  intro z
  change (W.diagram.map (SSet.stdSimplex.objEquiv
    ((SSet.ι₁ (X := mappingFibre W x y)).app e z).2).op).app e
      ((mappingFibre.fst W x y).app e z) = _
  have he : SSet.stdSimplex.objEquiv
      ((SSet.ι₁ (X := mappingFibre W x y)).app e z).2 =
      SimplexCategory.const e.unop (SimplexCategory.mk 1) 1 := rfl
  rw [he]
  have hc : SimplexCategory.const e.unop (SimplexCategory.mk 1) 1 =
      SimplexCategory.const e.unop (SimplexCategory.mk 0) 0 ≫ SimplexCategory.δ (0 : Fin 2) := by
    ext i
    rfl
  rw [hc, op_comp, W.diagram.map_comp]
  have hs := types_congr_hom (congrArg (fun q => q.app e) (mappingFibre.target_eq W x y)) z
  change (W.diagram.δ (0 : Fin 2)).app e ((mappingFibre.fst W x y).app e z) =
    (SSet.yonedaEquiv.symm y).app e ((mappingFibre.snd W x y).app e z) at hs
  change (W.diagram.map (SimplexCategory.const e.unop (SimplexCategory.mk 0) 0).op).app e
    ((W.diagram.δ (0 : Fin 2)).app e ((mappingFibre.fst W x y).app e z)) = _
  rw [hs]
  rfl

end SimplicialSpace.LeftDecalageObject
