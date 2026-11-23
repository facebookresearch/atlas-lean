/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMapReindex
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridStageProjection

/-!
# Exact-functor maps on Quillen Stage-grid nerves and diagonals

At common source and target universes, the degreewise exact-functor map on
Stage-grid lifts assembles into a map of outer simplicial nerves.  The same is
true for retained discrete Quillen simplices and outer-edgewise weak Stages.
Both grid projections form strict naturality squares, and applying the
simplicial diagonal functor gives the corresponding diagonal maps and squares.

This file constructs no comparison with the ordinary Quillen nerve or the
ordinary weak-Stage diagonal, realization map, grid-zero path, weakly pointed
or loop map, weak equivalence, group comparison, spectrum map, or Q/S
equivalence.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance quillenStageGridMapNerveWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

local instance quillenStageGridMapNerveWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- Exact-functor map on the outer simplicial nerve of Stage-grid lifts. -/
noncomputable def quillenStageGridNerveMap :
    quillenStageGridNerve C ⟶ quillenStageGridNerve D where
  app a := CategoryTheory.nerveMap
    (quillenStageGridLiftMap F a.unop)
  naturality {a b} f := by
    change CategoryTheory.nerveMap
          (reindexQuillenStageGridLift (C := C) f.unop) ≫
        CategoryTheory.nerveMap
          (quillenStageGridLiftMap F b.unop) =
      CategoryTheory.nerveMap
          (quillenStageGridLiftMap F a.unop) ≫
        CategoryTheory.nerveMap
          (reindexQuillenStageGridLift (C := D) f.unop)
    rw [CategoryTheory.nerveMap_comp, CategoryTheory.nerveMap_comp,
      quillenStageGridLiftMap_reindex]

@[simp]
theorem quillenStageGridNerveMap_app (a : SimplexCategoryᵒᵖ) :
    (quillenStageGridNerveMap F).app a =
      CategoryTheory.nerveMap (quillenStageGridLiftMap F a.unop) :=
  rfl

/-- Exact-functor map on the outer simplicial nerve of retained discrete
Quillen simplices. -/
noncomputable def quillenQSimplexDiscreteNerveMap :
    quillenQSimplexDiscreteNerve C ⟶ quillenQSimplexDiscreteNerve D where
  app a := CategoryTheory.nerveMap
    (quillenQSimplexDiscreteMap F a.unop)
  naturality {a b} f := by
    change CategoryTheory.nerveMap
          (quillenQSimplexDiscreteReindex (C := C) f.unop) ≫
        CategoryTheory.nerveMap
          (quillenQSimplexDiscreteMap F b.unop) =
      CategoryTheory.nerveMap
          (quillenQSimplexDiscreteMap F a.unop) ≫
        CategoryTheory.nerveMap
          (quillenQSimplexDiscreteReindex (C := D) f.unop)
    rw [CategoryTheory.nerveMap_comp, CategoryTheory.nerveMap_comp,
      quillenQSimplexDiscreteMap_reindex]

@[simp]
theorem quillenQSimplexDiscreteNerveMap_app (a : SimplexCategoryᵒᵖ) :
    (quillenQSimplexDiscreteNerveMap F).app a =
      CategoryTheory.nerveMap (quillenQSimplexDiscreteMap F a.unop) :=
  rfl

/-- Exact-functor map on the outer-edgewise weak-Stage nerve. -/
noncomputable def edgewiseStageWeakNerveMap :
    edgewiseStageWeakNerve C ⟶ edgewiseStageWeakNerve D where
  app a := CategoryTheory.nerveMap
    (mapStageWeak C D F (edgewiseQ.obj a.unop).len)
  naturality {a b} f := by
    change CategoryTheory.nerveMap
          (reindexStageWeak C (edgewiseQ.map f.unop)) ≫
        CategoryTheory.nerveMap
          (mapStageWeak C D F (edgewiseQ.obj b.unop).len) =
      CategoryTheory.nerveMap
          (mapStageWeak C D F (edgewiseQ.obj a.unop).len) ≫
        CategoryTheory.nerveMap
          (reindexStageWeak D (edgewiseQ.map f.unop))
    rw [CategoryTheory.nerveMap_comp, CategoryTheory.nerveMap_comp,
      mapStageWeak_reindex]

@[simp]
theorem edgewiseStageWeakNerveMap_app (a : SimplexCategoryᵒᵖ) :
    (edgewiseStageWeakNerveMap F).app a =
      CategoryTheory.nerveMap
        (mapStageWeak C D F (edgewiseQ.obj a.unop).len) :=
  rfl

/-- Naturality of the retained-Q projection at the level of outer
simplicial nerves. -/
theorem quillenStageGridQProjectionNerve_naturality :
    quillenStageGridNerveMap F ≫
        quillenStageGridQProjectionNerve (C := D) =
      quillenStageGridQProjectionNerve (C := C) ≫
        quillenQSimplexDiscreteNerveMap F := by
  apply NatTrans.ext
  funext a
  change CategoryTheory.nerveMap
        (quillenStageGridLiftMap F a.unop) ≫
      CategoryTheory.nerveMap
        (quillenStageGridQProjection D a.unop) =
    CategoryTheory.nerveMap
        (quillenStageGridQProjection C a.unop) ≫
      CategoryTheory.nerveMap
        (quillenQSimplexDiscreteMap F a.unop)
  rw [CategoryTheory.nerveMap_comp, CategoryTheory.nerveMap_comp,
    quillenStageGridLiftMap_qProjection]

/-- Naturality of the material-Stage projection at the level of outer
simplicial nerves. -/
theorem quillenStageGridStageProjectionNerve_naturality :
    quillenStageGridNerveMap F ≫
        quillenStageGridStageProjectionNerve (C := D) =
      quillenStageGridStageProjectionNerve (C := C) ≫
        edgewiseStageWeakNerveMap F := by
  apply NatTrans.ext
  funext a
  change CategoryTheory.nerveMap
        (quillenStageGridLiftMap F a.unop) ≫
      CategoryTheory.nerveMapHomDown
        (quillenStageGridProjection D a.unop) =
    CategoryTheory.nerveMapHomDown
        (quillenStageGridProjection C a.unop) ≫
      CategoryTheory.nerveMap
        (mapStageWeak C D F (edgewiseQ.obj a.unop).len)
  rw [CategoryTheory.nerveMap_nerveMapHomDown_comp,
    CategoryTheory.nerveMapHomDown_nerveMap_comp,
    quillenStageGridLiftMap_gridProjection]

/-- Exact-functor map on the diagonal Stage-grid nerve. -/
noncomputable def quillenStageGridDiagonalMap :
    quillenStageGridDiagonal C ⟶ quillenStageGridDiagonal D :=
  SSet.simplicialDiagonalFunctor.map (quillenStageGridNerveMap F)

@[simp]
theorem quillenStageGridDiagonalMap_app (a : SimplexCategoryᵒᵖ) :
    (quillenStageGridDiagonalMap F).app a =
      ((quillenStageGridNerveMap F).app a).app a :=
  rfl

/-- Exact-functor map on the diagonal retained-Q discrete nerve. -/
noncomputable def quillenQSimplexDiscreteDiagonalMap :
    quillenQSimplexDiscreteDiagonal C ⟶
      quillenQSimplexDiscreteDiagonal D :=
  SSet.simplicialDiagonalFunctor.map
    (quillenQSimplexDiscreteNerveMap F)

@[simp]
theorem quillenQSimplexDiscreteDiagonalMap_app
    (a : SimplexCategoryᵒᵖ) :
    (quillenQSimplexDiscreteDiagonalMap F).app a =
      ((quillenQSimplexDiscreteNerveMap F).app a).app a :=
  rfl

/-- Exact-functor map on the outer-edgewise weak-Stage diagonal. -/
noncomputable def edgewiseStageWeakDiagonalMap :
    edgewiseStageWeakDiagonal C ⟶ edgewiseStageWeakDiagonal D :=
  SSet.simplicialDiagonalFunctor.map (edgewiseStageWeakNerveMap F)

@[simp]
theorem edgewiseStageWeakDiagonalMap_app (a : SimplexCategoryᵒᵖ) :
    (edgewiseStageWeakDiagonalMap F).app a =
      ((edgewiseStageWeakNerveMap F).app a).app a :=
  rfl

/-- Naturality of the retained-Q projection on simplicial diagonals. -/
theorem quillenStageGridQProjectionDiagonal_naturality :
    quillenStageGridDiagonalMap F ≫
        quillenStageGridQProjectionDiagonal (C := D) =
      quillenStageGridQProjectionDiagonal (C := C) ≫
        quillenQSimplexDiscreteDiagonalMap F := by
  simpa only [quillenStageGridDiagonalMap,
    quillenQSimplexDiscreteDiagonalMap,
    quillenStageGridQProjectionDiagonal, Functor.map_comp] using
    congrArg (fun k => SSet.simplicialDiagonalFunctor.map k)
      (quillenStageGridQProjectionNerve_naturality F)

/-- Naturality of the material-Stage projection on simplicial diagonals. -/
theorem quillenStageGridStageProjectionDiagonal_naturality :
    quillenStageGridDiagonalMap F ≫
        quillenStageGridStageProjectionDiagonal (C := D) =
      quillenStageGridStageProjectionDiagonal (C := C) ≫
        edgewiseStageWeakDiagonalMap F := by
  simpa only [quillenStageGridDiagonalMap,
    edgewiseStageWeakDiagonalMap,
    quillenStageGridStageProjectionDiagonal, Functor.map_comp] using
    congrArg (fun k => SSet.simplicialDiagonalFunctor.map k)
      (quillenStageGridStageProjectionNerve_naturality F)

end AlgebraicKTheory

end
