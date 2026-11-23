/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.BlockSumClassifying
public import MathlibExt.CategoryTheory.ClassifyingSpace.CGWHWeakHSpace
public import MathlibExt.Topology.Category.CGWH.RealizedProductPoint

/-!
# The original native BGL multiplication and its two axis maps

The multiplication is the realization of the original opposite
block-sum functor. Its left and right axis maps are the original second
and first block embeddings. These are whole map equations, not unit
natural isomorphisms on BGL. The scalar is the original arbitrary ring.
-/

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory

universe u

namespace AlgebraicKTheory.StableGL

private theorem categoricalLeftBlockFunctor_eq (R : Type u) [Ring R] :
    CategoryTheory.categoricalLeftUnitFunctor (ClassifyingCategory R)
      (blockSumClassifyingFunctor R) (SingleObj.star ((StableGL R)ᵐᵒᵖ)) =
        blockSumRightClassifyingFunctor R := by
  apply Functor.hext (fun _ => Subsingleton.elim _ _)
  intro x y g
  apply heq_of_eq
  rw [CategoryTheory.categoricalLeftUnitFunctor, Functor.comp_map,
    blockSumClassifyingFunctor_map, blockSumRightClassifyingFunctor_map,
    blockSumRightHom_apply]; rfl

private theorem categoricalRightBlockFunctor_eq (R : Type u) [Ring R] :
    CategoryTheory.categoricalRightUnitFunctor (ClassifyingCategory R)
      (blockSumClassifyingFunctor R) (SingleObj.star ((StableGL R)ᵐᵒᵖ)) =
        blockSumLeftClassifyingFunctor R := by
  apply Functor.hext (fun _ => Subsingleton.elim _ _)
  intro x y g
  apply heq_of_eq
  rw [CategoryTheory.categoricalRightUnitFunctor, Functor.comp_map,
    blockSumClassifyingFunctor_map, blockSumLeftClassifyingFunctor_map,
    blockSumLeftHom_apply]; rfl

/-- The actual full native product multiplication from original block sum. -/
public abbrev nativeBGLBlockSum (R : Type u) [Ring R] :
    BGL.{u} R ⨯ BGL.{u} R ⟶ BGL.{u} R :=
  CategoryTheory.categoricalClassifyingSpaceMul.{u, 0, u}
    (ClassifyingCategory R) (blockSumClassifyingFunctor R)

/-- The pair of original BGL vertices maps to the same original vertex. -/
public theorem nativeBGLBlockSum_point (R : Type u) [Ring R] :
    nativeBGLBlockSum R (CGWH.tensorMk (BGLBasepoint.{u} R) (BGLBasepoint.{u} R)) =
      BGLBasepoint.{u} R := by
  rw [CGWH.tensorMk_eq_prodPoint]
  exact CategoryTheory.categoricalClassifyingSpaceMul_prodPoint
    (ClassifyingCategory R) (blockSumClassifyingFunctor R)
    (SingleObj.star ((StableGL R)ᵐᵒᵖ)) (SingleObj.star ((StableGL R)ᵐᵒᵖ))

/-- The left axis is the ORIGINAL second block map on the whole BGL. -/
public theorem nativeBGLBlockSum_leftUnitMap (R : Type u) [Ring R] :
    CGWH.hspaceLeftUnitMap (BGL.{u} R) (nativeBGLBlockSum R) (BGLBasepoint R) =
      blockSumRightBGLMap R := by
  exact (CategoryTheory.categoricalClassifyingSpaceMul_leftUnitMap
    (ClassifyingCategory R) (blockSumClassifyingFunctor R)
    (SingleObj.star ((StableGL R)ᵐᵒᵖ))).trans
      (congrArg (fun F : ClassifyingCategory R ⥤ ClassifyingCategory R =>
        CategoryTheory.classifyingSpaceCGWH.{u, u, 0}.map F.toCatHom)
          (categoricalLeftBlockFunctor_eq R))

/-- The right axis is the ORIGINAL first block map on the whole BGL. -/
public theorem nativeBGLBlockSum_rightUnitMap (R : Type u) [Ring R] :
    CGWH.hspaceRightUnitMap (BGL.{u} R) (nativeBGLBlockSum R) (BGLBasepoint R) =
      blockSumLeftBGLMap R := by
  exact (CategoryTheory.categoricalClassifyingSpaceMul_rightUnitMap
    (ClassifyingCategory R) (blockSumClassifyingFunctor R)
    (SingleObj.star ((StableGL R)ᵐᵒᵖ))).trans
      (congrArg (fun F : ClassifyingCategory R ⥤ ClassifyingCategory R =>
        CategoryTheory.classifyingSpaceCGWH.{u, u, 0}.map F.toCatHom)
          (categoricalRightBlockFunctor_eq R))

end AlgebraicKTheory.StableGL

end
