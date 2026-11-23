/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.BlockSum
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpaceFundamentalGroup
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The actual block-sum functor on stable general-linear classifying categories

The source is the product of the original opposite one-object categories.
The functor uses the actual stable block-sum homomorphism, with the original
opposite convention retained. Its nerve map preserves the canonical vertex
and takes normalized matrix loops to the normalized block-sum loop. No plus
extension, product equivalence or H-space operation is assumed here.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- The actual block-sum functor, on both original stable-GL factors. -/
public def blockSumClassifyingFunctor :
    (ClassifyingCategory R × ClassifyingCategory R) ⥤ ClassifyingCategory R where
  obj _ := SingleObj.star ((StableGL R)ᵐᵒᵖ)
  map g := MulOpposite.op
    (blockSumHom R (MulOpposite.unop g.1, MulOpposite.unop g.2))
  map_id x := by
    change MulOpposite.op (blockSumHom R (1, 1)) = (1 : (StableGL R)ᵐᵒᵖ)
    rw [blockSumHom_one]
    rfl
  map_comp f g := by
    apply MulOpposite.unop_injective
    change blockSumHom R
        (MulOpposite.unop f.1 * MulOpposite.unop g.1,
          MulOpposite.unop f.2 * MulOpposite.unop g.2) =
      blockSumHom R (MulOpposite.unop f.1, MulOpposite.unop f.2) *
        blockSumHom R (MulOpposite.unop g.1, MulOpposite.unop g.2)
    simpa only [Prod.mk_mul_mk] using
      (blockSumHom R).map_mul
        (MulOpposite.unop f.1, MulOpposite.unop f.2)
        (MulOpposite.unop g.1, MulOpposite.unop g.2)

private theorem blockSumClassifyingFunctor_obj_computed
    (x : ClassifyingCategory R × ClassifyingCategory R) :
    (blockSumClassifyingFunctor R).obj x = SingleObj.star ((StableGL R)ᵐᵒᵖ) := rfl

/-- Both source objects map to the actual canonical target object. -/
public theorem blockSumClassifyingFunctor_obj
    (x : ClassifyingCategory R × ClassifyingCategory R) :
    (blockSumClassifyingFunctor R).obj x = SingleObj.star ((StableGL R)ᵐᵒᵖ) :=
  blockSumClassifyingFunctor_obj_computed R x

private theorem blockSumClassifyingFunctor_map_computed
    {x y : ClassifyingCategory R × ClassifyingCategory R} (g : x ⟶ y) :
    (blockSumClassifyingFunctor R).map g = MulOpposite.op
      (blockSumHom R (MulOpposite.unop g.1, MulOpposite.unop g.2)) := rfl

/-- The functor's whole morphism map is the original stable block sum. -/
public theorem blockSumClassifyingFunctor_map
    {x y : ClassifyingCategory R × ClassifyingCategory R} (g : x ⟶ y) :
    (blockSumClassifyingFunctor R).map g = MulOpposite.op
      (blockSumHom R (MulOpposite.unop g.1, MulOpposite.unop g.2)) :=
  blockSumClassifyingFunctor_map_computed R g

/-- The actual nerve-level block-sum map from the classifying product category. -/
public def blockSumNerveMap :
    CategoryTheory.nerve (ClassifyingCategory R × ClassifyingCategory R) ⟶
      classifyingNerve R := CategoryTheory.nerveMap (blockSumClassifyingFunctor R)

/-- The canonical source vertex maps to the canonical stable-BGL vertex. -/
public theorem blockSumNerveMap_vertex :
    (blockSumNerveMap R).app (op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm
          (SingleObj.star ((StableGL R)ᵐᵒᵖ), SingleObj.star ((StableGL R)ᵐᵒᵖ))) =
      classifyingVertex R := by
  let e : (classifyingNerve R) _⦋0⦌ ≃ ClassifyingCategory R := CategoryTheory.nerveEquiv
  letI : Subsingleton ((classifyingNerve R) _⦋0⦌) := e.injective.subsingleton
  exact Subsingleton.elim _ _

/-- The deliberate opposite/inverse normalization is retained on matrix loops. -/
public theorem blockSumClassifyingFunctor_normalized_map (x y : StableGL R) :
    (blockSumClassifyingFunctor R).map
        (show (SingleObj.star ((StableGL R)ᵐᵒᵖ), SingleObj.star ((StableGL R)ᵐᵒᵖ)) ⟶
          (SingleObj.star ((StableGL R)ᵐᵒᵖ), SingleObj.star ((StableGL R)ᵐᵒᵖ)) from
            (MulOpposite.op x⁻¹, MulOpposite.op y⁻¹)) =
      MulOpposite.op (blockSumHom R (x, y))⁻¹ := by
  rw [blockSumClassifyingFunctor_map]
  change MulOpposite.op (blockSumHom R ((x, y)⁻¹)) =
    MulOpposite.op (blockSumHom R (x, y))⁻¹
  rw [map_inv]

/-- The actual first block functor, with the same opposite convention. -/
public def blockSumLeftClassifyingFunctor : ClassifyingCategory R ⥤ ClassifyingCategory R :=
  SingleObj.mapHom _ _ (MonoidHom.op (blockSumLeftHom R))

private theorem blockSumLeftClassifyingFunctor_map_computed
    {x y : ClassifyingCategory R} (g : x ⟶ y) :
    (blockSumLeftClassifyingFunctor R).map g =
      MulOpposite.op (blockSumLeftHom R (MulOpposite.unop g)) := rfl

/-- Its complete arrow formula is the first factor of the original block sum. -/
public theorem blockSumLeftClassifyingFunctor_map
    {x y : ClassifyingCategory R} (g : x ⟶ y) :
    (blockSumLeftClassifyingFunctor R).map g =
      MulOpposite.op (blockSumLeftHom R (MulOpposite.unop g)) :=
  blockSumLeftClassifyingFunctor_map_computed R g

/-- The actual second block functor. -/
public def blockSumRightClassifyingFunctor : ClassifyingCategory R ⥤ ClassifyingCategory R :=
  SingleObj.mapHom _ _ (MonoidHom.op (blockSumRightHom R))

private theorem blockSumRightClassifyingFunctor_map_computed
    {x y : ClassifyingCategory R} (g : x ⟶ y) :
    (blockSumRightClassifyingFunctor R).map g =
      MulOpposite.op (blockSumRightHom R (MulOpposite.unop g)) := rfl

/-- Its complete arrow formula is the second factor of the original block sum. -/
public theorem blockSumRightClassifyingFunctor_map
    {x y : ClassifyingCategory R} (g : x ⟶ y) :
    (blockSumRightClassifyingFunctor R).map g =
      MulOpposite.op (blockSumRightHom R (MulOpposite.unop g)) :=
  blockSumRightClassifyingFunctor_map_computed R g

universe w

/-- The ORIGINAL first block map on native stable BGL, obtained by
realizing its original one-object classifying functor. -/
public abbrev blockSumLeftBGLMap : BGL.{w} R ⟶ BGL.{w} R :=
  CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
    (blockSumLeftClassifyingFunctor R).toCatHom

/-- The ORIGINAL second block map on native stable BGL, with the same
original realization and unchanged scalar semiring. -/
public abbrev blockSumRightBGLMap : BGL.{w} R ⟶ BGL.{w} R :=
  CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
    (blockSumRightClassifyingFunctor R).toCatHom

/-- The ORIGINAL first block map fixes the actual stable BGL vertex. -/
public theorem blockSumLeftBGLMap_basepoint :
    blockSumLeftBGLMap R (BGLBasepoint.{w} R) = BGLBasepoint.{w} R :=
  CategoryTheory.classifyingSpaceCGWH_map_point
    (blockSumLeftClassifyingFunctor R) (SingleObj.star ((StableGL R)ᵐᵒᵖ))

/-- The ORIGINAL second block map fixes the same actual stable BGL vertex. -/
public theorem blockSumRightBGLMap_basepoint :
    blockSumRightBGLMap R (BGLBasepoint.{w} R) = BGLBasepoint.{w} R :=
  CategoryTheory.classifyingSpaceCGWH_map_point
    (blockSumRightClassifyingFunctor R) (SingleObj.star ((StableGL R)ᵐᵒᵖ))

end AlgebraicKTheory.StableGL

end
