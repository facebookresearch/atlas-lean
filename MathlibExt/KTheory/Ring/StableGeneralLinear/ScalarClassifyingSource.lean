/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ScalarMap
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpaceFundamentalGroup

/-!
# The original BGL scalar source map in independent ring universes

The coefficient map is the existing stable scalar map. Its opposite
one-object functor is realized between the original BGL spaces through the
existing category-lift realization homeomorphisms. The original marked
vertex is preserved. No plus map, inverse or naturality square defines it.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe uR uS

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]

/-- The actual opposite stable coefficient functor, with independent rings. -/
public def classifyingCategoryScalarMap (f : R →+* S) :
    ClassifyingCategory R ⥤ ClassifyingCategory S :=
  SingleObj.mapHom _ _ (MonoidHom.op (scalarMap f))

private theorem classifyingCategoryScalarMap_map_computed
    (f : R →+* S) {X Y : ClassifyingCategory R} (g : X ⟶ Y) :
    (classifyingCategoryScalarMap f).map g =
      MulOpposite.op (scalarMap f (MulOpposite.unop g)) := rfl

/-- Every original category arrow maps by the actual opposite scalar map. -/
public theorem classifyingCategoryScalarMap_map
    (f : R →+* S) {X Y : ClassifyingCategory R} (g : X ⟶ Y) :
    (classifyingCategoryScalarMap f).map g =
      MulOpposite.op (scalarMap f (MulOpposite.unop g)) :=
  classifyingCategoryScalarMap_map_computed f g

/-- The actual continuous BGL source map of the original scalar functor. -/
public def ordinaryBGLScalarMap (f : R →+* S) : C(ordinaryBGL R, ordinaryBGL S) :=
  CategoryTheory.realizedNerveFunctorMap.{0, uR, 0, uS} (classifyingCategoryScalarMap f)

private theorem ordinaryBGLScalarMap_point_computed (f : R →+* S) :
    ordinaryBGLScalarMap f (ordinaryBGLBasepoint R) = ordinaryBGLBasepoint S := by
  change CategoryTheory.realizedNerveFunctorMap (classifyingCategoryScalarMap f)
      (SSet.realizedVertex (X := nerve (ClassifyingCategory R))
        (ComposableArrows.mk₀ (SingleObj.star (StableGL R)ᵐᵒᵖ))) =
    SSet.realizedVertex (X := nerve (ClassifyingCategory S))
      (ComposableArrows.mk₀ (SingleObj.star (StableGL S)ᵐᵒᵖ))
  exact (CategoryTheory.realizedNerveFunctorMap_vertex (classifyingCategoryScalarMap f)
    (SingleObj.star (StableGL R)ᵐᵒᵖ)).trans
      (congrArg (fun z : ClassifyingCategory S =>
        SSet.realizedVertex (X := nerve (ClassifyingCategory S)) (ComposableArrows.mk₀ z))
        (Subsingleton.elim _ _))

/-- The original source point maps to the original target point. -/
public theorem ordinaryBGLScalarMap_point (f : R →+* S) :
    ordinaryBGLScalarMap f (ordinaryBGLBasepoint R) = ordinaryBGLBasepoint S :=
  ordinaryBGLScalarMap_point_computed f

end AlgebraicKTheory.StableGL

end


noncomputable section

universe uR uS

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]

private theorem ordinaryBGLScalarMap_eq_realizedFunctorMap_computed (f : R →+* S) :
    ordinaryBGLScalarMap f =
      CategoryTheory.realizedNerveFunctorMap (classifyingCategoryScalarMap f) := by
  rfl

/-- The whole original BGL scalar map keeps the SAME mixed-world realization
of its actual coefficient functor, in the original independent Semiring worlds. -/
public theorem ordinaryBGLScalarMap_eq_realizedFunctorMap (f : R →+* S) :
    ordinaryBGLScalarMap f =
      CategoryTheory.realizedNerveFunctorMap (classifyingCategoryScalarMap f) :=
  ordinaryBGLScalarMap_eq_realizedFunctorMap_computed f

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory

universe uR uS

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]

private theorem classifyingCategoryScalarMapStarComputed (f : R →+* S) :
    (classifyingCategoryScalarMap f).obj (SingleObj.star (StableGL R)ᵐᵒᵖ) =
      SingleObj.star (StableGL S)ᵐᵒᵖ :=
  Subsingleton.elim _ _

/-- The SAME original opposite scalar functor sends the original source star
    to the original target star in the two independent Semiring universes. -/
public theorem classifyingCategoryScalarMap_star (f : R →+* S) :
    (classifyingCategoryScalarMap f).obj (SingleObj.star (StableGL R)ᵐᵒᵖ) =
      SingleObj.star (StableGL S)ᵐᵒᵖ :=
  classifyingCategoryScalarMapStarComputed f

end AlgebraicKTheory.StableGL

end
