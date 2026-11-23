/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpace
public import Mathlib.CategoryTheory.Grothendieck

/-!
# The categorical telescope of finite general-linear classifying spaces

For a semiring `R`, this file packages the finite-stage maps
`BGLₙ(R) → BGL(R)` before realization.  The finite one-object categories form a
diagram indexed by `ℕ`; their Grothendieck construction is the categorical
mapping telescope.  Its fiber inclusions realize to canonical maps from each
finite classifying space.

The compatible finite-to-stable functors are bundled as a cocone.  A
transition in the indexing category also gives the canonical natural
transformation between the corresponding fiber inclusions.

This file makes no homotopy-colimit, homology-localization, weak-equivalence,
or plus-construction claim.  Those are the genuinely homotopical steps in the
Grayson--Quillen comparison.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- The finite-to-stable classifying-category maps as a cocone. -/
noncomputable def finiteToStableCocone
    (R : Type u) [Semiring R] :
    Cocone (finiteClassifyingCategoryDiagram R) where
  pt := Cat.of (ClassifyingCategory R)
  ι :=
    { app := fun n => finiteToStableCategoryMap R n
      naturality := fun {n m} f => by
        change (finiteClassifyingCategoryDiagram R).map f ≫
            finiteToStableCategoryMap R m =
          finiteToStableCategoryMap R n ≫ 𝟙 _
        rw [Category.comp_id]
        exact finiteToStableCategoryMap_naturality R f }

@[simp]
theorem finiteToStableCocone_ι_app
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteToStableCocone R).ι.app n =
      finiteToStableCategoryMap R n :=
  rfl

/-- The categorical mapping telescope of the finite stable-`GL`
one-object categories. -/
abbrev FiniteBGLTelescopeCategory
    (R : Type u) [Semiring R] :=
  Grothendieck (finiteClassifyingCategoryDiagram R)

/-- The inclusion of the `n`th finite classifying category into the
categorical telescope. -/
noncomputable def finiteBGLTelescopeFiberInclusion
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteClassifyingCategoryDiagram R).obj n ⥤
      FiniteBGLTelescopeCategory R :=
  Grothendieck.ι (finiteClassifyingCategoryDiagram R) n

@[simp]
theorem finiteBGLTelescopeFiberInclusion_obj_base
    (R : Type u) [Semiring R] (n : ℕ)
    (X : (finiteClassifyingCategoryDiagram R).obj n) :
    ((finiteBGLTelescopeFiberInclusion R n).obj X).base = n :=
  rfl

/-- An indexing transition gives the canonical transformation from the
earlier fiber inclusion to the later one after stabilization. -/
noncomputable def finiteBGLTelescopeFiberTransition
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    finiteBGLTelescopeFiberInclusion R n ⟶
      ((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        finiteBGLTelescopeFiberInclusion R m :=
  Grothendieck.ιNatTrans
    (F := finiteClassifyingCategoryDiagram R) f

/-- Native CGWH realization of the finite-`GL` categorical telescope. -/
noncomputable def finiteBGLTelescope
    (R : Type u) [Semiring R] : CGWH.{w, u} :=
  CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.obj
    (Cat.of (FiniteBGLTelescopeCategory R))

/-- The distinguished object at the zeroth finite stage. -/
abbrev finiteBGLTelescopeBaseObject
    (R : Type u) [Semiring R] :
    FiniteBGLTelescopeCategory R :=
  ⟨0, SingleObj.star
    (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ⟩

/-- The categorical telescope with the zeroth-stage object as basepoint. -/
noncomputable def pointedFiniteBGLTelescope
    (R : Type u) [Semiring R] : PointedCGWH.{w, u} :=
  CategoryTheory.classifyingSpaceCGWHPointed.{w}
    (finiteBGLTelescopeBaseObject R)

/-- The map from `BGLₙ(R)` into the realized categorical telescope. -/
noncomputable def finiteBGLToTelescope
    (R : Type u) [Semiring R] (n : ℕ) :
    FiniteBGL.{w} R n ⟶ finiteBGLTelescope.{w} R :=
  CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
    (finiteBGLTelescopeFiberInclusion R n).toCatHom

/-- The zeroth-stage map into the telescope, strictly pointed at the selected
zeroth-stage object. -/
noncomputable def pointedFiniteBGLZeroToTelescope
    (R : Type u) [Semiring R] :
    pointedFiniteBGL.{w} R 0 ⟶ pointedFiniteBGLTelescope.{w} R :=
  Under.homMk (finiteBGLToTelescope.{w} R 0) (by
    exact CategoryTheory.classifyingSpaceCGWH_basepointMap_naturality
      (finiteBGLTelescopeFiberInclusion R 0)
      (SingleObj.star
        (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ))

end StableGL
end AlgebraicKTheory

end
