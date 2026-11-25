/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Vertical homology complexes

This file packages the vertical homology objects of a bicomplex, in one fixed
vertical degree, as a horizontal homological complex. The shape-generic API is
provided by declarations ending in `OfShapes`. The original first-quadrant
API is retained as a thin specialization to `ℕ`-indexed chain bicomplexes.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Limits

universe v u u₁ u₂

namespace HomologicalComplex₂

section OfShapes

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [CategoryWithHomology C]
variable {I₁ : Type u₁} {I₂ : Type u₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

variable (B : HomologicalComplex₂ C c₁ c₂)

/-- The horizontal homological complex of vertical homology objects in fixed
vertical degree `q`. -/
noncomputable def verticalHomologyComplexOfShapes
    (q : I₂) : HomologicalComplex C c₁ :=
  ((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).obj B

/-- Objects of the vertical-homology complex are row homology objects. -/
@[simp]
theorem verticalHomologyComplexOfShapes_X (p : I₁) (q : I₂) :
    (B.verticalHomologyComplexOfShapes q).X p = (B.X p).homology q :=
  rfl

/-- Differentials of the vertical-homology complex are the induced homology
maps of the horizontal bicomplex maps. -/
@[simp]
theorem verticalHomologyComplexOfShapes_d (p p' : I₁) (q : I₂) :
    (B.verticalHomologyComplexOfShapes q).d p p' =
      HomologicalComplex.homologyMap (B.d p p') q :=
  rfl

variable {K L M : HomologicalComplex₂ C c₁ c₂}

/-- The map between vertical-homology complexes induced by a bicomplex map. -/
noncomputable def verticalHomologyComplexMapOfShapes (f : K ⟶ L) (q : I₂) :
    K.verticalHomologyComplexOfShapes q ⟶
      L.verticalHomologyComplexOfShapes q :=
  ((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).map f

/-- Components of the induced map between vertical-homology complexes. -/
@[simp]
theorem verticalHomologyComplexMapOfShapes_f
    (f : K ⟶ L) (p : I₁) (q : I₂) :
    (verticalHomologyComplexMapOfShapes f q).f p =
      HomologicalComplex.homologyMap (f.f p) q :=
  rfl

@[simp]
theorem verticalHomologyComplexMapOfShapes_id
    (K : HomologicalComplex₂ C c₁ c₂) (q : I₂) :
    verticalHomologyComplexMapOfShapes (𝟙 K) q = 𝟙 _ := by
  exact
    ((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).map_id K

@[reassoc, simp]
theorem verticalHomologyComplexMapOfShapes_comp
    (f : K ⟶ L) (g : L ⟶ M) (q : I₂) :
    verticalHomologyComplexMapOfShapes (f ≫ g) q =
      verticalHomologyComplexMapOfShapes f q ≫
        verticalHomologyComplexMapOfShapes g q := by
  exact
    ((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).map_comp f g

end OfShapes

/-! ## Original first-quadrant API

These declarations preserve the two-universe public signatures of the
original `ℕ × ℕ` API. They forward definitionally to the shape-generic
implementation above. -/

section FirstQuadrant

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The horizontal chain complex of vertical homology objects in fixed
vertical degree `q`. -/
noncomputable def verticalHomologyComplex (q : ℕ) : ChainComplex C ℕ :=
  B.verticalHomologyComplexOfShapes q

/-- Objects of the vertical-homology complex are row homology objects. -/
@[simp]
theorem verticalHomologyComplex_X (p q : ℕ) :
    (B.verticalHomologyComplex q).X p = (B.X p).homology q :=
  rfl

/-- Differentials of the vertical-homology complex are the induced homology
maps of the horizontal bicomplex maps. -/
@[simp]
theorem verticalHomologyComplex_d (p p' q : ℕ) :
    (B.verticalHomologyComplex q).d p p' =
      HomologicalComplex.homologyMap (B.d p p') q :=
  rfl

variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The map between vertical-homology complexes induced by a bicomplex map. -/
noncomputable def verticalHomologyComplexMap (f : K ⟶ L) (q : ℕ) :
    K.verticalHomologyComplex q ⟶ L.verticalHomologyComplex q :=
  verticalHomologyComplexMapOfShapes f q

/-- Components of the induced map between vertical-homology complexes. -/
@[simp]
theorem verticalHomologyComplexMap_f (f : K ⟶ L) (p q : ℕ) :
    (verticalHomologyComplexMap f q).f p =
      HomologicalComplex.homologyMap (f.f p) q :=
  rfl

@[simp]
theorem verticalHomologyComplexMap_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (q : ℕ) :
    verticalHomologyComplexMap (𝟙 K) q = 𝟙 _ := by
  exact verticalHomologyComplexMapOfShapes_id K q

@[reassoc, simp]
theorem verticalHomologyComplexMap_comp
    (f : K ⟶ L) (g : L ⟶ M) (q : ℕ) :
    verticalHomologyComplexMap (f ≫ g) q =
      verticalHomologyComplexMap f q ≫ verticalHomologyComplexMap g q := by
  exact verticalHomologyComplexMapOfShapes_comp f g q

end FirstQuadrant

end HomologicalComplex₂

end
