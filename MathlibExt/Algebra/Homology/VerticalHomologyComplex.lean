/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Complexes formed by vertical bicomplex homology

For a category with zero morphisms and chosen homology, take a
bicomplex of shapes `c₁,c₂` on independent index types. Fixing vertical
degree `q`, its row homology objects form a horizontal `c₁`-shaped
complex. The differential is the homology map of the horizontal row
map, and bicomplex maps induce componentwise homology maps.
In an abelian category, first-quadrant chain bicomplexes specialize
this construction to a nonnegative horizontal chain complex.
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

/-- Let `C` be a category with zero morphisms and chosen homology,
and `B` a bicomplex of independent shapes `c₁,c₂` on index types
`I₁,I₂`. For fixed vertical `q : I₂`, the row homology objects
`H_q(B_p)` form a horizontal homological complex of shape `c₁`. -/
noncomputable def verticalHomologyComplexOfShapes
    (q : I₂) : HomologicalComplex C c₁ :=
  ((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).obj B

/-- Let `C` be a category with zero morphisms and chosen homology,
and `B` a bicomplex of independent shapes `c₁,c₂` on index types
`I₁,I₂`. The degree-`p` object of the fixed-`q` vertical-homology
complex is `H_q(B_p)`. -/
@[simp]
theorem verticalHomologyComplexOfShapes_X (p : I₁) (q : I₂) :
    (B.verticalHomologyComplexOfShapes q).X p = (B.X p).homology q :=
  rfl

/-- Let `C` be a category with zero morphisms and chosen homology,
and `B` a bicomplex of independent shapes `c₁,c₂` on index types
`I₁,I₂`. The horizontal differential from `p` to `p′` in fixed
vertical degree `q` is `H_q(B.d(p,p′))`. -/
@[simp]
theorem verticalHomologyComplexOfShapes_d (p p' : I₁) (q : I₂) :
    (B.verticalHomologyComplexOfShapes q).d p p' =
      HomologicalComplex.homologyMap (B.d p p') q :=
  rfl

variable {K L M : HomologicalComplex₂ C c₁ c₂}

/-- Let `C` have zero morphisms and chosen homology, and
`f : K → L` be a map of bicomplexes of independent shapes `c₁,c₂`.
For `q : I₂`, row homology gives a map between their horizontal
vertical-homology complexes. -/
noncomputable def verticalHomologyComplexMapOfShapes (f : K ⟶ L) (q : I₂) :
    K.verticalHomologyComplexOfShapes q ⟶
      L.verticalHomologyComplexOfShapes q :=
  ((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).map f

/-- Let `C` have zero morphisms and chosen homology and
`f : K → L` be a bicomplex map of shapes `c₁,c₂`. The degree-`p`
component in fixed vertical degree `q` is `H_q(f_p)`. -/
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

/-!
## First-quadrant chain bicomplexes

In an abelian category, fixing `q ∈ ℕ` in a bicomplex with both
shapes `down ℕ` gives a nonnegative chain complex in the horizontal
index. Its degree-`p` term is row homology `H_q(B_p)`, with the
horizontal row maps inducing the chain differential.
-/

section FirstQuadrant

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Let `C` be abelian and `B` a first-quadrant chain bicomplex,
with both index shapes `down ℕ`. For fixed vertical degree `q`, its row homology objects
form a nonnegative horizontal chain complex. -/
noncomputable def verticalHomologyComplex (q : ℕ) : ChainComplex C ℕ :=
  B.verticalHomologyComplexOfShapes q

/-- Let `C` be abelian and `B` a first-quadrant chain bicomplex,
with both index shapes `down ℕ`. The degree-`p` term of the fixed-`q` vertical-homology
chain complex is `H_q(B_p)`. -/
@[simp]
theorem verticalHomologyComplex_X (p q : ℕ) :
    (B.verticalHomologyComplex q).X p = (B.X p).homology q :=
  rfl

/-- Let `C` be abelian and `B` a first-quadrant chain bicomplex,
with both index shapes `down ℕ`. The horizontal differential from `p` to `p′` in fixed
vertical degree `q` is the homology map `H_q(B.d(p,p′))`. -/
@[simp]
theorem verticalHomologyComplex_d (p p' q : ℕ) :
    (B.verticalHomologyComplex q).d p p' =
      HomologicalComplex.homologyMap (B.d p p') q :=
  rfl

variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- In an abelian category `C`, a map `f : K → L` of first-quadrant
chain bicomplexes induces, for each vertical degree `q`, a map
between their horizontal vertical-homology chain complexes. -/
noncomputable def verticalHomologyComplexMap (f : K ⟶ L) (q : ℕ) :
    K.verticalHomologyComplex q ⟶ L.verticalHomologyComplex q :=
  verticalHomologyComplexMapOfShapes f q

/-- In an abelian category `C`, for a first-quadrant bicomplex map
`f : K → L`, its induced horizontal chain map in vertical degree
`q` has degree-`p` component `H_q(f_p)`. -/
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
