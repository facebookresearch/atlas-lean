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

public import MathlibExt.Algebra.Homology.VerticalHomologyComplex

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Limits

universe v u u₁ u₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

-- The original first-quadrant API has exactly the two category universes.
#check @verticalHomologyComplex.{v, u}
#check @verticalHomologyComplex_X.{v, u}
#check @verticalHomologyComplex_d.{v, u}
#check @verticalHomologyComplexMap.{v, u}
#check @verticalHomologyComplexMap_f.{v, u}
#check @verticalHomologyComplexMap_id.{v, u}
#check @verticalHomologyComplexMap_comp.{v, u}

example (q : ℕ) : ChainComplex C ℕ :=
  B.verticalHomologyComplex q

example (p q : ℕ) :
    (B.verticalHomologyComplex q).X p = (B.X p).homology q := by
  simp

example (p p' q : ℕ) :
    (B.verticalHomologyComplex q).d p p' =
      HomologicalComplex.homologyMap (B.d p p') q := by
  simp

variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

example (f : K ⟶ L) (p q : ℕ) :
    (verticalHomologyComplexMap f q).f p =
      HomologicalComplex.homologyMap (f.f p) q := by
  simp

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (q : ℕ) :
    verticalHomologyComplexMap (𝟙 K) q = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (q : ℕ) :
    verticalHomologyComplexMap (f ≫ g) q =
      verticalHomologyComplexMap f q ≫ verticalHomologyComplexMap g q := by
  simp

section GenericShapes

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
  [CategoryWithHomology D]
variable {I₁ : Type u₁} {I₂ : Type u₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

example (K : HomologicalComplex₂ D c₁ c₂) (q : I₂) :
    HomologicalComplex D c₁ :=
  K.verticalHomologyComplexOfShapes q

end GenericShapes

section MixedShapes

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
  [CategoryWithHomology D]
variable {K L M : HomologicalComplex₂ D (ComplexShape.up ℤ)
  (ComplexShape.down ℕ)}

example (K : HomologicalComplex₂ D (ComplexShape.up ℤ)
    (ComplexShape.down ℕ)) (q : ℕ) : CochainComplex D ℤ :=
  K.verticalHomologyComplexOfShapes q

example (f : K ⟶ L) (q : ℕ) :
    (verticalHomologyComplexMapOfShapes f q).f (-2 : ℤ) =
      HomologicalComplex.homologyMap (f.f (-2 : ℤ)) q := by
  simp

example (K : HomologicalComplex₂ D (ComplexShape.up ℤ)
    (ComplexShape.down ℕ)) (q : ℕ) :
    (verticalHomologyComplexMapOfShapes (𝟙 K) q).f (-2 : ℤ) = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (q : ℕ) :
    verticalHomologyComplexMapOfShapes (f ≫ g) q =
      verticalHomologyComplexMapOfShapes f q ≫
        verticalHomologyComplexMapOfShapes g q := by
  simp

example (f : K ⟶ L) (q : ℕ) :
    (verticalHomologyComplexMapOfShapes f q).f (-1 : ℤ) ≫
        (L.verticalHomologyComplexOfShapes q).d (-1 : ℤ) (-2 : ℤ) =
      (K.verticalHomologyComplexOfShapes q).d (-1 : ℤ) (-2 : ℤ) ≫
        (verticalHomologyComplexMapOfShapes f q).f (-2 : ℤ) := by
  simpa using
    (verticalHomologyComplexMapOfShapes f q).comm (-1 : ℤ) (-2 : ℤ)

end MixedShapes

end HomologicalComplex₂

end
