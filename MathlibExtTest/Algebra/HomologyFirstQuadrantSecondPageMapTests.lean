/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageMap

/-! # Tests for first-quadrant fixed-page maps -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace HomologicalComplex₂.FirstQuadrantSecondPageMapTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check verticalHomologyComplexMap
#check verticalHomologyComplexMap_f
#check verticalHomologyComplexMap_id
#check verticalHomologyComplexMap_comp
#check horizontalPageMapOfBicomplex
#check horizontalPageMapOfBicomplex_f
#check horizontalPageMapOfBicomplex_id
#check horizontalPageMapOfBicomplex_comp
#check isIso_horizontalPageMapOfBicomplex
#check horizontalSecondPageMapOfBicomplex
#check horizontalSecondPageMapOfBicomplex_id
#check horizontalSecondPageMapOfBicomplex_comp
#check isIso_horizontalSecondPageMapOfBicomplex
#check horizontalSecondPageXIso
#check horizontalSecondPageEMapOfBicomplex
#check horizontalSecondPageMapOfBicomplex_eq

example (f : K ⟶ L) (p q : ℕ) :
    (verticalHomologyComplexMap f q).f p =
      HomologicalComplex.homologyMap (f.f p) q := by
  simp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (q : ℕ) :
    verticalHomologyComplexMap (𝟙 K) q = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (q : ℕ) :
    verticalHomologyComplexMap (f ≫ g) q =
      verticalHomologyComplexMap f q ≫ verticalHomologyComplexMap g q := by
  simp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (r : ℤ) (hr : 1 ≤ r) :
    horizontalPageMapOfBicomplex (𝟙 K) r hr = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (r : ℤ) (hr : 1 ≤ r) :
    horizontalPageMapOfBicomplex (f ≫ g) r hr =
      horizontalPageMapOfBicomplex f r hr ≫
        horizontalPageMapOfBicomplex g r hr := by
  simp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex (𝟙 K) p q = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex (f ≫ g) p q =
      horizontalSecondPageMapOfBicomplex f p q ≫
        horizontalSecondPageMapOfBicomplex g p q := by
  simp

example (f : K ⟶ L) [IsIso f] (r : ℤ) (hr : 1 ≤ r) :
    IsIso (horizontalPageMapOfBicomplex f r hr) := by
  infer_instance

example (f : K ⟶ L) [IsIso f] (p q : ℕ) :
    IsIso (horizontalSecondPageMapOfBicomplex f p q) := by
  infer_instance

example (f : K ⟶ L) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex f p q =
      (horizontalSecondPageXIso K p q).hom ≫
        horizontalSecondPageEMapOfBicomplex f p q ≫
        (horizontalSecondPageXIso L p q).inv :=
  horizontalSecondPageMapOfBicomplex_eq f p q

/-- Boundary `p = 0`: page two uses the complete-filtration lower index `-2`. -/
example : horizontalSecondPageLowerIndex 0 = ((-2 : ℤ) : EInt) :=
  rfl

/-- Boundary `p = 1`: the lower filtration index is still negative. -/
example : horizontalSecondPageLowerIndex 1 = ((-1 : ℤ) : EInt) := by
  rfl

/-- Boundary `q = 0` for the page-two presentation. -/
example (f : K ⟶ L) (p : ℕ) :
    horizontalSecondPageMapOfBicomplex f p 0 =
      (horizontalSecondPageXIso K p 0).hom ≫
        horizontalSecondPageEMapOfBicomplex f p 0 ≫
        (horizontalSecondPageXIso L p 0).inv :=
  horizontalSecondPageMapOfBicomplex_eq f p 0

/-- Boundary `(p,q) = (0,0)`. -/
example (f : K ⟶ L) :
    horizontalSecondPageMapOfBicomplex f 0 0 =
      (horizontalSecondPageXIso K 0 0).hom ≫
        horizontalSecondPageEMapOfBicomplex f 0 0 ≫
        (horizontalSecondPageXIso L 0 0).inv :=
  horizontalSecondPageMapOfBicomplex_eq f 0 0

/-- Boundary case: identity maps of the zero bicomplex. -/
example (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex
        (𝟙 (0 : HomologicalComplex₂ C (ComplexShape.down ℕ)
          (ComplexShape.down ℕ))) p q =
      𝟙 _ :=
  horizontalSecondPageMapOfBicomplex_id
    (0 : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) p q

#print axioms verticalHomologyComplexMap
#print axioms verticalHomologyComplexMap_id
#print axioms verticalHomologyComplexMap_comp
#print axioms horizontalPageMapOfBicomplex
#print axioms horizontalPageMapOfBicomplex_id
#print axioms horizontalPageMapOfBicomplex_comp
#print axioms isIso_horizontalPageMapOfBicomplex
#print axioms horizontalSecondPageMapOfBicomplex
#print axioms isIso_horizontalSecondPageMapOfBicomplex
#print axioms horizontalSecondPageMapOfBicomplex_eq

end HomologicalComplex₂.FirstQuadrantSecondPageMapTests

end
