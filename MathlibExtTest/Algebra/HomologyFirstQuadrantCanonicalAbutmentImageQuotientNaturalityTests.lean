/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentImageQuotientNaturality

/-! # Tests for canonical-abutment image-quotient naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCanonicalAbutmentImageQuotientNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCanonicalAbutmentImageQuotientMapOfBicomplex
#check horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_π
#check horizontalCanonicalAbutmentImageQuotientIso_naturality

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentImageQuotientIso L p q).hom =
      (horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
        horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q :=
  horizontalCanonicalAbutmentImageQuotientIso_naturality f p q

example (f : K ⟶ L) (p q : ℕ) :
    cokernel.π (CategoryTheory.imageCompMap
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap K p q)) ≫
        horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q =
      horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q ≫
        cokernel.π (CategoryTheory.imageCompMap
          (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) :=
  horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_π f p q

-- Corner and one-sided zero-index boundaries.
example (f : K ⟶ L) :=
  horizontalCanonicalAbutmentImageQuotientIso_naturality f 0 0

example (f : K ⟶ L) (q : ℕ) :=
  horizontalCanonicalAbutmentImageQuotientIso_naturality f 0 q

example (f : K ⟶ L) (p : ℕ) :=
  horizontalCanonicalAbutmentImageQuotientIso_naturality f p 0

-- Identity and composite bicomplex maps.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :=
  horizontalCanonicalAbutmentImageQuotientIso_naturality (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :=
  horizontalCanonicalAbutmentImageQuotientIso_naturality (f ≫ g) p q

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

example
    (K : HomologicalComplex₂ ZeroModuleCat (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :=
  horizontalCanonicalAbutmentImageQuotientIso_naturality (𝟙 K) 0 0

#print axioms horizontalCanonicalAbutmentImageQuotientMapOfBicomplex
#print axioms horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_π
#print axioms horizontalCanonicalAbutmentImageQuotientIso_naturality

end HomologicalComplex₂.FirstQuadrantCanonicalAbutmentImageQuotientNaturalityTests

end
