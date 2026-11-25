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
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCokernelNaturality

/-! # Tests for canonical-abutment cokernel naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCanonicalAbutmentCokernelNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex
#check horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex_π
#check horizontalCanonicalAbutmentCokernelIso_hom_fac
#check horizontalCanonicalAbutmentCokernelIso_naturality

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentCokernelIso L p q).hom =
      (horizontalCanonicalAbutmentCokernelIso K p q).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f p q :=
  horizontalCanonicalAbutmentCokernelIso_naturality f p q

example (f : K ⟶ L) (p q : ℕ) :
    cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q =
      ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + q : ℕ) : ℤ))).app
          (ComposableArrows.mk₁
            (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
        cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
          (horizontalCanonicalAbutmentBoundaryMap L p q)) :=
  horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex_π f p q

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        (horizontalCanonicalAbutmentCokernelIso K p q).hom =
      (horizontalCanonicalAbutmentCokernelSequence K p q).g :=
  horizontalCanonicalAbutmentCokernelIso_hom_fac K p q

-- Corner and one-sided zero-index boundaries.
example (f : K ⟶ L) :=
  horizontalCanonicalAbutmentCokernelIso_naturality f 0 0

example (f : K ⟶ L) (q : ℕ) :=
  horizontalCanonicalAbutmentCokernelIso_naturality f 0 q

example (f : K ⟶ L) (p : ℕ) :=
  horizontalCanonicalAbutmentCokernelIso_naturality f p 0

-- Identity bicomplex map.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :=
  horizontalCanonicalAbutmentCokernelIso_naturality (𝟙 K) p q

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

example
    (K : HomologicalComplex₂ ZeroModuleCat (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :=
  horizontalCanonicalAbutmentCokernelIso_naturality (𝟙 K) 0 0

#print axioms horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex
#print axioms horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex_π
#print axioms horizontalCanonicalAbutmentCokernelIso_hom_fac
#print axioms horizontalCanonicalAbutmentCokernelIso_naturality

end HomologicalComplex₂.FirstQuadrantCanonicalAbutmentCokernelNaturalityTests

end
