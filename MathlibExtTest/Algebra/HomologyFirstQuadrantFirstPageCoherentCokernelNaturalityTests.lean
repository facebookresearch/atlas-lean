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
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCoherentCokernelNaturality

/-! # Tests for coherent first-page cokernel naturality -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageCoherentCokernelNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFilteredTotalMapOfBicomplex_topProjection
#check horizontalNaturalDirectColumnProjectionComponent_naturality
#check horizontalNaturalDirectColumnProjectionMap_naturality
#check horizontalCompleteDirectColumnProjectionMap_eq_finite
#check horizontalCompleteDirectColumnProjectionMap_naturality
#check horizontalFirstPageCoherentMap_naturality_of_bicomplex
#check horizontalFirstPageCoherentCokernelMapOfBicomplex
#check horizontalFirstPageCoherentCokernelMapOfBicomplex_π
#check horizontalFirstPageCoherentCokernelIso_π_hom
#check
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex

example (f : K ⟶ L) (p q : ℕ) :
    horizontalFilteredTotalMapOfBicomplex f p (p + q) ≫
        horizontalFilteredTopProjection L p q =
      horizontalFilteredTopProjection K p q ≫ (f.f p).f q :=
  horizontalFilteredTotalMapOfBicomplex_topProjection f p q

example (f : K ⟶ L) (p q : ℕ) :
    (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat).f (-(p : ℤ) - q) ≫
        horizontalNaturalDirectColumnProjectionComponent L p q =
      horizontalNaturalDirectColumnProjectionComponent K p q ≫
        (horizontalDirectColumnCochainMap f p).f (-(p : ℤ) - q) :=
  horizontalNaturalDirectColumnProjectionComponent_naturality f p q

example (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap L p =
      horizontalNaturalDirectColumnProjectionMap K p ≫
        horizontalDirectColumnCochainMap f p :=
  horizontalNaturalDirectColumnProjectionMap_naturality f p

example (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
            (horizontalFirstPageUpperIndex p))
          ComplexShape.embeddingDownNat ≫
        horizontalCompleteDirectColumnProjectionMap L p =
      horizontalCompleteDirectColumnProjectionMap K p ≫
        horizontalDirectColumnCochainMap f p :=
  horizontalCompleteDirectColumnProjectionMap_naturality f p

example (f : K ⟶ L) (p : ℕ) :
    horizontalFirstPageCoherentMap K p ≫
        horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p =
      horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p ≫
        horizontalFirstPageCoherentMap L p :=
  horizontalFirstPageCoherentMap_naturality_of_bicomplex f p

example (f : K ⟶ L) (p : ℕ) :
    cokernel (horizontalFirstPageCoherentMap K p) ⟶
      cokernel (horizontalFirstPageCoherentMap L p) :=
  horizontalFirstPageCoherentCokernelMapOfBicomplex f p

example (f : K ⟶ L) (p : ℕ) :
    cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        horizontalFirstPageCoherentCokernelMapOfBicomplex f p =
      horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
        cokernel.π (horizontalFirstPageCoherentMap L p) :=
  horizontalFirstPageCoherentCokernelMapOfBicomplex_π f p

example (p : ℕ) :
    cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        (horizontalFirstPageCoherentCokernelIso K p).hom =
      horizontalCompleteDirectColumnProjectionMap K p :=
  horizontalFirstPageCoherentCokernelIso_π_hom K p

example (f : K ⟶ L) (p : ℕ) :
    horizontalFirstPageCoherentCokernelMapOfBicomplex f p ≫
        (horizontalFirstPageCoherentCokernelIso L p).hom =
      (horizontalFirstPageCoherentCokernelIso K p).hom ≫
        horizontalDirectColumnCochainMap f p :=
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
    f p

example (f : K ⟶ L) (p : ℕ) :
    horizontalFilteredTotalMapOfBicomplex f p p ≫
        horizontalFilteredTopProjection L p 0 =
      horizontalFilteredTopProjection K p 0 ≫ (f.f p).f 0 := by
  simpa using
    horizontalFilteredTotalMapOfBicomplex_topProjection f p 0

example (f : K ⟶ L) :
    (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f 0)
          ComplexShape.embeddingDownNat).f 0 ≫
        horizontalNaturalDirectColumnProjectionComponent L 0 0 =
      horizontalNaturalDirectColumnProjectionComponent K 0 0 ≫
        (horizontalDirectColumnCochainMap f 0).f 0 := by
  simpa using
    horizontalNaturalDirectColumnProjectionComponent_naturality f 0 0

example :
    cokernel.π (horizontalFirstPageCoherentMap K 0) ≫
        (horizontalFirstPageCoherentCokernelIso K 0).hom =
      horizontalCompleteDirectColumnProjectionMap K 0 :=
  horizontalFirstPageCoherentCokernelIso_π_hom K 0

example (p : ℕ) :
    cokernel.π (horizontalFirstPageCoherentMap K (p + 1)) ≫
        (horizontalFirstPageCoherentCokernelIso K (p + 1)).hom =
      horizontalCompleteDirectColumnProjectionMap K (p + 1) :=
  horizontalFirstPageCoherentCokernelIso_π_hom K (p + 1)

example (f : K ⟶ L) :
    horizontalFirstPageCoherentCokernelMapOfBicomplex f 0 ≫
        (horizontalFirstPageCoherentCokernelIso L 0).hom =
      (horizontalFirstPageCoherentCokernelIso K 0).hom ≫
        horizontalDirectColumnCochainMap f 0 :=
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
    f 0

example (f : K ⟶ L) (p : ℕ) :
    horizontalFirstPageCoherentCokernelMapOfBicomplex f (p + 1) ≫
        (horizontalFirstPageCoherentCokernelIso L (p + 1)).hom =
      (horizontalFirstPageCoherentCokernelIso K (p + 1)).hom ≫
        horizontalDirectColumnCochainMap f (p + 1) :=
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
    f (p + 1)

example (p : ℕ) :
    horizontalFirstPageCoherentCokernelMapOfBicomplex (𝟙 K) p ≫
        (horizontalFirstPageCoherentCokernelIso K p).hom =
      (horizontalFirstPageCoherentCokernelIso K p).hom ≫
        horizontalDirectColumnCochainMap (𝟙 K) p :=
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
    (𝟙 K) p

example (f : K ⟶ L) (g : L ⟶ M) (p : ℕ) :
    horizontalFirstPageCoherentCokernelMapOfBicomplex (f ≫ g) p ≫
        (horizontalFirstPageCoherentCokernelIso M p).hom =
      (horizontalFirstPageCoherentCokernelIso K p).hom ≫
        horizontalDirectColumnCochainMap (f ≫ g) p :=
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
    (f ≫ g) p

example (p : ℕ) :
    cokernel.π (horizontalFirstPageCoherentMap
        (HomologicalComplex.zero : HomologicalComplex₂ C
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)) p) ≫
      (horizontalFirstPageCoherentCokernelIso
        (HomologicalComplex.zero : HomologicalComplex₂ C
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)) p).hom =
    horizontalCompleteDirectColumnProjectionMap
      (HomologicalComplex.zero : HomologicalComplex₂ C
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)) p :=
  horizontalFirstPageCoherentCokernelIso_π_hom _ p

section ZeroRing

variable {K₀ L₀ : HomologicalComplex₂ (ModuleCat.{0} (ZMod 1))
  (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

example (f : K₀ ⟶ L₀) (p : ℕ) :=
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
    f p

end ZeroRing

#print axioms horizontalFilteredTotalMapOfBicomplex_topProjection
#print axioms horizontalNaturalDirectColumnProjectionMap_naturality
#print axioms horizontalCompleteDirectColumnProjectionMap_naturality
#print axioms horizontalFirstPageCoherentMap_naturality_of_bicomplex
#print axioms horizontalFirstPageCoherentCokernelMapOfBicomplex
#print axioms horizontalFirstPageCoherentCokernelMapOfBicomplex_π
#print axioms horizontalFirstPageCoherentCokernelIso_π_hom
#print axioms
  horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex

end HomologicalComplex₂.FirstQuadrantFirstPageCoherentCokernelNaturalityTests

end
