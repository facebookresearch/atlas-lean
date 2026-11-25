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
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageMappingConeNaturality

/-! # Tests for coherent first-page mapping-cone naturality -/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageMappingConeNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
#check horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₁
#check horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₂
#check horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₃
#check
  horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
#check
  horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex

example (f : K ⟶ L) (p : ℕ) :
    ShortComplex.cokernelSequence (horizontalFirstPageCoherentMap K p) ⟶
      ShortComplex.cokernelSequence
        (horizontalFirstPageCoherentMap L p) :=
  horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex f p

example (f : K ⟶ L) (p : ℕ) :
    (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
      f p).τ₁ =
        horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p :=
  horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₁
    f p

example (f : K ⟶ L) (p : ℕ) :
    (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
      f p).τ₂ =
        horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p :=
  horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₂
    f p

example (f : K ⟶ L) (p : ℕ) :
    (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
      f p).τ₃ =
        horizontalFirstPageCoherentCokernelMapOfBicomplex f p :=
  horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₃
    f p

example (f : K ⟶ L) (p : ℕ) :
    (horizontalCompleteFiltrationMappingConeNatTrans f).app
          (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))) ≫
        horizontalFirstPageCoherentMappingConeToDirectColumn L p =
      horizontalFirstPageCoherentMappingConeToDirectColumn K p ≫
        horizontalDirectColumnCochainMap f p :=
  horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
    f p

example (f : K ⟶ L) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-(p : ℤ) - q)).app
        (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))) ≫
        (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          L p q).hom =
      (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          K p q).hom ≫
        HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p) (-(p : ℤ) - q) :=
  horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex
    f p q

example (f : K ⟶ L) :
    (horizontalCompleteFiltrationMappingConeNatTrans f).app
          (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le 0))) ≫
        horizontalFirstPageCoherentMappingConeToDirectColumn L 0 =
      horizontalFirstPageCoherentMappingConeToDirectColumn K 0 ≫
        horizontalDirectColumnCochainMap f 0 :=
  horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
    f 0

example (f : K ⟶ L) (p : ℕ) :
    (horizontalCompleteFiltrationMappingConeNatTrans f).app
          (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le (p + 1)))) ≫
        horizontalFirstPageCoherentMappingConeToDirectColumn L (p + 1) =
      horizontalFirstPageCoherentMappingConeToDirectColumn K (p + 1) ≫
        horizontalDirectColumnCochainMap f (p + 1) :=
  horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
    f (p + 1)

example (f : K ⟶ L) (p : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-(p : ℤ) - ((0 : ℕ) : ℤ))).app
        (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))) ≫
        (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          L p 0).hom =
      (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          K p 0).hom ≫
        HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p)
          (-(p : ℤ) - ((0 : ℕ) : ℤ)) :=
  horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex
    f p 0

example (f : K ⟶ L) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom 0).app
          (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le 0))) ≫
        (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          L 0 0).hom =
      (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          K 0 0).hom ≫
        HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f 0) 0 := by
  simpa using
    horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex
      f 0 0

example (p : ℕ) :
    (horizontalCompleteFiltrationMappingConeNatTrans (𝟙 K)).app
          (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))) ≫
        horizontalFirstPageCoherentMappingConeToDirectColumn K p =
      horizontalFirstPageCoherentMappingConeToDirectColumn K p ≫
        horizontalDirectColumnCochainMap (𝟙 K) p :=
  horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
    (𝟙 K) p

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap (f ≫ g)).hom
          (-(p : ℤ) - q)).app
        (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))) ≫
        (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          M p q).hom =
      (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          K p q).hom ≫
        HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap (f ≫ g) p)
          (-(p : ℤ) - q) :=
  horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex
    (f ≫ g) p q

example (p : ℕ) :
    (horizontalCompleteFiltrationMappingConeNatTrans
        (𝟙 (HomologicalComplex.zero : HomologicalComplex₂ C
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)))).app
          (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))) ≫
      horizontalFirstPageCoherentMappingConeToDirectColumn
        (HomologicalComplex.zero : HomologicalComplex₂ C
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)) p =
    horizontalFirstPageCoherentMappingConeToDirectColumn
        (HomologicalComplex.zero : HomologicalComplex₂ C
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)) p ≫
      horizontalDirectColumnCochainMap
        (𝟙 (HomologicalComplex.zero : HomologicalComplex₂ C
          (ComplexShape.down ℕ) (ComplexShape.down ℕ))) p :=
  horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
    _ p

section ZeroRing

variable {K₀ L₀ : HomologicalComplex₂ (ModuleCat.{0} (ZMod 1))
  (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

example (f : K₀ ⟶ L₀) (p q : ℕ) :=
  horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex
    f p q

end ZeroRing

#print axioms
  horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
#print axioms
  horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
#print axioms
  horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex

end HomologicalComplex₂.FirstQuadrantFirstPageMappingConeNaturalityTests

end
