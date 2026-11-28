/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCoherentCokernelNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralNaturality

/-!
# Naturality of coherent filtration cones and direct columns

Let `f : K → L` be a map of first-quadrant bicomplexes in an abelian category. The coherent
lower-stage, upper-stage, and cokernel maps form a morphism of the cokernel short complexes
for each first-page window.

The induced mapping-cone map commutes with descent to the direct column and its cokernel
comparison. Taking homology at degree `-p-q` gives naturality of the coherent relative-window
homology isomorphism.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The cokernel-sequence map of a coherent first-page window.

The lower and upper filtration-stage maps induced by a bicomplex morphism, together with the
induced cokernel map, define a morphism of window cokernel sequences. -/
noncomputable def horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
    (f : K ⟶ L) (p : ℕ) :
    ShortComplex.cokernelSequence (horizontalFirstPageCoherentMap K p) ⟶
      ShortComplex.cokernelSequence
        (horizontalFirstPageCoherentMap L p) where
  τ₁ := horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p
  τ₂ := horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p
  τ₃ := horizontalFirstPageCoherentCokernelMapOfBicomplex f p
  comm₁₂ :=
    (horizontalFirstPageCoherentMap_naturality_of_bicomplex f p).symm
  comm₂₃ :=
    (horizontalFirstPageCoherentCokernelMapOfBicomplex_π f p).symm

/-- The lower endpoint of a coherent window cokernel-sequence map.

The first component is the bicomplex-induced map of the coherent lower cochain stage. -/
@[simp]
theorem horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₁
    (f : K ⟶ L) (p : ℕ) :
    (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
      f p).τ₁ =
        horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p :=
  rfl

/-- The upper endpoint of a coherent window cokernel-sequence map.

The middle component is the bicomplex-induced map of the coherent upper cochain stage. -/
@[simp]
theorem horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₂
    (f : K ⟶ L) (p : ℕ) :
    (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
      f p).τ₂ =
        horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p :=
  rfl

/-- The cokernel endpoint of a coherent window sequence map.

The third component is the induced map between the coherent filtration cokernels. -/
@[simp]
theorem horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₃
    (f : K ⟶ L) (p : ℕ) :
    (horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
      f p).τ₃ =
        horizontalFirstPageCoherentCokernelMapOfBicomplex f p :=
  rfl

/-- Naturality of coherent cone descent to a direct column.

The mapping-cone map of a bicomplex morphism followed by target cone-to-column descent equals
source descent followed by the direct-column map. -/
theorem horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
    (f : K ⟶ L) (p : ℕ) :
    (horizontalCompleteFiltrationMappingConeNatTrans f).app
          (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))) ≫
        horizontalFirstPageCoherentMappingConeToDirectColumn L p =
      horizontalFirstPageCoherentMappingConeToDirectColumn K p ≫
        horizontalDirectColumnCochainMap f p := by
  let SK := ShortComplex.cokernelSequence
    (horizontalFirstPageCoherentMap K p)
  let SL := ShortComplex.cokernelSequence
    (horizontalFirstPageCoherentMap L p)
  let φ := horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex
    f p
  have hDesc := CochainComplex.mappingCone.descShortComplex_naturality φ
  have hIso :=
    horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
      f p
  change CochainComplex.mappingCone.map SK.f SL.f φ.τ₁ φ.τ₂
        φ.comm₁₂.symm ≫
        (CochainComplex.mappingCone.descShortComplex SL ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom) =
      (CochainComplex.mappingCone.descShortComplex SK ≫
        (horizontalFirstPageCoherentCokernelIso K p).hom) ≫
          horizontalDirectColumnCochainMap f p
  calc
    _ = (CochainComplex.mappingCone.map SK.f SL.f φ.τ₁ φ.τ₂
          φ.comm₁₂.symm ≫
        CochainComplex.mappingCone.descShortComplex SL) ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom :=
      (Category.assoc _ _ _).symm
    _ = (CochainComplex.mappingCone.descShortComplex SK ≫ φ.τ₃) ≫
        (horizontalFirstPageCoherentCokernelIso L p).hom := by
      rw [hDesc]
    _ = CochainComplex.mappingCone.descShortComplex SK ≫
        (φ.τ₃ ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom) :=
      Category.assoc _ _ _
    _ = CochainComplex.mappingCone.descShortComplex SK ≫
        ((horizontalFirstPageCoherentCokernelIso K p).hom ≫
          horizontalDirectColumnCochainMap f p) := by
      rw [horizontalFirstPageCoherentCokernelShortComplexMapOfBicomplex_τ₃,
        hIso]
    _ = (CochainComplex.mappingCone.descShortComplex SK ≫
        (horizontalFirstPageCoherentCokernelIso K p).hom) ≫
          horizontalDirectColumnCochainMap f p :=
      (Category.assoc _ _ _).symm

/-- Naturality of coherent relative-window homology in direct-column coordinates.

At degree `-p-q`, the induced relative homology map commutes with the direct-column homology
comparison and the direct-column homology map. -/
theorem
    horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-(p : ℤ) - q)).app
        (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))) ≫
        (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          L p q).hom =
      (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          K p q).hom ≫
        HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p) (-(p : ℤ) - q) := by
  rw [horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom,
    horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom]
  let D := mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p))
  let m := (horizontalCompleteFiltrationMappingConeNatTrans f).app D
  let n : ℤ := -(p : ℤ) - q
  have hFactors := (HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) n).hom.naturality m
  change _ =
    (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) n).hom.app
        ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
      HomologicalComplex.homologyMap m n at hFactors
  have hChain :=
    horizontalFirstPageCoherentMappingConeToDirectColumn_naturality_of_bicomplex
      f p
  have hChainHomology := congrArg
    (fun k ↦ HomologicalComplex.homologyMap k n) hChain
  simp only [HomologicalComplex.homologyMap_comp] at hChainHomology
  have hSpectral :
      ((horizontalCompleteFiltrationSpectralObjectMap f).hom n).app D =
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor C
            (ComplexShape.up ℤ) n).map m) := by
    rfl
  rw [hSpectral]
  change
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) n).map m) ≫
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) n).hom.app
          ((horizontalCompleteFiltrationMappingConeFunctor L).obj D) ≫
      HomologicalComplex.homologyMap
        (horizontalFirstPageCoherentMappingConeToDirectColumn L p) n =
    ((HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) n).hom.app
          ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
      HomologicalComplex.homologyMap
        (horizontalFirstPageCoherentMappingConeToDirectColumn K p) n) ≫
      HomologicalComplex.homologyMap
        (horizontalDirectColumnCochainMap f p) n
  calc
    _ = (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) n).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
        HomologicalComplex.homologyMap m n ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageCoherentMappingConeToDirectColumn L p) n := by
      simpa only [Category.assoc] using hFactors =≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageCoherentMappingConeToDirectColumn L p) n
    _ = (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) n).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageCoherentMappingConeToDirectColumn K p) n ≫
        HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p) n := by
      simpa only [Category.assoc] using
        ((HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) n).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫=
          hChainHomology)
    _ = _ := by simp only [Category.assoc]

end HomologicalComplex₂

end
