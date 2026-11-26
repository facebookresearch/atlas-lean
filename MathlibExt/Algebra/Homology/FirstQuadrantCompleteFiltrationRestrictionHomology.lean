/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionTotal

/-!
# Homology of the complete-filtration restriction comparison

For a fixed homological degree, pointwise application of the canonical
homology functor sends the bicomplex-natural complete/finite restriction
comparison and its total-inclusion square to homology-valued diagrams.  All
maps and isomorphisms here are obtained functorially from the chain-level
constructions.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C] [CategoryWithHomology C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Pointwise degree-`n` homology on natural-index diagrams of chain
complexes. -/
noncomputable abbrev horizontalNatDiagramHomologyFunctor (n : ℕ) :
    (ℕ ⥤ ChainComplex C ℕ) ⥤ (ℕ ⥤ C) :=
  (Functor.whiskeringRight ℕ (ChainComplex C ℕ) C).obj
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n)

/-- Degree-`n` homology of the natural-index restriction of the complete
filtration, functorial in the bicomplex. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
    (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ C) :=
  horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor ⋙
    horizontalNatDiagramHomologyFunctor n

/-- Degree-`n` homology of the finite horizontal-filtration diagram,
functorial in the bicomplex. -/
noncomputable def horizontalTotalFiltrationHomologyDiagramFunctor (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ C) :=
  horizontalTotalFiltrationDiagramFunctor ⋙
    horizontalNatDiagramHomologyFunctor n

/-- Degree-`n` homology of the natural-index constant total-complex diagram,
functorial in the bicomplex. -/
noncomputable def horizontalTotalHomologyNatConstDiagramFunctor (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ C) :=
  horizontalTotalComplexNatConstDiagramFunctor ⋙
    horizontalNatDiagramHomologyFunctor n

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
      n).obj K =
      (horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor.obj K ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) :=
  rfl

@[simp]
theorem
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor_obj_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
      n).obj K).obj i =
      (horizontalCompleteFilteredTotalComplex K
        ((i : ℤ) : EInt)).homology n :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationHomologyDiagramFunctor_obj_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalTotalFiltrationHomologyDiagramFunctor n).obj K).obj i =
      (horizontalFilteredTotalComplex K i).homology n :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalHomologyNatConstDiagramFunctor_obj_obj
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalTotalHomologyNatConstDiagramFunctor n).obj K).obj i =
      (K.total (ComplexShape.down ℕ)).homology n :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor_map_app
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
      n).map f).app i =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
          ((i : ℤ) : EInt)) n :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationHomologyDiagramFunctor_map_app
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalTotalFiltrationHomologyDiagramFunctor n).map f).app i =
      HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexMapOfBicomplex f i) n :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalHomologyNatConstDiagramFunctor_map_app
    (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    ((horizontalTotalHomologyNatConstDiagramFunctor n).map f).app i =
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) n :=
  rfl

/-- The complete/finite restriction comparison after pointwise degree-`n`
homology. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
    (n : ℕ) :
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
        (C := C) n ≅
      horizontalTotalFiltrationHomologyDiagramFunctor (C := C) n :=
  Functor.isoWhiskerRight
    (horizontalCompleteTotalFiltrationNatRestrictionNatIso (C := C))
    (horizontalNatDiagramHomologyFunctor (C := C) n)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_app_app
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
      (C := C) n).hom.app K).app i =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexFiniteIso K
          (i : ℤ) (Int.natCast_nonneg i)).hom n :=
  rfl

/-- Homology of the finite-stage inclusions into total complexes. -/
noncomputable def horizontalTotalFiltrationHomologyDiagramToTotal (n : ℕ) :
    horizontalTotalFiltrationHomologyDiagramFunctor (C := C) n ⟶
      horizontalTotalHomologyNatConstDiagramFunctor (C := C) n :=
  Functor.whiskerRight (horizontalTotalFiltrationDiagramToTotal (C := C))
    (horizontalNatDiagramHomologyFunctor (C := C) n)

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationHomologyDiagramToTotal_app_app
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalTotalFiltrationHomologyDiagramToTotal
      (C := C) n).app K).app i =
      HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal K i) n :=
  rfl

/-- Homology of the restricted complete-stage inclusions into total
complexes. -/
noncomputable def
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
    (n : ℕ) :
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramFunctor
        (C := C) n ⟶
      horizontalTotalHomologyNatConstDiagramFunctor (C := C) n :=
  Functor.whiskerRight
    (horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal (C := C))
    (horizontalNatDiagramHomologyFunctor (C := C) n)

@[simp]
theorem
    horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal_app_app
    (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (i : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
      (C := C) n).app K).app i =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalToTotal K ((i : ℤ) : EInt)) n :=
  rfl

/-- Pointwise homology preserves the global complete/finite restriction
comparison with the inclusions into total complexes. -/
theorem
    horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso_hom_comp_toTotal
    (n : ℕ) :
    (horizontalCompleteTotalFiltrationNatRestrictionHomologyNatIso
        (C := C) n).hom ≫
        horizontalTotalFiltrationHomologyDiagramToTotal (C := C) n =
      horizontalCompleteTotalFiltrationNatRestrictionHomologyDiagramToTotal
        (C := C) n := by
  change Functor.whiskerRight
          ((horizontalCompleteTotalFiltrationNatRestrictionNatIso
            (C := C)).hom)
          (horizontalNatDiagramHomologyFunctor (C := C) n) ≫
      Functor.whiskerRight (horizontalTotalFiltrationDiagramToTotal (C := C))
          (horizontalNatDiagramHomologyFunctor (C := C) n) =
    Functor.whiskerRight
      (horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal (C := C))
      (horizontalNatDiagramHomologyFunctor (C := C) n)
  rw [← Functor.whiskerRight_comp]
  rw [horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_comp_toTotal]

end HomologicalComplex₂

end
