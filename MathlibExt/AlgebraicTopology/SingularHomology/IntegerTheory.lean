/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

import MathlibExt.Algebra.Homology.HomologySequenceFunctor

public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerHomotopy
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerExactness
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerExcision
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerAdditivity
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerDimensionAxiom
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeBoundaryCoefficient

/-!
# Integer-graded singular homology theory
-/

@[expose] public section

universe w v u

/-- Integer-graded singular homology packaged as an ordinary homology theory. -/
noncomputable def singularHomologyIntTheory {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{w} C]
    [CategoryTheory.AB4OfSize.{w} C] (R : C)
    [hExcisive : (AlgebraicTopology.singularHomologyIntData C R).IsExcisive] :
    TopPair.OrdinaryHomologyTheory C :=
  TopPair.OrdinaryHomologyTheory.of (AlgebraicTopology.singularHomologyIntData C R)

/-- Identifying the relative degree-`z` functor of `singularHomologyIntTheory`. -/
@[simp]
lemma singularHomologyIntTheory_Hₚ {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{w} C]
    [CategoryTheory.AB4OfSize.{w} C] (R : C)
    [hExcisive : (AlgebraicTopology.singularHomologyIntData C R).IsExcisive] (z : ℤ) :
    (TopPair.OrdinaryHomologyTheory.hₚFunctor (C := C) z).obj
        (singularHomologyIntTheory (C := C) R) =
      AlgebraicTopology.relativeSingularHomologyIntFunctor C R z :=
  rfl

/-- Identifying the absolute degree-`z` functor of `singularHomologyIntTheory`. -/
@[simp]
lemma singularHomologyIntTheory_H {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{w} C]
    [CategoryTheory.AB4OfSize.{w} C] (R : C)
    [hExcisive : (AlgebraicTopology.singularHomologyIntData C R).IsExcisive] (z : ℤ) :
    (TopPair.OrdinaryHomologyTheory.hFunctor (C := C) z).obj
        (singularHomologyIntTheory (C := C) R) =
      AlgebraicTopology.singularHomologyIntFunctor C R z :=
  rfl

/-- Integral specialization of `singularHomologyIntTheory` to `ℤ`. -/
noncomputable abbrev singularHomologyℤTheory :
    TopPair.OrdinaryHomologyTheory AddCommGrpCat.{0} :=
  singularHomologyIntTheory (AddCommGrpCat.of ℤ)

open CategoryTheory Limits HomologicalComplex TopPair

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

noncomputable def singularChainIntCoefficientFunctor :
    C ⥤ (TopCat.{w} ⥤ ChainComplex C ℤ) :=
  singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight TopCat.{w} (ChainComplex C ℕ)
      (ChainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNatToIntExtendFunctor C)

noncomputable def relativeSingularChainIntCoefficientFunctor :
    C ⥤ (TopPair.{w} ⥤ ChainComplex C ℤ) :=
  relativeSingularChainComplexFunctor (C := C) ⋙
    (Functor.whiskeringRight TopPair.{w} (ChainComplex C ℕ)
      (ChainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNatToIntExtendFunctor C)

noncomputable def singularHomologyIntCoefficientFunctor (z : ℤ) :
    C ⥤ (TopCat.{w} ⥤ C) :=
  singularChainIntCoefficientFunctor (C := C) ⋙
    (Functor.whiskeringRight TopCat.{w} (ChainComplex C ℤ) C).obj
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) z)

noncomputable def relativeSingularHomologyIntCoefficientFunctor (z : ℤ) :
    C ⥤ (TopPair.{w} ⥤ C) :=
  relativeSingularChainIntCoefficientFunctor (C := C) ⋙
    (Functor.whiskeringRight TopPair.{w} (ChainComplex C ℤ) C).obj
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) z)

noncomputable def singularPairShortComplexIntCoefficientFunctor :
    C ⥤ (TopPair.{w} ⥤ ShortComplex (ChainComplex C ℤ)) :=
  singularPairShortComplexCoefficientFunctor (C := C) ⋙
    (Functor.whiskeringRight TopPair.{w} (ShortComplex (ChainComplex C ℕ))
      (ShortComplex (ChainComplex C ℤ))).obj
        (ComplexShape.embeddingDownNatToIntExtendFunctor C).mapShortComplex

@[simp] lemma singularChainIntCoefficientFunctor_obj (R : C) :
    (singularChainIntCoefficientFunctor (C := C)).obj R = singularChainIntFunctor C R := rfl

@[simp] lemma relativeSingularChainIntCoefficientFunctor_obj (R : C) :
    (relativeSingularChainIntCoefficientFunctor (C := C)).obj R =
      relativeSingularChainIntFunctor C R := rfl

@[simp] lemma singularHomologyIntCoefficientFunctor_obj (R : C) (z : ℤ) :
    (singularHomologyIntCoefficientFunctor (C := C) z).obj R =
      singularHomologyIntFunctor C R z := rfl

@[simp] lemma relativeSingularHomologyIntCoefficientFunctor_obj (R : C) (z : ℤ) :
    (relativeSingularHomologyIntCoefficientFunctor (C := C) z).obj R =
      relativeSingularHomologyIntFunctor C R z := rfl

@[simp] lemma singularPairShortComplexIntCoefficientFunctor_obj (R : C) :
    (singularPairShortComplexIntCoefficientFunctor (C := C)).obj R =
      singularPairShortComplexIntFunctor C R := rfl

theorem singularHomologyEmptyPairIntIso_naturality_coefficient
    {R S : C} (a : R ⟶ S) (z : ℤ) :
    (singularHomologyEmptyPairIntIso C R z).hom ≫
        TopPair.incl.whiskerLeft
          ((relativeSingularHomologyIntCoefficientFunctor (C := C) z).map a) =
      ((singularHomologyIntCoefficientFunctor (C := C) z).map a) ≫
        (singularHomologyEmptyPairIntIso C S z).hom := by
  apply NatTrans.ext
  funext X
  change HomologicalComplex.homologyMap
        (((singularPairShortComplexIntCoefficientFunctor (C := C)).obj R).obj
          (TopPair.incl.obj X)).g z ≫
      HomologicalComplex.homologyMap
        (((singularPairShortComplexIntCoefficientFunctor (C := C)).map a).app
          (TopPair.incl.obj X)).τ₃ z =
    HomologicalComplex.homologyMap
        (((singularPairShortComplexIntCoefficientFunctor (C := C)).map a).app
          (TopPair.incl.obj X)).τ₂ z ≫
      HomologicalComplex.homologyMap
        (((singularPairShortComplexIntCoefficientFunctor (C := C)).obj S).obj
          (TopPair.incl.obj X)).g z
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun f => HomologicalComplex.homologyMap f z)
    ((((singularPairShortComplexIntCoefficientFunctor (C := C)).map a).app
      (TopPair.incl.obj X)).comm₂₃.symm)

theorem relativeSingularBoundaryIntRel_naturality_coefficient
    {R S : C} (a : R ⟶ S) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    (relativeSingularHomologyIntCoefficientFunctor (C := C) i).map a ≫
        relativeSingularBoundaryIntRel C S i j hij =
      relativeSingularBoundaryIntRel C R i j hij ≫
        TopPair.proj₂.whiskerLeft
          ((singularHomologyIntCoefficientFunctor (C := C) j).map a) := by
  apply NatTrans.ext
  funext P
  exact (HomologicalComplex.HomologySequence.δNatTrans
    (C := C) i j hij).naturality
      (show (⟨(singularPairShortComplexIntFunctor C R).obj P,
        singularPairShortComplexIntFunctor_obj_shortExact C R P⟩ :
          ShortComplex.ShortExactSequences (ChainComplex C ℤ)) ⟶
        ⟨(singularPairShortComplexIntFunctor C S).obj P,
          singularPairShortComplexIntFunctor_obj_shortExact C S P⟩ from
        ⟨((singularPairShortComplexIntCoefficientFunctor (C := C)).map a).app P⟩)

noncomputable def singularHomologyIntDataHom
    {R S : C} (a : R ⟶ S) :
    singularHomologyIntData C R ⟶ singularHomologyIntData C S where
  homₚ z := (relativeSingularHomologyIntCoefficientFunctor (C := C) z).map a
  hom z := (singularHomologyIntCoefficientFunctor (C := C) z).map a
  iso_comm z := singularHomologyEmptyPairIntIso_naturality_coefficient C a z
  w i j := by
    by_cases hij : (ComplexShape.down ℤ).Rel i j
    · dsimp only [singularHomologyIntData]
      rw [dite_eq_left hij, dite_eq_left hij]
      exact (relativeSingularBoundaryIntRel_naturality_coefficient C a i j hij).symm
    · dsimp only [singularHomologyIntData]
      simp only [dite_eq_right hij, zero_comp]
      exact comp_zero.symm

noncomputable def singularHomologyIntDataFunctor :
    C ⥤ TopPair.HomologyTheoryData.{w} C where
  obj R := singularHomologyIntData C R
  map a := singularHomologyIntDataHom C a
  map_id R := by
    apply TopPair.HomologyPretheory.Hom.ext <;>
      funext z <;> simp [singularHomologyIntDataHom]
  map_comp a b := by
    apply TopPair.HomologyPretheory.Hom.ext
    · funext z
      simp [singularHomologyIntDataHom]
    · funext z
      rw [TopPair.HomologyPretheory.Hom.comp_hom]
      simp [singularHomologyIntDataHom]

/-- The coefficient-object functor `C ⥤ TopPair.OrdinaryHomologyTheory C` sending `R` to
`singularHomologyIntTheory (C := C) R`; the supplied family `hExcisive` provides excision. -/
noncomputable def singularHomologyIntTheoryFunctor [AB4OfSize.{w} C]
    (hExcisive : ∀ R : C, (singularHomologyIntData C R).IsExcisive) :
    C ⥤ TopPair.OrdinaryHomologyTheory C :=
  (TopPair.HomologyTheoryData.isOrdinaryHomologyTheory (C := C)).lift
    (singularHomologyIntDataFunctor (C := C))
    (fun R => haveI := hExcisive R; (singularHomologyIntTheory (C := C) R).property)

@[simp]
lemma singularHomologyIntTheoryFunctor_obj [AB4OfSize.{w} C]
    (hExcisive : ∀ R : C, (singularHomologyIntData C R).IsExcisive) (R : C) :
    (singularHomologyIntTheoryFunctor (hExcisive := hExcisive)).obj R =
      singularHomologyIntTheory (C := C) R := rfl

/-- Relative evaluation identification for `singularHomologyIntTheoryFunctor`: whiskering
with `hₚFunctor z` identifies the theory with `relativeSingularHomologyIntCoefficientFunctor z`. -/
noncomputable def singularHomologyIntTheoryFunctorHₚIso [AB4OfSize.{w} C]
    (hExcisive : ∀ R : C, (singularHomologyIntData C R).IsExcisive) (z : ℤ) :
    singularHomologyIntTheoryFunctor (hExcisive := hExcisive) ⋙
        TopPair.OrdinaryHomologyTheory.hₚFunctor (C := C) z ≅
      relativeSingularHomologyIntCoefficientFunctor (C := C) z :=
  Iso.refl _

/-- Absolute evaluation identification for `singularHomologyIntTheoryFunctor`: whiskering
with `hFunctor z` identifies the theory with `singularHomologyIntCoefficientFunctor z`. -/
noncomputable def singularHomologyIntTheoryFunctorHIso [AB4OfSize.{w} C]
    (hExcisive : ∀ R : C, (singularHomologyIntData C R).IsExcisive) (z : ℤ) :
    singularHomologyIntTheoryFunctor (hExcisive := hExcisive) ⋙
        TopPair.OrdinaryHomologyTheory.hFunctor (C := C) z ≅
      singularHomologyIntCoefficientFunctor (C := C) z :=
  Iso.refl _

end AlgebraicTopology
