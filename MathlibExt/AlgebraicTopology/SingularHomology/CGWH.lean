/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerDimension
public import MathlibExt.AlgebraicTopology.SingularHomology.Integral
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClasses
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopySingularHomology
public import MathlibExt.Topology.Category.CGWH.Point

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.WeakHomotopyReducedSingularHomology

/-!
# Singular homology of CGWH spaces

This file provides thin CGWH facades for singular chains and homology by
precomposition with the inclusion into topological spaces.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

universe a w v u

namespace CGWH

/-- Singular chains on CGWH spaces. -/
noncomputable abbrev singularChainComplexFunctor
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) :
    CGWH.{a, w} ⥤ ChainComplex C ℕ :=
  CGWH.cgwhToTop ⋙
    (AlgebraicTopology.singularChainComplexFunctor C).obj R

/-- Singular homology on CGWH spaces. -/
noncomputable abbrev singularHomologyFunctor
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [CategoryWithHomology C]
    (R : C) (n : ℕ) : CGWH.{a, w} ⥤ C :=
  CGWH.cgwhToTop ⋙
    (AlgebraicTopology.singularHomologyFunctor C n).obj R

/-- Integer-graded singular chains on CGWH spaces. -/
noncomputable abbrev singularChainIntFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) :
    CGWH.{a, w} ⥤ ChainComplex C ℤ :=
  CGWH.cgwhToTop ⋙
    AlgebraicTopology.singularChainIntFunctor C R

/-- Integer-graded singular homology on CGWH spaces. -/
noncomputable abbrev singularHomologyIntFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (z : ℤ) :
    CGWH.{a, w} ⥤ C :=
  CGWH.cgwhToTop ⋙
    AlgebraicTopology.singularHomologyIntFunctor C R z

/-- Reduced singular homology on CGWH spaces. -/
noncomputable abbrev reducedSingularHomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (n : ℕ) :
    CGWH.{a, w} ⥤ C :=
  CGWH.cgwhToTop ⋙
    AlgebraicTopology.reducedSingularHomologyFunctor C R n

/-- Integral singular chains on CGWH spaces. -/
noncomputable abbrev singularIntegralChainFunctor :
    CGWH.{a, u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  CGWH.cgwhToTop ⋙
    AlgebraicTopology.singularIntegralChainFunctor

/-- Integral singular homology on CGWH spaces. -/
noncomputable abbrev singularIntegralHomologyFunctor (n : ℕ) :
    CGWH.{a, u} ⥤ AddCommGrpCat.{u} :=
  CGWH.cgwhToTop ⋙
    AlgebraicTopology.singularIntegralHomologyFunctor n

@[simp]
theorem singularChainComplexFunctor_obj
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (X : CGWH.{a, w}) :
    (CGWH.singularChainComplexFunctor C R).obj X =
      ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

@[simp]
theorem singularChainComplexFunctor_map
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C)
    {X Y : CGWH.{a, w}} (f : X ⟶ Y) :
    (CGWH.singularChainComplexFunctor C R).map f =
      ((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
        (CGWH.cgwhToTop.map f) :=
  rfl

@[simp]
theorem singularHomologyFunctor_obj
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [CategoryWithHomology C]
    (R : C) (n : ℕ) (X : CGWH.{a, w}) :
    (CGWH.singularHomologyFunctor C R n).obj X =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

@[simp]
theorem singularHomologyFunctor_map
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [CategoryWithHomology C]
    (R : C) (n : ℕ) {X Y : CGWH.{a, w}} (f : X ⟶ Y) :
    (CGWH.singularHomologyFunctor C R n).map f =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
        (CGWH.cgwhToTop.map f) :=
  rfl

@[simp]
theorem singularChainIntFunctor_obj
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (X : CGWH.{a, w}) :
    (CGWH.singularChainIntFunctor C R).obj X =
      (AlgebraicTopology.singularChainIntFunctor C R).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

@[simp]
theorem singularChainIntFunctor_map
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C)
    {X Y : CGWH.{a, w}} (f : X ⟶ Y) :
    (CGWH.singularChainIntFunctor C R).map f =
      (AlgebraicTopology.singularChainIntFunctor C R).map
        (CGWH.cgwhToTop.map f) :=
  rfl

@[simp]
theorem singularHomologyIntFunctor_obj
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (z : ℤ)
    (X : CGWH.{a, w}) :
    (CGWH.singularHomologyIntFunctor C R z).obj X =
      (AlgebraicTopology.singularHomologyIntFunctor C R z).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

@[simp]
theorem singularHomologyIntFunctor_map
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (z : ℤ)
    {X Y : CGWH.{a, w}} (f : X ⟶ Y) :
    (CGWH.singularHomologyIntFunctor C R z).map f =
      (AlgebraicTopology.singularHomologyIntFunctor C R z).map
        (CGWH.cgwhToTop.map f) :=
  rfl

@[simp]
theorem reducedSingularHomologyFunctor_obj
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (n : ℕ)
    (X : CGWH.{a, w}) :
    (CGWH.reducedSingularHomologyFunctor C R n).obj X =
      (AlgebraicTopology.reducedSingularHomologyFunctor C R n).obj
        (CGWH.cgwhToTop.obj X) :=
  rfl

@[simp]
theorem reducedSingularHomologyFunctor_map
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (n : ℕ)
    {X Y : CGWH.{a, w}} (f : X ⟶ Y) :
    (CGWH.reducedSingularHomologyFunctor C R n).map f =
      (AlgebraicTopology.reducedSingularHomologyFunctor C R n).map
        (CGWH.cgwhToTop.map f) :=
  rfl

/-- Degree-zero singular homology of the CGWH point recovers the coefficient
object. -/
noncomputable def singularHomologyPointZeroIso
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) :
    (CGWH.singularHomologyFunctor C R 0).obj
        CGWH.point.{a, w} ≅ R :=
  AlgebraicTopology.singularHomologyPUnitZeroIso C R

/-- Singular homology of the CGWH point vanishes in nonzero natural
degrees. -/
theorem isZero_singularHomologyPoint_of_ne_zero
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (n : ℕ) (hn : n ≠ 0) :
    IsZero
      ((CGWH.singularHomologyFunctor C R n).obj
        CGWH.point.{a, w}) :=
  AlgebraicTopology.isZero_singularHomology_punit C R n hn

/-- Degree-zero integer-graded singular homology of the CGWH point recovers
the coefficient object. -/
noncomputable def singularHomologyIntPointZeroIso
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) :
    (CGWH.singularHomologyIntFunctor C R (0 : ℤ)).obj
        CGWH.point.{a, w} ≅ R :=
  AlgebraicTopology.singularHomologyIntPUnitZeroIso C R

/-- Integer-graded singular homology of the CGWH point vanishes away from
degree zero. -/
theorem isZero_singularHomologyIntPoint_of_ne_zero
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (z : ℤ) (hz : z ≠ 0) :
    IsZero
      ((CGWH.singularHomologyIntFunctor C R z).obj
        CGWH.point.{a, w}) :=
  AlgebraicTopology.isZero_singularHomologyInt_punit C R z hz

/-- Reduced singular homology of the CGWH point vanishes in every degree. -/
theorem isZero_reducedSingularHomologyPoint
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (n : ℕ) :
    IsZero
      ((CGWH.reducedSingularHomologyFunctor C R n).obj
        CGWH.point.{a, w}) :=
  AlgebraicTopology.isZero_reducedSingularHomology_punit C R n

private theorem weakHomotopyEquivalences_toTop
    {X Y : CGWH.{a, w}} {f : X ⟶ Y}
    (hf : CGWH.weakHomotopyEquivalences f) :
    TopCat.weakHomotopyEquivalences (CGWH.cgwhToTop.map f) := by
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage,
    CategoryTheory.MorphismProperty.inverseImage_iff] at hf
  exact hf

namespace weakHomotopyEquivalences

/-- A CGWH weak homotopy equivalence induces a quasi-isomorphism on singular
chains. -/
theorem quasiIso_singularChainComplexMap
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [CategoryWithHomology C]
    {X Y : CGWH.{a, w}} {f : X ⟶ Y}
    (hf : CGWH.weakHomotopyEquivalences f) (A : C) :
    QuasiIso ((CGWH.singularChainComplexFunctor C A).map f) :=
  (CGWH.weakHomotopyEquivalences_toTop hf).quasiIso_singularChainComplexMap A

/-- A CGWH weak homotopy equivalence induces an isomorphism on ordinary
singular homology. -/
theorem isIso_singularHomologyFunctor_map
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [CategoryWithHomology C]
    {X Y : CGWH.{a, w}} {f : X ⟶ Y}
    (hf : CGWH.weakHomotopyEquivalences f) (A : C) (n : ℕ) :
    IsIso ((CGWH.singularHomologyFunctor C A n).map f) :=
  (CGWH.weakHomotopyEquivalences_toTop hf).isIso_singularHomologyFunctor_map A n

/-- A CGWH weak homotopy equivalence induces an isomorphism on reduced
singular homology. -/
theorem isIso_reducedSingularHomologyFunctor_map
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C]
    {X Y : CGWH.{a, w}} {f : X ⟶ Y}
    (hf : CGWH.weakHomotopyEquivalences f) (A : C) (n : ℕ) :
    IsIso ((CGWH.reducedSingularHomologyFunctor C A n).map f) :=
  (CGWH.weakHomotopyEquivalences_toTop hf).isIso_reducedSingularHomologyFunctor_map
    A n

end weakHomotopyEquivalences

end CGWH

end
