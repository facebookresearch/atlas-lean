/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import MathlibExt.Algebra.Homology.BisimplicialModule.Diagonal
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFunctor
public import MathlibExt.Algebra.Homology.PartialTotalEIntFiltration
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Retract

/-!
# Actual normalized bisimplicial objects and their filtered totals

Normalize the actual inner simplicial object, then the actual outer one in
the abelian category of chain complexes. This is a first-quadrant bicomplex;
its two differentials commute by the native chain-map laws. The native total
adds its existing homological sign and finite antidiagonal coproducts.

The existing complete horizontal-filtration functor gives the actual filtered
total, with all original maps retained. The separate native diagonal functor
gives the normalized diagonal model. No diagonal/total comparison, asphericity,
spectral-page identification or convergence is accepted as caller data or
claimed merely from constructing these objects.

The coefficient category is arbitrary abelian, with independent object/hom
worlds. The construction is natural in bisimplicial objects and their morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped ZeroObject

universe u v

namespace BisimplicialModule

variable (C : Type u) [Category.{v} C]


variable [Abelian C]

/-- The actual native Moore split pair, viewed as a retract for componentwise properties. -/
def normalizationRetract (X : SimplicialObject C) :
    Retract ((normalizedMooreComplex C).obj X) ((alternatingFaceMapComplex C).obj X) where
  i := inclusionOfMooreComplexMap X
  r := DoldKan.PInftyToNormalizedMooreComplex X
  retract := (DoldKan.splitMonoInclusionOfMooreComplexMap X).id

/-- Actual projective simplicial degrees have projective normalized degrees. -/
theorem normalizedDegree_projective (X : SimplicialObject C)
    (hX : ∀ n : ℕ, Projective (X.obj (Opposite.op (SimplexCategory.mk n)))) (n : ℕ) :
    Projective (((normalizedMooreComplex C).obj X).X n) := by
  have hP : Projective ((HomologicalComplex.eval C (ComplexShape.down ℕ) n).obj
      ((alternatingFaceMapComplex C).obj X)) := by
    change Projective (X.obj (Opposite.op (SimplexCategory.mk n)))
    exact hX n
  exact ((normalizationRetract C X).map
    (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).projective (p := hP)

/-- Normalize both actual simplicial variables using the native Moore functors. -/
def normalizedBicomplexFunctor :
    SimplicialObject (SimplicialObject C) ⥤
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (SimplicialObject.whiskering (SimplicialObject C) (ChainComplex C ℕ)).obj
      (normalizedMooreComplex C) ⋙ normalizedMooreComplex (ChainComplex C ℕ)

/-- The actual original double-normalized chain object. -/
abbrev normalizedBicomplex (X : SimplicialObject (SimplicialObject C)) :=
  (normalizedBicomplexFunctor C).obj X

/-- Both native Moore retracts preserve the actual original component projectivity. -/
theorem normalizedBicomplexTerm_projective (X : SimplicialObject (SimplicialObject C))
    (hX : ∀ p q : ℕ, Projective ((X.obj (Opposite.op (SimplexCategory.mk p))).obj
      (Opposite.op (SimplexCategory.mk q)))) (p q : ℕ) :
    Projective (((normalizedBicomplex C X).X p).X q) := by
  let Y := X ⋙ normalizedMooreComplex C
  have hP : Projective
      ((HomologicalComplex.eval (ChainComplex C ℕ) (ComplexShape.down ℕ) p ⋙
          HomologicalComplex.eval C (ComplexShape.down ℕ) q).obj
        ((alternatingFaceMapComplex (ChainComplex C ℕ)).obj Y)) := by
    change Projective (((normalizedMooreComplex C).obj
      (X.obj (Opposite.op (SimplexCategory.mk p)))).X q)
    exact normalizedDegree_projective C
      (X.obj (Opposite.op (SimplexCategory.mk p))) (hX p) q
  exact ((normalizationRetract (ChainComplex C ℕ) Y).map
    (HomologicalComplex.eval (ChainComplex C ℕ) (ComplexShape.down ℕ) p ⋙
      HomologicalComplex.eval C (ComplexShape.down ℕ) q)).projective (p := hP)

/-- Reuse native totalization, including its original total differential signs. -/
def totalFunctor : SimplicialObject (SimplicialObject C) ⥤ ChainComplex C ℕ :=
  normalizedBicomplexFunctor C ⋙
    HomologicalComplex₂.totalFunctor C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- The existing complete horizontal filtration of the actual native total. -/
def filteredTotalFunctor :
    SimplicialObject (SimplicialObject C) ⥤ FilteredObject (ChainComplex C ℕ) EInt :=
  normalizedBicomplexFunctor C ⋙
    HomologicalComplex₂.horizontalCompleteTotalFilteredObjectFunctor

/-- The actual partial-total tower has zero bottom and the native total at top. -/
abbrev partialTotalFiltration (X : SimplicialObject (SimplicialObject C)) :
    EInt ⥤ ChainComplex C ℕ :=
  (normalizedBicomplex C X).partialTotalEIntFiltration

theorem partialTotalFiltration_bot (X : SimplicialObject (SimplicialObject C)) :
    (partialTotalFiltration C X).obj ⊥ = 0 :=
  HomologicalComplex₂.partialTotalEIntFiltration_obj_bot _

theorem partialTotalFiltration_top (X : SimplicialObject (SimplicialObject C)) :
    (partialTotalFiltration C X).obj ⊤ = (totalFunctor C).obj X :=
  HomologicalComplex₂.partialTotalEIntFiltration_obj_top _

/-- Normalize the actual diagonal separately from the filtered-total construction. -/
def diagonalChainFunctor : SimplicialObject (SimplicialObject C) ⥤ ChainComplex C ℕ :=
  diagonalFunctor C ⋙ normalizedMooreComplex C

/-- The total map on every original antidiagonal coprojection is the same
actual double-normalized component map. -/
theorem totalMap_ι {X Y : SimplicialObject (SimplicialObject C)} (f : X ⟶ Y)
    (p q n : ℕ) (h : p + q = n) :
    (normalizedBicomplex C X).ιTotal (ComplexShape.down ℕ) p q n h ≫
        ((totalFunctor C).map f).f n =
      (((normalizedBicomplexFunctor C).map f).f p).f q ≫
        (normalizedBicomplex C Y).ιTotal (ComplexShape.down ℕ) p q n h :=
  HomologicalComplex₂.ιTotal_map _ _ ((normalizedBicomplexFunctor C).map f)
    (ComplexShape.down ℕ) p q n h

end BisimplicialModule

end
