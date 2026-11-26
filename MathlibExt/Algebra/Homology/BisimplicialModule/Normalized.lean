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
# Double normalization and horizontal filtration of bisimplicial objects

For a bisimplicial object in an abelian category C, normalize the inner simplicial direction
and then the outer direction. This gives a first-quadrant commuting bicomplex K_{p,q}. Its
total has degree-n object ⊕_{p+q=n}K_{p,q} and differential d_h + (−1)^p d_v on the summand of
horizontal degree p, following the tensor signs for homological complexes.

The complete horizontal filtration and the extended-integer partial-total tower retain the
normalized component maps, with zero bottom stage and the total complex at the top.
Normalizing the diagonal gives a separate chain-complex functor. Moore normalization is a
retract of the alternating-face complex, so degreewise projective simplicial objects yield
degreewise projective normalized objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped ZeroObject

universe u v

namespace BisimplicialModule

variable (C : Type u) [Category.{v} C]


variable [Abelian C]

/-- The Moore normalization retract of the alternating-face complex.

The normalized Moore complex includes into the alternating-face complex and retracts by the
Dold–Kan projection, with retraction composed with inclusion equal to the identity. -/
def normalizationRetract (X : SimplicialObject C) :
    Retract ((normalizedMooreComplex C).obj X) ((alternatingFaceMapComplex C).obj X) where
  i := inclusionOfMooreComplexMap X
  r := DoldKan.PInftyToNormalizedMooreComplex X
  retract := (DoldKan.splitMonoInclusionOfMooreComplexMap X).id

/-- Projectivity of normalized simplicial degrees.

If every simplicial degree of X is projective in C, then every degree of its normalized Moore
complex is projective, by the normalization retract. -/
theorem normalizedDegree_projective (X : SimplicialObject C)
    (hX : ∀ n : ℕ, Projective (X.obj (Opposite.op (SimplexCategory.mk n)))) (n : ℕ) :
    Projective (((normalizedMooreComplex C).obj X).X n) := by
  have hP : Projective ((HomologicalComplex.eval C (ComplexShape.down ℕ) n).obj
      ((alternatingFaceMapComplex C).obj X)) := by
    change Projective (X.obj (Opposite.op (SimplexCategory.mk n)))
    exact hX n
  exact ((normalizationRetract C X).map
    (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).projective (p := hP)

/-- Double Moore normalization of a bisimplicial object.

Normalize the inner simplicial variable, then normalize the outer variable in the category of
chain complexes, obtaining a commuting bicomplex indexed by ℕ × ℕ. -/
def normalizedBicomplexFunctor :
    SimplicialObject (SimplicialObject C) ⥤
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (SimplicialObject.whiskering (SimplicialObject C) (ChainComplex C ℕ)).obj
      (normalizedMooreComplex C) ⋙ normalizedMooreComplex (ChainComplex C ℕ)

/-- The double-normalized bicomplex of one bisimplicial object.

This is the value of normalizedBicomplexFunctor at X, with the outer normalized degree first
and inner normalized degree second. -/
abbrev normalizedBicomplex (X : SimplicialObject (SimplicialObject C)) :=
  (normalizedBicomplexFunctor C).obj X

/-- Projectivity of double-normalized components.

If every raw bidegree X_{p,q} is projective, every bidegree of the double-normalized bicomplex
is projective, by applying the two normalization retracts. -/
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

/-- The total chain complex of double normalization.

Take the finite antidiagonal coproducts of the double-normalized bicomplex, with differential
d_h + (−1)^p d_v on horizontal degree p. -/
def totalFunctor : SimplicialObject (SimplicialObject C) ⥤ ChainComplex C ℕ :=
  normalizedBicomplexFunctor C ⋙
    HomologicalComplex₂.totalFunctor C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- The complete horizontal filtration of the normalized total.

Apply the complete horizontal total-filtration functor to double normalization, giving an
extended-integer filtered chain complex. -/
def filteredTotalFunctor :
    SimplicialObject (SimplicialObject C) ⥤ FilteredObject (ChainComplex C ℕ) EInt :=
  normalizedBicomplexFunctor C ⋙
    HomologicalComplex₂.horizontalCompleteTotalFilteredObjectFunctor

/-- The extended-integer partial-total tower.

For X, take the partial-total filtration of its double-normalized bicomplex, as a functor from
EInt to chain complexes. -/
abbrev partialTotalFiltration (X : SimplicialObject (SimplicialObject C)) :
    EInt ⥤ ChainComplex C ℕ :=
  (normalizedBicomplex C X).partialTotalEIntFiltration

/-- The bottom stage of the bisimplicial partial-total tower.

The extended-integer bottom stage is the zero chain complex. -/
theorem partialTotalFiltration_bot (X : SimplicialObject (SimplicialObject C)) :
    (partialTotalFiltration C X).obj ⊥ = 0 :=
  HomologicalComplex₂.partialTotalEIntFiltration_obj_bot _

/-- The top stage of the bisimplicial partial-total tower.

The extended-integer top stage is the total complex of the double-normalized bicomplex. -/
theorem partialTotalFiltration_top (X : SimplicialObject (SimplicialObject C)) :
    (partialTotalFiltration C X).obj ⊤ = (totalFunctor C).obj X :=
  HomologicalComplex₂.partialTotalEIntFiltration_obj_top _

/-- The normalized chain complex of a bisimplicial diagonal.

Take the simplicial diagonal n ↦ X_{n,n} and then its normalized Moore complex. -/
def diagonalChainFunctor : SimplicialObject (SimplicialObject C) ⥤ ChainComplex C ℕ :=
  diagonalFunctor C ⋙ normalizedMooreComplex C

/-- The normalized total map on an antidiagonal coprojection.

For p+q=n, the coprojection into the source total followed by the degree-n total map equals
the bidegree-(p,q) normalized map followed by the target coprojection. -/
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
