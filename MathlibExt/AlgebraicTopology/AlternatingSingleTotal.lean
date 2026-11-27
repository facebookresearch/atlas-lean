/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.TotalComplexSingle
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Total complexes of simplicial objects concentrated in a second degree

Let C be preadditive with a zero object and finite coproducts. Replace every term X_n of a
simplicial object by the chain complex concentrated in degree zero, form its alternating-face
bicomplex, and take the direct-sum total. This total is canonically isomorphic to the
alternating-face chain complex of X.

The bicomplex has terms X_p in bidegrees (p, 0) and zero terms in positive second degree. Thus
the total comparison retains X_n in total degree n and its alternating sum of face maps. The
comparisons form a natural isomorphism of functors on simplicial objects.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- Let C be a preadditive category with a zero object and finite coproducts. The functor from
simplicial objects to bicomplexes of shape (down ℕ, down ℕ) first replaces X_n by
ChainComplex.single₀ C (X_n), then forms the alternating-face complex in the simplicial
direction. Its term in bidegree (p, q) is X_p for q = 0 and a zero object otherwise. -/
def alternatingSingleBicomplexFunctor : SimplicialObject C ⥤
    HomologicalComplex₂ C (.down ℕ) (.down ℕ) :=
  (SimplicialObject.whiskering C (ChainComplex C ℕ)).obj (ChainComplex.single₀ C) ⋙
    alternatingFaceMapComplex (ChainComplex C ℕ)

/-- Let C be a preadditive category with a zero object and finite coproducts. This functor sends a
simplicial object X to the direct-sum total of alternatingSingleBicomplexFunctor C applied to
X, using down ℕ in both bicomplex directions and in the total direction. Total degree n sums
the terms with p + q = n. -/
def alternatingSingleTotalFunctor : SimplicialObject C ⥤ ChainComplex C ℕ :=
  alternatingSingleBicomplexFunctor C ⋙
    HomologicalComplex₂.totalFunctor C (.down ℕ) (.down ℕ) (.down ℕ)

/-- Let C be a preadditive category with a zero object and finite coproducts. For every simplicial
object X, there is a chain-complex isomorphism from its concentrated alternating-face
bicomplex total to alternatingFaceMapComplex C applied to X. It is the composite of the
alternating-face comparison for the single-degree-zero functor with the total comparison for a
bicomplex supported in second degree zero. -/
def alternatingSingleTotalIso (X : SimplicialObject C) :
    (alternatingSingleTotalFunctor C).obj X ≅ (alternatingFaceMapComplex C).obj X :=
  (HomologicalComplex₂.totalFunctor C (.down ℕ) (.down ℕ) (.down ℕ)).mapIso
      (((alternatingFaceMapComplexCompMapHomologicalComplexIso (ChainComplex.single₀ C)).app X).symm) ≪≫
    HomologicalComplex₂.single₀MapTotalIso ((alternatingFaceMapComplex C).obj X)

/-- Let C be a preadditive category with a zero object and finite coproducts. For a simplicial map
f : X ⟶ Y, let e_X and e_Y denote alternatingSingleTotalIso C at X and Y. Then
alternatingSingleTotalFunctor.map f ≫ e_Y.hom = e_X.hom ≫ alternatingFaceMapComplex.map f.
Both sides are maps from the total for X to the alternating-face complex of Y. -/
@[reassoc]
theorem alternatingSingleTotalIso_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (alternatingSingleTotalFunctor C).map f ≫ (alternatingSingleTotalIso C Y).hom =
      (alternatingSingleTotalIso C X).hom ≫ (alternatingFaceMapComplex C).map f := by
  let T := HomologicalComplex₂.totalFunctor C (.down ℕ) (.down ℕ) (.down ℕ)
  let H := alternatingSingleBicomplexFunctor C
  let a := alternatingFaceMapComplexCompMapHomologicalComplexIso (ChainComplex.single₀ C)
  let F := alternatingFaceMapComplex C
  have h : T.map (H.map f) ≫ T.map (a.app Y).inv =
      T.map (a.app X).inv ≫ T.map (HomologicalComplex₂.singleMapBicomplexFunctorDownNat.map (F.map f)) := by
    have ha : H.map f ≫ (a.app Y).inv =
        (a.app X).inv ≫ HomologicalComplex₂.singleMapBicomplexFunctorDownNat.map (F.map f) :=
      a.inv.naturality f
    exact (T.map_comp (H.map f) (a.app Y).inv).symm.trans
      ((congrArg T.map ha).trans
        (T.map_comp (a.app X).inv (HomologicalComplex₂.singleMapBicomplexFunctorDownNat.map (F.map f))))
  have hs := HomologicalComplex₂.singleMapTotalIsoDownNat_hom_naturality (F.map f)
  change T.map (H.map f) ≫ (T.map (a.app Y).inv ≫ (HomologicalComplex₂.single₀MapTotalIso (F.obj Y)).hom) =
    (T.map (a.app X).inv ≫ (HomologicalComplex₂.single₀MapTotalIso (F.obj X)).hom) ≫ F.map f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (HomologicalComplex₂.single₀MapTotalIso (F.obj Y)).hom) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => T.map (a.app X).inv ≫ t) hs).trans (Category.assoc _ _ _).symm)))

/-- Let C be a preadditive category with a zero object and finite coproducts. The isomorphisms
alternatingSingleTotalIso C X, from the direct-sum total of the concentrated alternating-face
bicomplex to the alternating-face complex of X, form a natural isomorphism
alternatingSingleTotalFunctor C ≅ alternatingFaceMapComplex C. -/
def alternatingSingleTotalNatIso : alternatingSingleTotalFunctor C ≅ alternatingFaceMapComplex C :=
  NatIso.ofComponents (alternatingSingleTotalIso C) (alternatingSingleTotalIso_naturality C)

end AlgebraicTopology
