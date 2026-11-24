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
# Totals of alternating single-zero diagrams

Applying the single-zero chain functor to a simplicial
object and totalizing its alternating-face bicomplex
gives its alternating-face chain complex. The object
comparison and its functorial form use the same
single-zero total isomorphism.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- The original alternating-face bicomplex of the native single-zero simplicial objects. -/
def alternatingSingleBicomplexFunctor : SimplicialObject C ⥤
    HomologicalComplex₂ C (.down ℕ) (.down ℕ) :=
  (SimplicialObject.whiskering C (ChainComplex C ℕ)).obj (ChainComplex.single₀ C) ⋙
    alternatingFaceMapComplex (ChainComplex C ℕ)

/-- The native direct-sum total of that original bicomplex diagram. -/
def alternatingSingleTotalFunctor : SimplicialObject C ⥤ ChainComplex C ℕ :=
  alternatingSingleBicomplexFunctor C ⋙
    HomologicalComplex₂.totalFunctor C (.down ℕ) (.down ℕ) (.down ℕ)

/-- Native additive-functor comparison followed by the original single-zero total isomorphism. -/
def alternatingSingleTotalIso (X : SimplicialObject C) :
    (alternatingSingleTotalFunctor C).obj X ≅ (alternatingFaceMapComplex C).obj X :=
  (HomologicalComplex₂.totalFunctor C (.down ℕ) (.down ℕ) (.down ℕ)).mapIso
      (((alternatingFaceMapComplexCompMapHomologicalComplexIso (ChainComplex.single₀ C)).app X).symm) ≪≫
    HomologicalComplex₂.single₀MapTotalIso ((alternatingFaceMapComplex C).obj X)

/-- Every original simplicial morphism preserves this exact native total comparison. -/
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

/-- The total of single-zero simplicial columns is the original alternating-face complex
as a native functor isomorphism. -/
def alternatingSingleTotalNatIso : alternatingSingleTotalFunctor C ≅ alternatingFaceMapComplex C :=
  NatIso.ofComponents (alternatingSingleTotalIso C) (alternatingSingleTotalIso_naturality C)

end AlgebraicTopology
