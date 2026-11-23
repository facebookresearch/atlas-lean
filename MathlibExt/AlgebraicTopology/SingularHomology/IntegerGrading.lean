/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Algebra.Homology.Embedding.DownNatToInt
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeHomology

/-!
# Integer-graded singular homology

This file extends the nonnegative singular and relative singular chain complexes
to homological complexes indexed by the integers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Singular chains extended by zero from nonnegative to integer degrees. -/
noncomputable def singularChainIntFunctor (R : C) :
    TopCat.{w} ⥤ ChainComplex C ℤ :=
  (singularChainComplexFunctor C).obj R ⋙
    ComplexShape.embeddingDownNatToIntExtendFunctor C

/-- Relative singular chains extended by zero from nonnegative to integer degrees. -/
noncomputable def relativeSingularChainIntFunctor (R : C) :
    TopPair.{w} ⥤ ChainComplex C ℤ :=
  relativeSingularChainFunctor C R ⋙
    ComplexShape.embeddingDownNatToIntExtendFunctor C

/-- The quotient from absolute to relative singular chains, extended to integer grading. -/
noncomputable def relativeSingularChainIntQuotientNatTrans (R : C) :
    TopPair.proj₁ ⋙ singularChainIntFunctor C R ⟶
      relativeSingularChainIntFunctor C R := by
  change (TopPair.proj₁ ⋙ (singularChainComplexFunctor C).obj R) ⋙
      ComplexShape.embeddingDownNatToIntExtendFunctor C ⟶
    relativeSingularChainFunctor C R ⋙
      ComplexShape.embeddingDownNatToIntExtendFunctor C
  exact Functor.whiskerRight (relativeSingularChainQuotientNatTrans C R)
    (ComplexShape.embeddingDownNatToIntExtendFunctor C)

/-- Objectwise quotient from absolute to relative singular chains in integer grading. -/
noncomputable def relativeSingularChainIntQuotient (R : C) (P : TopPair.{w}) :
    (singularChainIntFunctor C R).obj P.fst ⟶
      (relativeSingularChainIntFunctor C R).obj P :=
  (relativeSingularChainIntQuotientNatTrans C R).app P

@[reassoc]
theorem relativeSingularChainIntQuotient_naturality (R : C)
    {P Q : TopPair.{w}} (f : P ⟶ Q) :
    relativeSingularChainIntQuotient C R P ≫
        (relativeSingularChainIntFunctor C R).map f =
      (singularChainIntFunctor C R).map (TopPair.Hom.fst f) ≫
        relativeSingularChainIntQuotient C R Q :=
  (relativeSingularChainIntQuotientNatTrans C R).naturality f |>.symm

theorem singularChainIntMap_comp_relativeSingularChainIntQuotient
    (R : C) (P : TopPair.{w}) :
    (singularChainIntFunctor C R).map P.map ≫
      relativeSingularChainIntQuotient C R P = 0 := by
  change (ComplexShape.embeddingDownNatToIntExtendFunctor C).map
      (((singularChainComplexFunctor C).obj R).map P.map) ≫
    (ComplexShape.embeddingDownNatToIntExtendFunctor C).map
      (relativeSingularChainQuotient C R P) = 0
  rw [← Functor.map_comp]
  have h := ((singularPairCokernelSequenceFunctor C R).obj P).zero
  change (((singularChainComplexFunctor C).obj R).map P.map) ≫
    relativeSingularChainQuotient C R P = 0 at h
  rw [h]
  change (ComplexShape.embeddingDownNatToInt.extendFunctor C).map 0 = 0
  rw [Functor.map_zero]

/-- Integer-graded singular homology in a fixed degree. -/
noncomputable def singularHomologyIntFunctor (R : C) (z : ℤ) : TopCat.{w} ⥤ C :=
  singularChainIntFunctor C R ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) z

/-- Integer-graded relative singular homology in a fixed degree. -/
noncomputable def relativeSingularHomologyIntFunctor (R : C) (z : ℤ) : TopPair.{w} ⥤ C :=
  relativeSingularChainIntFunctor C R ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) z

/-- Nonnegative singular homology agrees with its integer-graded zero extension. -/
noncomputable def singularHomologyNatToIntIso (R : C) (n : ℕ) :
    singularHomologyIntFunctor C R (n : ℤ) ≅
      (singularHomologyFunctor C n).obj R :=
  NatIso.ofComponents
    (fun X => homologyIsoExtendDownNatToInt
      (((singularChainComplexFunctor C).obj R).obj X) n)
    (fun {X Y} f => by
      exact homologyIso_extendDownNatToInt_naturality
        (((singularChainComplexFunctor C).obj R).map f) n)

/-- Nonnegative relative singular homology agrees with its integer-graded zero extension. -/
noncomputable def relativeSingularHomologyNatToIntIso (R : C) (n : ℕ) :
    relativeSingularHomologyIntFunctor C R (n : ℤ) ≅
      relativeSingularHomologyFunctor C R n :=
  NatIso.ofComponents
    (fun P => homologyIsoExtendDownNatToInt
      ((relativeSingularChainFunctor C R).obj P) n)
    (fun {P Q} f => by
      exact homologyIso_extendDownNatToInt_naturality
        ((relativeSingularChainFunctor C R).map f) n)

/-- The Nat-to-Int singular and relative singular homology isomorphisms
intertwine the homology map induced by the relative-chain quotient. -/
public theorem singularHomologyNatToIntIso_relativeQuotient
    (R : C) (P : TopPair.{w}) (n : ℕ) :
    ((singularHomologyNatToIntIso C R n).app P.fst).hom ≫
        HomologicalComplex.homologyMap
          (relativeSingularChainQuotient C R P) n =
      HomologicalComplex.homologyMap
          (relativeSingularChainIntQuotient C R P) (n : ℤ) ≫
        ((relativeSingularHomologyNatToIntIso C R n).app P).hom := by
  change
    (homologyIsoExtendDownNatToInt
      (((singularChainComplexFunctor C).obj R).obj P.fst) n).hom ≫
        HomologicalComplex.homologyMap
          (relativeSingularChainQuotient C R P) n =
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (relativeSingularChainQuotient C R P)
          ComplexShape.embeddingDownNatToInt) (n : ℤ) ≫
        (homologyIsoExtendDownNatToInt
          ((relativeSingularChainFunctor C R).obj P) n).hom
  exact (homologyIso_extendDownNatToInt_naturality
    (relativeSingularChainQuotient C R P) n).symm

theorem isZero_singularHomologyIntFunctor_of_neg
    (R : C) (z : ℤ) (hz : z < 0) (X : TopCat.{w}) :
    IsZero ((singularHomologyIntFunctor C R z).obj X) :=
  isZero_homology_extendDownNatToInt_neg
    (((singularChainComplexFunctor C).obj R).obj X) z hz

theorem isZero_relativeSingularHomologyIntFunctor_of_neg
    (R : C) (z : ℤ) (hz : z < 0) (P : TopPair.{w}) :
    IsZero ((relativeSingularHomologyIntFunctor C R z).obj P) :=
  isZero_homology_extendDownNatToInt_neg
    ((relativeSingularChainFunctor C R).obj P) z hz

end AlgebraicTopology
