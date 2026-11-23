/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntExact
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerGrading

/-!
# Integer-graded singular pair sequences
-/

@[expose] public section

open CategoryTheory Category Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Transport the functorial singular-pair short complex from natural grading to the
zero-extended integer grading. -/
noncomputable def singularPairShortComplexIntFunctor (R : C) :
    TopPair.{w} ⥤ ShortComplex (ChainComplex C ℤ) :=
  singularPairShortComplexFunctor C R ⋙
    (ComplexShape.embeddingDownNatToIntExtendFunctor C).mapShortComplex

/-- First term is the integer singular chains of the subspace. -/
lemma singularPairShortComplexIntFunctor_obj_X₁ (R : C) (P : TopPair.{w}) :
    ((singularPairShortComplexIntFunctor C R).obj P).X₁ =
      (singularChainIntFunctor C R).obj P.snd :=
  rfl

/-- Second term is the integer singular chains of the ambient space. -/
lemma singularPairShortComplexIntFunctor_obj_X₂ (R : C) (P : TopPair.{w}) :
    ((singularPairShortComplexIntFunctor C R).obj P).X₂ =
      (singularChainIntFunctor C R).obj P.fst :=
  rfl

/-- Third term is the integer relative chains. -/
lemma singularPairShortComplexIntFunctor_obj_X₃ (R : C) (P : TopPair.{w}) :
    ((singularPairShortComplexIntFunctor C R).obj P).X₃ =
      (relativeSingularChainIntFunctor C R).obj P :=
  rfl

lemma singularPairShortComplexIntFunctor_map_τ₁ (R : C) {P Q : TopPair.{w}} (f : P ⟶ Q) :
    ((singularPairShortComplexIntFunctor C R).map f).τ₁ =
      (singularChainIntFunctor C R).map (TopPair.Hom.snd f) :=
  rfl

lemma singularPairShortComplexIntFunctor_map_τ₂ (R : C) {P Q : TopPair.{w}} (f : P ⟶ Q) :
    ((singularPairShortComplexIntFunctor C R).map f).τ₂ =
      (singularChainIntFunctor C R).map (TopPair.Hom.fst f) :=
  rfl

lemma singularPairShortComplexIntFunctor_map_τ₃ (R : C) {P Q : TopPair.{w}} (f : P ⟶ Q) :
    ((singularPairShortComplexIntFunctor C R).map f).τ₃ =
      (relativeSingularChainIntFunctor C R).map f :=
  rfl

lemma singularPairShortComplexIntFunctor_obj_shortExact (R : C) (P : TopPair.{w}) :
    ((singularPairShortComplexIntFunctor C R).obj P).ShortExact := by
  change (((singularPairShortComplexFunctor C R).obj P).map
      (ComplexShape.embeddingDownNatToIntExtendFunctor C)).ShortExact
  apply ShortComplex.ShortExact.map_embeddingDownNatToIntExtend
  exact singularPairShortComplex_shortExact C R P

end AlgebraicTopology
