/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Pair
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace SSetPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [HasCokernels (ChainComplex C ℕ)]

/-- The coefficient-natural unnormalized relative chain complex functor.
For `R : C`, this sends a simplicial pair `X = (A ↪ X₀)` to the cokernel of
`C_*(A;R) ⟶ C_*(X₀;R)`. It is defined as the composite

`SSet.chainComplexFunctor C`
`⋙ Functor.mapArrowFunctor`
`⋙ (whiskeringLeft SSetPair.forget)`
`⋙ (whiskeringRight Limits.coker)`,

so naturality and functor laws are inherited from categorical composition. -/
noncomputable def relativeChainComplexFunctor :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  SSet.chainComplexFunctor C ⋙
    Functor.mapArrowFunctor SSet.{w} (ChainComplex C ℕ) ⋙
    (Functor.whiskeringLeft SSetPair.{w} (Arrow SSet.{w}) (Arrow (ChainComplex C ℕ))).obj
      SSetPair.forget ⋙
    (Functor.whiskeringRight SSetPair.{w} (Arrow (ChainComplex C ℕ))
        (ChainComplex C ℕ)).obj
      (Limits.coker (C := ChainComplex C ℕ))

/-- For fixed coefficients `R : C`, the relative chain functor is definitionally
the pipeline `SSetPair.forget` followed by the fixed-coefficient unnormalized
chain functor on arrows and `Limits.coker`. -/
lemma relativeChainComplexFunctor_obj (R : C) :
    (relativeChainComplexFunctor (C := C)).obj R =
      SSetPair.forget ⋙ ((SSet.chainComplexFunctor C).obj R).mapArrow ⋙
        (Limits.coker (C := ChainComplex C ℕ)) :=
  rfl

/-- For fixed coefficients `R : C` and a simplicial pair `X`, the value is
definitionally the cokernel of the unnormalized chain map induced by `X.hom`,
i.e. `cokernel ((SSet.chainComplexFunctor C).obj R).map X.hom`. -/
lemma relativeChainComplexFunctor_obj_obj (R : C) (X : SSetPair.{w}) :
    ((relativeChainComplexFunctor (C := C)).obj R).obj X =
      (Limits.coker (C := ChainComplex C ℕ)).obj
        (Arrow.mk (((SSet.chainComplexFunctor C).obj R).map X.hom)) :=
  rfl

/-- The chain map induced by the subobject inclusion of a simplicial pair. -/
noncomputable abbrev chainInclusion (R : C) (P : SSetPair.{w}) :
    ((SSet.chainComplexFunctor C).obj R).obj P.snd ⟶
      ((SSet.chainComplexFunctor C).obj R).obj P.fst :=
  ((SSet.chainComplexFunctor C).obj R).map P.map

omit [HasCokernels (ChainComplex C ℕ)] in
@[reassoc]
lemma chainInclusion_naturality (R : C) {P Q : SSetPair.{w}} (f : P ⟶ Q) :
    ((SSet.chainComplexFunctor C).obj R).map (Hom.snd f) ≫ chainInclusion C R Q =
      chainInclusion C R P ≫
        ((SSet.chainComplexFunctor C).obj R).map (Hom.fst f) := by
  rw [← Functor.map_comp, ← Functor.map_comp, Hom.w]

/-- The canonical projection from absolute chains to the relative-chain cokernel. -/
noncomputable abbrev relativeChainProjection (R : C) (P : SSetPair.{w}) :
    ((SSet.chainComplexFunctor C).obj R).obj P.fst ⟶
      ((relativeChainComplexFunctor (C := C)).obj R).obj P :=
  cokernel.π (chainInclusion C R P)

@[reassoc (attr := simp)]
lemma chainInclusion_relativeChainProjection (R : C) (P : SSetPair.{w}) :
    chainInclusion C R P ≫ relativeChainProjection C R P = 0 :=
  cokernel.condition _

@[reassoc (attr := simp)]
lemma relativeChainProjection_naturality
    (R : C) {P Q : SSetPair.{w}} (f : P ⟶ Q) :
    relativeChainProjection C R P ≫
        ((relativeChainComplexFunctor (C := C)).obj R).map f =
      ((SSet.chainComplexFunctor C).obj R).map (Hom.fst f) ≫
        relativeChainProjection C R Q := by
  change cokernel.π
        ((SSetPair.forget ⋙ ((SSet.chainComplexFunctor C).obj R).mapArrow).obj P).hom ≫
      (Limits.coker (C := ChainComplex C ℕ)).map
        ((SSetPair.forget ⋙ ((SSet.chainComplexFunctor C).obj R).mapArrow).map f) =
    ((SSetPair.forget ⋙ ((SSet.chainComplexFunctor C).obj R).mapArrow).map f).right ≫
      cokernel.π
        ((SSetPair.forget ⋙ ((SSet.chainComplexFunctor C).obj R).mapArrow).obj Q).hom
  apply cokernel.π_desc

@[reassoc]
lemma relativeChainProjection_naturality_coefficient
    {M M' : C} (a : M ⟶ M') (P : SSetPair.{w}) :
    relativeChainProjection C M P ≫
        ((relativeChainComplexFunctor (C := C)).map a).app P =
      ((SSet.chainComplexFunctor C).map a).app P.fst ≫
        relativeChainProjection C M' P := by
  let h : Arrow.mk (chainInclusion C M P) ⟶
      Arrow.mk (chainInclusion C M' P) :=
    Arrow.homMk
      (((SSet.chainComplexFunctor C).map a).app P.snd)
      (((SSet.chainComplexFunctor C).map a).app P.fst)
      (((SSet.chainComplexFunctor C).map a).naturality P.map).symm
  change cokernel.π (chainInclusion C M P) ≫
      (Limits.coker (C := ChainComplex C ℕ)).map h =
    h.right ≫ cokernel.π (chainInclusion C M' P)
  exact (Limits.coker.π (C := ChainComplex C ℕ)).naturality h |>.symm

end SSetPair
