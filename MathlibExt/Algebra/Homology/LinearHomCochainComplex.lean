/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Opposite
public import MathlibExt.CategoryTheory.Linear.Yoneda.Limits
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
universe w v u vJ uJ
namespace HomologicalComplex

variable (R : Type w) [Ring R]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]

noncomputable def linearHomCochainComplexFunctor (G : C) :
    (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  HomologicalComplex.opFunctor C (ComplexShape.down ℕ) ⋙
    ((linearYoneda R C).obj G).mapHomologicalComplex (ComplexShape.up ℕ)

noncomputable instance linearHomCochainComplexFunctor_additive (G : C) :
    (linearHomCochainComplexFunctor R C G).Additive := by
  change (HomologicalComplex.opFunctor C (ComplexShape.down ℕ) ⋙
    ((linearYoneda R C).obj G).mapHomologicalComplex ((ComplexShape.down ℕ).symm)).Additive
  infer_instance

/-- The contravariant linear Hom-cochain functor preserves limits whenever
the opposite source category has them. -/
noncomputable instance
    linearHomCochainComplexFunctor_preservesLimitsOfShape
    {J : Type uJ} [Category.{vJ} J] [HasLimitsOfShape J Cᵒᵖ]
    (G : C) :
    PreservesLimitsOfShape J
      (linearHomCochainComplexFunctor R C G) := by
  have hOp : PreservesLimitsOfShape J
      (HomologicalComplex.opFunctor C (ComplexShape.down ℕ)) :=
    inferInstance
  have hMap : PreservesLimitsOfShape J
      (((linearYoneda R C).obj G).mapHomologicalComplex
        (ComplexShape.up ℕ)) :=
    HomologicalComplex.preservesLimitsOfShape_of_eval
      (((linearYoneda R C).obj G).mapHomologicalComplex
        (ComplexShape.up ℕ))
      (fun n => by
        have hEval : PreservesLimitsOfShape J
            (HomologicalComplex.eval Cᵒᵖ
              (ComplexShape.up ℕ) n) :=
          inferInstance
        have hYoneda : PreservesLimitsOfShape J
            ((linearYoneda R C).obj G) :=
          inferInstance
        have hComp : PreservesLimitsOfShape J
            (HomologicalComplex.eval Cᵒᵖ
                (ComplexShape.up ℕ) n ⋙
              (linearYoneda R C).obj G) :=
          @CategoryTheory.Limits.comp_preservesLimitsOfShape
            _ _ _ _ _ _ _ _
            (HomologicalComplex.eval Cᵒᵖ
              (ComplexShape.up ℕ) n)
            ((linearYoneda R C).obj G) hEval hYoneda
        change PreservesLimitsOfShape J
          (HomologicalComplex.eval Cᵒᵖ
              (ComplexShape.up ℕ) n ⋙
            (linearYoneda R C).obj G)
        exact hComp)
  exact @CategoryTheory.Limits.comp_preservesLimitsOfShape
    _ _ _ _ _ _ _ _
    (HomologicalComplex.opFunctor C (ComplexShape.down ℕ))
    (((linearYoneda R C).obj G).mapHomologicalComplex
      (ComplexShape.up ℕ)) hOp hMap
noncomputable def linearHomCochainComplexBifunctor :
    C ⥤ ((ChainComplex C ℕ)ᵒᵖ ⥤
      CochainComplex (ModuleCat.{v} R) ℕ) where
  obj G := linearHomCochainComplexFunctor R C G
  map f := Functor.whiskerLeft
    (HomologicalComplex.opFunctor C (ComplexShape.down ℕ))
    (NatTrans.mapHomologicalComplex
      ((linearYoneda R C).map f) (ComplexShape.up ℕ))

@[simp]
lemma linearHomCochainComplexFunctor_obj_X (G : C)
    (K : ChainComplex C ℕ) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C G).obj (Opposite.op K)).X n =
      ModuleCat.of R (K.X n ⟶ G) := rfl

/-- Functor `G ↦ H^n(Hom_R(K, G))` for a fixed chain complex `K`. -/
noncomputable def linearHomCochainComplexHomologyFunctor
    (K : ChainComplex C ℕ) (n : ℕ) : C ⥤ ModuleCat.{v} R :=
  linearHomCochainComplexBifunctor R C ⋙
    (evaluation _ _).obj (Opposite.op K) ⋙
    homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℕ) n

end HomologicalComplex

namespace Homotopy

open HomologicalComplex

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {K L : ChainComplex C ℕ} {f g : K ⟶ L}

/-- Applying the linear Yoneda functor `Hom(-, G)` to chain-homotopic maps
gives homotopic linear Hom-cochain maps. -/
noncomputable def mapLinearHomCochainComplex (h : Homotopy f g) (G : C) :
    Homotopy
      ((linearHomCochainComplexFunctor R C G).map f.op)
      ((linearHomCochainComplexFunctor R C G).map g.op) :=
  ((linearYoneda R C).obj G).mapHomotopy h.op

/-- Chain-homotopic maps induce equal maps on the cohomology of linear
Hom-cochains. -/
lemma linearHomCochainComplex_homologyMap_eq
    (h : Homotopy f g) (G : C) (n : ℕ)
    [((linearHomCochainComplexFunctor R C G).obj (Opposite.op L)).HasHomology n]
    [((linearHomCochainComplexFunctor R C G).obj (Opposite.op K)).HasHomology n] :
    homologyMap ((linearHomCochainComplexFunctor R C G).map f.op) n =
      homologyMap ((linearHomCochainComplexFunctor R C G).map g.op) n :=
  (h.mapLinearHomCochainComplex R G).homologyMap_eq n

end Homotopy
