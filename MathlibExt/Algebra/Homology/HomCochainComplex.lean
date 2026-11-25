/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

public import MathlibExt.Algebra.Homology.HomologyMapSquare

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]

noncomputable def homCochainComplexFunctor (G : C) :
    (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  HomologicalComplex.opFunctor C (ComplexShape.down ℕ) ⋙
    (preadditiveYoneda.obj G).mapHomologicalComplex (ComplexShape.up ℕ)

noncomputable instance homCochainComplexFunctor_additive (G : C) :
    (homCochainComplexFunctor (C := C) G).Additive := by
  change (HomologicalComplex.opFunctor C (ComplexShape.down ℕ) ⋙
    (preadditiveYoneda.obj G).mapHomologicalComplex ((ComplexShape.down ℕ).symm)).Additive
  infer_instance

/-- The contravariant Hom-cochain functor `Hom(-, G)` preserves limits of shape `J`
when `Cᵒᵖ` has limits of that shape. -/
noncomputable instance homCochainComplexFunctor_preservesLimitsOfShape
    {J : Type v} [Category.{v} J] [HasLimitsOfShape J Cᵒᵖ] (G : C) :
    PreservesLimitsOfShape J (homCochainComplexFunctor C G) := by
  have hOp : PreservesLimitsOfShape J (HomologicalComplex.opFunctor C (ComplexShape.down ℕ)) :=
    inferInstance
  have hMap : PreservesLimitsOfShape J
      ((preadditiveYoneda.obj G).mapHomologicalComplex (ComplexShape.up ℕ)) :=
    HomologicalComplex.preservesLimitsOfShape_of_eval
      ((preadditiveYoneda.obj G).mapHomologicalComplex (ComplexShape.up ℕ))
      (fun n => by
        have hEval : PreservesLimitsOfShape J
            (HomologicalComplex.eval Cᵒᵖ (ComplexShape.up ℕ) n) :=
          inferInstance
        have hYoneda : PreservesLimitsOfShape J (preadditiveYoneda.obj G) :=
          inferInstance
        have hComp : PreservesLimitsOfShape J
            (HomologicalComplex.eval Cᵒᵖ (ComplexShape.up ℕ) n ⋙ preadditiveYoneda.obj G) :=
          @CategoryTheory.Limits.comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
            (HomologicalComplex.eval Cᵒᵖ (ComplexShape.up ℕ) n) (preadditiveYoneda.obj G)
            hEval hYoneda
        change PreservesLimitsOfShape J
            (HomologicalComplex.eval Cᵒᵖ (ComplexShape.up ℕ) n ⋙ preadditiveYoneda.obj G)
        exact hComp)
  exact @CategoryTheory.Limits.comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
    (HomologicalComplex.opFunctor C (ComplexShape.down ℕ))
    ((preadditiveYoneda.obj G).mapHomologicalComplex (ComplexShape.up ℕ))
    hOp hMap

noncomputable def homCochainComplexBifunctor :
    C ⥤ ((ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ) where
  obj G := homCochainComplexFunctor C G
  map f := Functor.whiskerLeft
    (HomologicalComplex.opFunctor C (ComplexShape.down ℕ))
    (NatTrans.mapHomologicalComplex
      (preadditiveYoneda.map f) (ComplexShape.up ℕ))

@[simp]
lemma homCochainComplexFunctor_obj_X (G : C)
    (K : ChainComplex C ℕ) (n : ℕ) :
    ((homCochainComplexFunctor C G).obj (Opposite.op K)).X n =
      AddCommGrpCat.of (K.X n ⟶ G) := rfl

/-- Functor `G ↦ H^n(Hom(K, G))` for a fixed chain complex `K`. -/
noncomputable def homCochainComplexHomologyFunctor (K : ChainComplex C ℕ) (n : ℕ) :
    C ⥤ AddCommGrpCat.{v} :=
  homCochainComplexBifunctor C ⋙
    (evaluation _ _).obj (Opposite.op K) ⋙
    homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n

end HomologicalComplex

namespace Homotopy

open HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : ChainComplex C ℕ} {f g : K ⟶ L}

/-- Applying `Hom(-, G)` to chain-homotopic maps gives homotopic cochain maps. -/
noncomputable def mapHomCochainComplex (h : Homotopy f g) (G : C) :
    Homotopy
      ((HomologicalComplex.homCochainComplexFunctor C G).map f.op)
      ((HomologicalComplex.homCochainComplexFunctor C G).map g.op) :=
  (preadditiveYoneda.obj G).mapHomotopy h.op

/-- Chain-homotopic maps induce equal maps on the cohomology of `Hom(-, G)`. -/
lemma homCochainComplex_homologyMap_eq (h : Homotopy f g) (G : C) (n : ℕ)
    [((HomologicalComplex.homCochainComplexFunctor C G).obj
      (Opposite.op L)).HasHomology n]
    [((HomologicalComplex.homCochainComplexFunctor C G).obj
      (Opposite.op K)).HasHomology n] :
    homologyMap
        ((HomologicalComplex.homCochainComplexFunctor C G).map f.op) n =
      homologyMap
        ((HomologicalComplex.homCochainComplexFunctor C G).map g.op) n :=
  (h.mapHomCochainComplex G).homologyMap_eq n

end Homotopy

namespace HomologicalComplex

variable {C D : Type u} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]

noncomputable def homCochainComplexObjIsoOfFullyFaithful
    (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful) (G : C) (K : ChainComplex C ℕ) :
    (homCochainComplexFunctor C G).obj (Opposite.op K) ≅
      (homCochainComplexFunctor D (F.obj G)).obj
        (Opposite.op ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      (AddEquiv.ofBijective (F.mapAddHom (X := K.X n) (Y := G))
        (hF.map_bijective (X := K.X n) (Y := G))).toAddCommGrpIso)
    (fun i j hij => by
      ext f
      let f' : K.X i ⟶ G := f
      change F.map (K.d j i) ≫ F.map f' = F.map (K.d j i ≫ f')
      rw [← F.map_comp])

noncomputable def homCochainComplexFunctorIsoOfFullyFaithful
    (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful) (G : C) :
    homCochainComplexFunctor (C := C) G ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).op ⋙
        homCochainComplexFunctor D (F.obj G) :=
  NatIso.ofComponents
    (fun K => homCochainComplexObjIsoOfFullyFaithful F hF G K.unop)
    (fun {K L} f => by
      ext n g
      let g' : (Opposite.unop K).X n ⟶ G := g
      change F.map (f.unop.f n ≫ g') = F.map (f.unop.f n) ≫ F.map g'
      rw [F.map_comp])

@[simp]
lemma homCochainComplexFunctorIsoOfFullyFaithful_hom_app_f_apply
    (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful) (G : C)
    (K : ChainComplex C ℕ) (n : ℕ) (f : K.X n ⟶ G) :
    ((homCochainComplexFunctorIsoOfFullyFaithful F hF G).hom.app (Opposite.op K)).f n f =
      F.map f := rfl

/-- The fully faithful comparison for Hom-cochains, natural in the target
object as well as in the source chain complex. -/
noncomputable def homCochainComplexBifunctorIsoOfFullyFaithful
    (F : Functor C D) [F.Additive] (hF : F.FullyFaithful) :
    homCochainComplexBifunctor C ≅
      F ⋙ homCochainComplexBifunctor D ⋙
        (Functor.whiskeringLeft
          (ChainComplex C ℕ)ᵒᵖ (ChainComplex D ℕ)ᵒᵖ
          (CochainComplex AddCommGrpCat.{v} ℕ)).obj
            (F.mapHomologicalComplex (ComplexShape.down ℕ)).op :=
  NatIso.ofComponents
    (fun G ↦ homCochainComplexFunctorIsoOfFullyFaithful F hF G)
    (fun {G G'} f ↦ by
      ext K n g
      let g' : K.unop.X n ⟶ G := g
      change F.map (g' ≫ f) = F.map g' ≫ F.map f
      rw [F.map_comp])

end HomologicalComplex
namespace HomologicalComplex.HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : ChainComplex C ℕ}

public noncomputable def mapHomCochainComplex (e : HomotopyEquiv K L) (G : C) :
    HomotopyEquiv ((homCochainComplexFunctor C G).obj (Opposite.op L))
      ((homCochainComplexFunctor C G).obj (Opposite.op K)) where
  hom := (homCochainComplexFunctor C G).map e.hom.op
  inv := (homCochainComplexFunctor C G).map e.inv.op
  homotopyHomInvId := by
    have h := e.homotopyInvHomId.mapHomCochainComplex (G := G)
    simpa [Functor.map_comp, Functor.map_id] using h
  homotopyInvHomId := by
    have h := e.homotopyHomInvId.mapHomCochainComplex (G := G)
    simpa [Functor.map_comp, Functor.map_id] using h

/-- Natural iso `Hⁿ(Hom(L, -)) ≅ Hⁿ(Hom(K, -))` from `e : K ≃ L`, natural in `G`. -/
public noncomputable def homCochainComplexHomologyNatIso {K L : ChainComplex C ℕ}
    (e : HomotopyEquiv K L) (n : ℕ) :
    homCochainComplexHomologyFunctor (C := C) L n ≅
      homCochainComplexHomologyFunctor (C := C) K n :=
  NatIso.ofComponents
    (fun G => (mapHomCochainComplex e G).toHomologyIso n)
    (fun {G G'} f => by
      change
        homologyMap (((homCochainComplexBifunctor C).map f).app
            (Opposite.op L)) n ≫
            homologyMap (((homCochainComplexBifunctor C).obj G').map e.hom.op) n =
          homologyMap (((homCochainComplexBifunctor C).obj G).map e.hom.op) n ≫
            homologyMap (((homCochainComplexBifunctor C).map f).app
                (Opposite.op K)) n
      exact homologyMap_square
        ((((homCochainComplexBifunctor C).map f).naturality e.hom.op).symm) n)

end HomologicalComplex.HomotopyEquiv
