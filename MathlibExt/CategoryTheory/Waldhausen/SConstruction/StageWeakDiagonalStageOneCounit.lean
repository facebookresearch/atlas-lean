/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalStageOneDegeneracy
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneEquivalence

/-!
# Stage-one counit normalization in the weak-stage diagonal

The degree-one `Stage` counit lifts to the pointwise weak-equivalence wide
subcategory.  Its two degree-zero faces agree, after the canonical endpoint
transports, with the coherent Stage-zero contraction.  Combining those face
identifications with the two generic Stage-one degeneracy triangles normalizes
the identity edge of an arbitrary degree-one weak stage to the canonical
object edge of its `(0, 1)` evaluation.

Everything here is combinatorial.  This file makes no arbitrary-edge
normalization, generation, realization, K-zero, additivity, or Q/S claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- The degree-one `Stage` counit lifted through the weak-equivalence wide
subcategory. -/
noncomputable def stageOneCounitWeakIso (A : StageWeakCategory C 1) :
    stageOneWeakObj C ((stageOneEval C).obj A.obj) ≅ A :=
  WideSubcategory.isoMk (counitAppStageIso C A.obj)
    ((stageWeak C 1).of_isIso (counitAppStageIso C A.obj).hom)
    ((stageWeak C 1).of_isIso (counitAppStageIso C A.obj).inv)

/-- The hom of the weak counit has the landed Stage counit as its underlying
Stage morphism. -/
@[simp]
theorem stageOneCounitWeakIso_hom_hom (A : StageWeakCategory C 1) :
    (stageOneCounitWeakIso C A).hom.hom =
      (counitAppStageIso C A.obj).hom :=
  rfl

/-- The inverse of the weak counit has the landed Stage counit inverse as its
underlying Stage morphism. -/
@[simp]
theorem stageOneCounitWeakIso_inv_hom (A : StageWeakCategory C 1) :
    (stageOneCounitWeakIso C A).inv.hom =
      (counitAppStageIso C A.obj).inv :=
  rfl

/-- Naturality of the lifted weak counit.  The proof reuses the landed Stage
counit naturality after forgetting the wide-subcategory data. -/
@[reassoc]
theorem stageOneCounitWeakIso_hom_naturality
    {A B : StageWeakCategory C 1} (f : A ⟶ B) :
    stageOneWeakMap C ((stageOneEval C).map f.hom)
          (f.property (interval (0 : Fin 2) 1 (by decide))) ≫
        (stageOneCounitWeakIso C B).hom =
      (stageOneCounitWeakIso C A).hom ≫ f := by
  apply WideSubcategory.hom_ext
  exact counit_naturality C f.hom

/-- The source face of the weak counit is the coherent Stage-zero contraction,
after transporting its canonical source face to the chosen zero Stage. -/
theorem stageOneCounitWeakIso_reindex_d1_hom
    (A : StageWeakCategory C 1)
    (h := stageOneWeakObj_reindex_d1 C ((stageOneEval C).obj A.obj)) :
    (reindexStageWeak C (SimplexCategory.δ 1)).map
        (stageOneCounitWeakIso C A).hom =
      eqToHom h ≫
        (stageWeakZeroIso C
          ((reindexStageWeak C (SimplexCategory.δ 1)).obj A)).hom := by
  exact stageWeakZero_hom_ext C _ _

/-- The target face of the weak counit is the coherent Stage-zero contraction,
after transporting its canonical target face to the chosen zero Stage. -/
theorem stageOneCounitWeakIso_reindex_d0_hom
    (A : StageWeakCategory C 1)
    (h := stageOneWeakObj_reindex_d0 C ((stageOneEval C).obj A.obj)) :
    (reindexStageWeak C (SimplexCategory.δ 0)).map
        (stageOneCounitWeakIso C A).hom =
      eqToHom h ≫
        (stageWeakZeroIso C
          ((reindexStageWeak C (SimplexCategory.δ 0)).obj A)).hom := by
  exact stageWeakZero_hom_ext C _ _

/-- Source degeneracy relation for the weak counit. -/
theorem stageOneCounitWeakIso_source_homMk_comp
    (A : StageWeakCategory C 1) :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C
          (stageOneWeakObj C ((stageOneEval C).obj A.obj))) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C
          ((reindexStageWeak C (SimplexCategory.δ 0)).map
            (stageOneCounitWeakIso C A).hom)) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalStageOneMapEdge C
        (stageOneCounitWeakIso C A).hom) :=
  stageWeakDiagonalStageOneSource_homMk_comp C
    (stageOneCounitWeakIso C A).hom

/-- Target degeneracy relation for the weak counit. -/
theorem stageOneCounitWeakIso_target_homMk_comp
    (A : StageWeakCategory C 1) :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C
          ((reindexStageWeak C (SimplexCategory.δ 1)).map
            (stageOneCounitWeakIso C A).hom)) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C A) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalStageOneMapEdge C
        (stageOneCounitWeakIso C A).hom) :=
  stageWeakDiagonalStageOneTarget_homMk_comp C
    (stageOneCounitWeakIso C A).hom

/-- The generic identity Stage-one edge on a canonical object stage has the
same underlying simplex as the canonical object edge. -/
@[simp]
theorem stageWeakDiagonalStageOneIdentityEdge_stageOneWeakObj_edge (X : C) :
    (stageWeakDiagonalStageOneIdentityEdge C
        (stageOneWeakObj C X)).edge =
      (stageWeakDiagonalObjectEdge C X).edge :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem stageWeakDiagonalStageOneWeakObjIdentity_normalization
    (X : C) :
    (SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C
          ((reindexStageWeak C (SimplexCategory.δ 1)).obj
            (stageOneWeakObj C X))) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C
          (stageOneWeakObj C X))) ≫
        inv (SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToObjEdge C
            ((reindexStageWeak C (SimplexCategory.δ 0)).obj
              (stageOneWeakObj C X)))) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalObjectEdge C X) := by
  let E := stageOneWeakObj C X
  let Z : StageWeakCategory C 0 := ⟨stageZero C⟩
  have hS : (reindexStageWeak C (SimplexCategory.δ 1)).obj E = Z := by
    change (⟨(reindexStage (C := C) (SimplexCategory.δ 1)).obj
      (stageOneWeakObj C X).obj⟩ : StageWeakCategory C 0) =
      (⟨stageZero C⟩ : StageWeakCategory C 0)
    exact stageOneWeakObj_reindex_d1 C X
  have hT : (reindexStageWeak C (SimplexCategory.δ 0)).obj E = Z := by
    change (⟨(reindexStage (C := C) (SimplexCategory.δ 0)).obj
      (stageOneWeakObj C X).obj⟩ : StageWeakCategory C 0) =
      (⟨stageZero C⟩ : StageWeakCategory C 0)
    exact stageOneWeakObj_reindex_d0 C X
  have hSVertex :
      ComposableArrows.mk₀
          ((reindexStageWeak C (SimplexCategory.δ 1)).obj E) =
        stageWeakDiagonalZeroVertex C :=
    congrArg ComposableArrows.mk₀ hS
  have hTVertex :
      ComposableArrows.mk₀
          ((reindexStageWeak C (SimplexCategory.δ 0)).obj E) =
        stageWeakDiagonalZeroVertex C :=
    congrArg ComposableArrows.mk₀ hT
  have connector_eq_eqToHom : ∀ (T : StageWeakCategory C 0) (h : T = Z),
      SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToObjEdge C T) =
        eqToHom (congrArg SSet.FundamentalGroupoid.mk
          (show stageWeakDiagonalZeroVertex C = ComposableArrows.mk₀ T from
            (congrArg ComposableArrows.mk₀ h).symm)) := by
    intro T h
    subst T
    simp only [Z, stageWeakDiagonalZeroToObjEdge_zero_homMk,
      eqToHom_refl]
  have homMk_ofEq : ∀
      {x₀ x₁ y₀ y₁ : (stageWeakDiagonal C).obj (op ⦋0⦌)}
      (e : SSet.Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁),
      SSet.FundamentalGroupoid.homMk (e.ofEq h₀ h₁) =
        eqToHom (congrArg SSet.FundamentalGroupoid.mk h₀).symm ≫
          SSet.FundamentalGroupoid.homMk e ≫
          eqToHom (congrArg SSet.FundamentalGroupoid.mk h₁) := by
    intro x₀ x₁ y₀ y₁ e h₀ h₁
    cases h₀
    cases h₁
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    congr 1
  have hEdge :
      (stageWeakDiagonalStageOneIdentityEdge C E).ofEq
          hSVertex hTVertex =
        stageWeakDiagonalObjectEdge C X := by
    apply SSet.Edge.ext
    rfl
  have hHom := homMk_ofEq
    (stageWeakDiagonalStageOneIdentityEdge C E) hSVertex hTVertex
  rw [hEdge] at hHom
  rw [connector_eq_eqToHom _ hS, connector_eq_eqToHom _ hT,
    inv_eqToHom]
  simpa only [Category.assoc] using hHom.symm

/-- The identity edge of an arbitrary degree-one weak stage, transported to
the canonical zero vertex by the coherent Stage-zero connectors, is the
canonical object edge of its `(0, 1)` evaluation. -/
theorem stageWeakDiagonalStageOneIdentityEdge_normalization
    (A : StageWeakCategory C 1) :
    (SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C
          ((reindexStageWeak C (SimplexCategory.δ 1)).obj A)) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C A)) ≫
        inv (SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToObjEdge C
            ((reindexStageWeak C (SimplexCategory.δ 0)).obj A))) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalObjectEdge C
          ((stageOneEval C).obj A.obj)) := by
  let X := (stageOneEval C).obj A.obj
  let E := stageOneWeakObj C X
  let ε : E ⟶ A := (stageOneCounitWeakIso C A).hom
  let S₀ := (reindexStageWeak C (SimplexCategory.δ 1)).obj E
  let T₀ := (reindexStageWeak C (SimplexCategory.δ 0)).obj E
  let S := (reindexStageWeak C (SimplexCategory.δ 1)).obj A
  let T := (reindexStageWeak C (SimplexCategory.δ 0)).obj A
  let kS₀ := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C S₀)
  let kT₀ := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C T₀)
  let kS := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C S)
  let kT := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C T)
  let b₁ := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalStageZeroMapEdge C
      ((reindexStageWeak C (SimplexCategory.δ 1)).map ε))
  let b₀ := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalStageZeroMapEdge C
      ((reindexStageWeak C (SimplexCategory.δ 0)).map ε))
  let iE := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalStageOneIdentityEdge C E)
  let iA := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalStageOneIdentityEdge C A)
  let cε := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalStageOneMapEdge C ε)
  let oX := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalObjectEdge C X)
  have hconn₁ : kS₀ ≫ b₁ = kS := by
    simpa only [kS₀, b₁, kS, S₀, S] using
      (stageWeakDiagonalZeroConnector_homMk_comp C
        ((reindexStageWeak C (SimplexCategory.δ 1)).map ε))
  have hconn₀ : kT₀ ≫ b₀ = kT := by
    simpa only [kT₀, b₀, kT, T₀, T] using
      (stageWeakDiagonalZeroConnector_homMk_comp C
        ((reindexStageWeak C (SimplexCategory.δ 0)).map ε))
  have hsource : iE ≫ b₀ = cε := by
    simpa only [iE, b₀, cε, E] using
      (stageOneCounitWeakIso_source_homMk_comp C A)
  have htarget : b₁ ≫ iA = cε := by
    simpa only [b₁, iA, cε] using
      (stageOneCounitWeakIso_target_homMk_comp C A)
  have hcancel₀ : b₀ ≫ inv kT = inv kT₀ := by
    rw [← cancel_epi kT₀]
    rw [← Category.assoc, hconn₀, IsIso.hom_inv_id,
      IsIso.hom_inv_id]
  have hcanonical : (kS₀ ≫ iE) ≫ inv kT₀ = oX := by
    simpa only [kS₀, iE, kT₀, oX, S₀, T₀, E] using
      (stageWeakDiagonalStageOneWeakObjIdentity_normalization C X)
  change (kS ≫ iA) ≫ inv kT = oX
  calc
    (kS ≫ iA) ≫ inv kT =
        ((kS₀ ≫ b₁) ≫ iA) ≫ inv kT := by
          simp only [hconn₁]
    _ = (kS₀ ≫ (b₁ ≫ iA)) ≫ inv kT := by
          simp only [Category.assoc]
    _ = (kS₀ ≫ cε) ≫ inv kT := by rw [htarget]
    _ = (kS₀ ≫ (iE ≫ b₀)) ≫ inv kT := by rw [hsource]
    _ = (kS₀ ≫ iE) ≫ (b₀ ≫ inv kT) := by
          simp only [Category.assoc]
    _ = (kS₀ ≫ iE) ≫ inv kT₀ := by rw [hcancel₀]
    _ = oX := hcanonical

end CategoryTheory.Waldhausen.SConstruction

end
