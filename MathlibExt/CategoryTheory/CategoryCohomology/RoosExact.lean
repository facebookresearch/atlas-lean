/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Exactness of the Roos complex functor

In an abelian category with correctly sized exact products, a short exact
sequence of coefficient diagrams gives a short exact sequence of Roos cochain
complexes. The product comparison and its coefficient naturality reduce the
statement to degreewise exactness. The construction requires the exact-product
hypothesis, independently of injective resolutions or diagram limits.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A]

private abbrev roosDegreeIndexFunctor (n : ℕ) :
    Discrete (ComposableArrows Iᵒᵖ n) ⥤ I :=
  Discrete.functor fun F ↦ F.left.unop

private abbrev roosDegreePrecompFunctor (n : ℕ) :
    (I ⥤ A) ⥤ Discrete (ComposableArrows Iᵒᵖ n) ⥤ A :=
  (Functor.whiskeringLeft (Discrete (ComposableArrows Iᵒᵖ n)) I A).obj
    (roosDegreeIndexFunctor (I := I) n)

section ProductPresentation

variable [Preadditive A] [HasProducts.{max u₁ v₁} A]

private def roosDegreeObjIso (M : I ⥤ A) (n : ℕ) :
    (roosComplex M).X n ≅ limit (roosDegreeIndexFunctor (I := I) n ⋙ M) :=
  roosObjIso M n ≪≫
    (HasLimit.isoOfNatIso
      (Discrete.compNatIsoDiscrete
        (fun F : ComposableArrows Iᵒᵖ n ↦ F.left.unop) M)).symm

private theorem roosDegreeObjIso_hom_π (M : I ⥤ A) (n : ℕ)
    (F : Discrete (ComposableArrows Iᵒᵖ n)) :
    (roosDegreeObjIso M n).hom ≫
        limit.π (roosDegreeIndexFunctor (I := I) n ⋙ M) F = roosπ M F.as := by
  let D : Discrete (ComposableArrows Iᵒᵖ n) ⥤ A :=
    roosDegreeIndexFunctor (I := I) n ⋙ M
  let G : Discrete (ComposableArrows Iᵒᵖ n) ⥤ A :=
    Discrete.functor (roosFamily M n)
  let η : D ≅ G :=
    Discrete.compNatIsoDiscrete
      (fun F : ComposableArrows Iᵒᵖ n ↦ F.left.unop) M
  let e : (roosComplex M).X n ≅ ∏ᶜ (roosFamily M n) := roosObjIso M n
  let t : (∏ᶜ (roosFamily M n)) ≅ limit D := (HasLimit.isoOfNatIso η).symm
  let π : limit D ⟶ M.obj F.as.left.unop := limit.π D F
  let p : (∏ᶜ (roosFamily M n)) ⟶ M.obj F.as.left.unop :=
    Pi.π (roosFamily M n) F.as
  have hIso : (roosDegreeObjIso M n).hom = e.hom ≫ t.hom :=
    Iso.trans_hom e t
  have ht : t.hom = (HasLimit.isoOfNatIso η).inv :=
    Iso.symm_hom (HasLimit.isoOfNatIso η)
  have hη : η.inv.app F = 𝟙 (M.obj F.as.left.unop) := rfl
  have hπ : t.hom ≫ π = p :=
    (congrArg (fun k : (∏ᶜ (roosFamily M n)) ⟶ limit D => k ≫ π) ht).trans
      ((HasLimit.isoOfNatIso_inv_π η F).trans
        ((congrArg (fun k : M.obj F.as.left.unop ⟶ M.obj F.as.left.unop => p ≫ k)
          hη).trans (Category.comp_id p)))
  change (roosDegreeObjIso M n).hom ≫ π = roosπ M F.as
  have hR : e.hom ≫ p = roosπ M F.as := roosObjIso_hom_π M F.as
  exact (congrArg (fun k : (roosComplex M).X n ⟶ limit D => k ≫ π) hIso).trans
    ((Category.assoc e.hom t.hom π).trans
      ((congrArg (fun k : (∏ᶜ (roosFamily M n)) ⟶ M.obj F.as.left.unop => e.hom ≫ k)
        hπ).trans hR))

private def roosDegreeLimitIso (n : ℕ) :
    (roosComplexFunctor (I := I) (A := A) ⋙
      HomologicalComplex.eval A (ComplexShape.up ℕ) n) ≅
    (roosDegreePrecompFunctor (I := I) (A := A) n ⋙
      lim (J := Discrete (ComposableArrows Iᵒᵖ n)) (C := A)) :=
  NatIso.ofComponents (fun M ↦ roosDegreeObjIso M n)
    (fun {M N} α ↦ by
      change ((roosComplexFunctor (I := I) (A := A)).map α).f n ≫
          (roosDegreeObjIso N n).hom =
        (roosDegreeObjIso M n).hom ≫
          (lim (J := Discrete (ComposableArrows Iᵒᵖ n)) (C := A)).map
            ((roosDegreePrecompFunctor (I := I) (A := A) n).map α)
      apply limit.hom_ext
      intro F
      let DM : Discrete (ComposableArrows Iᵒᵖ n) ⥤ A :=
        roosDegreeIndexFunctor (I := I) n ⋙ M
      let DN : Discrete (ComposableArrows Iᵒᵖ n) ⥤ A :=
        roosDegreeIndexFunctor (I := I) n ⋙ N
      let f : (roosComplex M).X n ⟶ (roosComplex N).X n :=
        ((roosComplexFunctor (I := I) (A := A)).map α).f n
      let eM : (roosComplex M).X n ⟶ limit DM := (roosDegreeObjIso M n).hom
      let eN : (roosComplex N).X n ⟶ limit DN := (roosDegreeObjIso N n).hom
      let m : limit DM ⟶ limit DN :=
        (lim (J := Discrete (ComposableArrows Iᵒᵖ n)) (C := A)).map
          ((roosDegreePrecompFunctor (I := I) (A := A) n).map α)
      let πM : limit DM ⟶ M.obj F.as.left.unop := limit.π DM F
      let πN : limit DN ⟶ N.obj F.as.left.unop := limit.π DN F
      have hM : eM ≫ πM = roosπ M F.as := roosDegreeObjIso_hom_π M n F
      have hN : eN ≫ πN = roosπ N F.as := roosDegreeObjIso_hom_π N n F
      have hF : f ≫ roosπ N F.as = roosπ M F.as ≫ α.app F.as.left.unop := by
        have h := congrArg
          (fun k : (roosCosimplicial M).obj (SimplexCategory.mk n) ⟶
            (roosCosimplicial N).obj (SimplexCategory.mk n) => k ≫ roosπ N F.as)
          (roosComplexFunctor_map_f α n)
        exact h.trans (roosMap_app_π α F.as)
      have hα : ((roosDegreePrecompFunctor (I := I) (A := A) n).map α).app F =
          α.app F.as.left.unop := rfl
      have hm : m ≫ πN = πM ≫ α.app F.as.left.unop :=
        (limit.map_π ((roosDegreePrecompFunctor (I := I) (A := A) n).map α) F).trans
          (congrArg (fun k : M.obj F.as.left.unop ⟶ N.obj F.as.left.unop => πM ≫ k) hα)
      change (f ≫ eN) ≫ πN = (eM ≫ m) ≫ πN
      have hLeft : (f ≫ eN) ≫ πN = roosπ M F.as ≫ α.app F.as.left.unop :=
        (Category.assoc f eN πN).trans
          ((congrArg (fun k : (roosComplex N).X n ⟶ N.obj F.as.left.unop => f ≫ k)
            hN).trans hF)
      have hRight : (eM ≫ m) ≫ πN = roosπ M F.as ≫ α.app F.as.left.unop :=
        (Category.assoc eM m πN).trans
          ((congrArg (fun k : limit DM ⟶ N.obj F.as.left.unop => eM ≫ k) hm).trans
            ((Category.assoc eM πM (α.app F.as.left.unop)).symm.trans
              (congrArg (fun k : (roosComplex M).X n ⟶ M.obj F.as.left.unop =>
                k ≫ α.app F.as.left.unop) hM)))
      exact hLeft.trans hRight.symm)

end ProductPresentation

section Exactness

variable [Abelian A] [HasProducts.{max u₁ v₁} A]
  [AB4StarOfSize.{max u₁ v₁} A]

private theorem roosDegree_shortExact (S : ShortComplex (I ⥤ A))
    (hS : S.ShortExact) (n : ℕ) :
    ((S.map (roosComplexFunctor (I := I) (A := A))).map
      (HomologicalComplex.eval A (ComplexShape.up ℕ) n)).ShortExact := by
  let : HasExactLimitsOfShape (Discrete (ComposableArrows Iᵒᵖ n)) A := inferInstance
  let : (roosDegreePrecompFunctor (I := I) (A := A) n ⋙
      lim (J := Discrete (ComposableArrows Iᵒᵖ n)) (C := A)).Additive :=
    Functor.additive_of_iso (roosDegreeLimitIso (I := I) (A := A) n)
  have hP :
      (S.map (roosDegreePrecompFunctor (I := I) (A := A) n ⋙
        lim (J := Discrete (ComposableArrows Iᵒᵖ n)) (C := A))).ShortExact :=
    hS.map_of_exact (roosDegreePrecompFunctor (I := I) (A := A) n ⋙
      lim (J := Discrete (ComposableArrows Iᵒᵖ n)) (C := A))
  have hD := ShortComplex.shortExact_of_iso
    (S.mapNatIso (roosDegreeLimitIso (I := I) (A := A) n)).symm hP
  simpa only [ShortComplex.map_comp] using hD

/-- The Roos cochain functor sends coefficient short exact sequences to short exact sequences when
products of the chain-index size are exact. -/
theorem roosComplexFunctor_map_shortExact (S : ShortComplex (I ⥤ A))
    (hS : S.ShortExact) :
    (S.map (roosComplexFunctor (I := I) (A := A))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    (S.map (roosComplexFunctor (I := I) (A := A)))
    (fun n ↦ roosDegree_shortExact S hS n)

end Exactness

end CategoryTheory.CategoryCohomology

end
