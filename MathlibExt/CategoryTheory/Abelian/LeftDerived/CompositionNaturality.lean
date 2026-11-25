/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ResolutionComparison

/-!
# Naturality of exact postcomposition in the functor variable

Let `C`, `D`, `E` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, and `U : D → E` additive and preserving
homology. The comparison between `L_nF ⋙ U` and `L_n(F ⋙ U)`
is natural in a transformation `F → G`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  (α : F ⟶ G) (U : D ⥤ E) [U.Additive] [U.PreservesHomology]

/- Proof implementation note.
The exact-forgetting derived comparison is natural in the original coefficient transformation,
with its projective-resolution maps.
-/

/-- For abelian `C`, `D`, `E`, with projective resolutions in `C`,
additive `F,G : C → D`, homology-preserving additive
`U : D → E`, and `α : F → G`, the postcomposition comparisons
satisfy `(L_nα ⋙ U) ≫ e_G = e_F ≫ L_n(α ⋙ U)`. -/
theorem leftDerivedCompIsoOfPreservesHomology_hom_naturality_functor (n : ℕ) :
    Functor.whiskerRight (NatTrans.leftDerived α n) U ≫
        (G.leftDerivedCompIsoOfPreservesHomology U n).hom =
      (F.leftDerivedCompIsoOfPreservesHomology U n).hom ≫
        NatTrans.leftDerived (Functor.whiskerRight α U) n := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  let φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex
  let H := HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
  let H' := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let e := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n U
  let A := (F.leftDerived n).obj X
  let B := (G.leftDerived n).obj X
  let A' := H.obj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
  let B' := H.obj ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
  let a : A ⟶ B := (NatTrans.leftDerived α n).app X
  let iF : A ⟶ A' := (P.isoLeftDerivedObj F n).hom
  let iG : B ⟶ B' := (P.isoLeftDerivedObj G n).hom
  let m : A' ⟶ B' := H.map φ
  have hMaps : a ≫ iG = iF ≫ m := by
    have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality_functor P α n
    change a ≫ iG = iF ≫ m at h
    exact h
  have h₁ : U.map ((NatTrans.leftDerived α n).app X) ≫
      U.map (P.isoLeftDerivedObj G n).hom =
      U.map (P.isoLeftDerivedObj F n).hom ≫ U.map (H.map φ) :=
    (U.map_comp a iG).symm.trans
      ((congrArg (fun f : A ⟶ B' => U.map f) hMaps).trans (U.map_comp iF m))
  have h₂ : U.map (H.map φ) ≫ e.inv.app ((G.mapHomologicalComplex _).obj P.complex) =
      e.inv.app ((F.mapHomologicalComplex _).obj P.complex) ≫
        H'.map ((U.mapHomologicalComplex _).map φ) :=
    e.inv.naturality φ
  have h₃ : H'.map ((U.mapHomologicalComplex _).map φ) ≫
        (P.isoLeftDerivedObj (G ⋙ U) n).inv =
      (P.isoLeftDerivedObj (F ⋙ U) n).inv ≫
        (NatTrans.leftDerived (Functor.whiskerRight α U) n).app X := by
    have h := ProjectiveResolution.isoLeftDerivedObj_inv_naturality_functor
      P (Functor.whiskerRight α U) n
    exact h
  dsimp only [leftDerivedCompIsoOfPreservesHomology, NatIso.ofComponents,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app]
  simp only [Category.assoc]
  change U.map a ≫ U.map iG ≫
      e.inv.app ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
        (P.isoLeftDerivedObj (G ⋙ U) n).inv =
    U.map iF ≫
      e.inv.app ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
        (P.isoLeftDerivedObj (F ⋙ U) n).inv ≫
          (NatTrans.leftDerived (Functor.whiskerRight α U) n).app X
  calc
    _ = (U.map a ≫ U.map iG) ≫
        e.inv.app ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
          (P.isoLeftDerivedObj (G ⋙ U) n).inv := by
      simp only [Category.assoc]
    _ = (U.map iF ≫ U.map m) ≫
        e.inv.app ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
          (P.isoLeftDerivedObj (G ⋙ U) n).inv :=
      congrArg (fun f => f ≫
        e.inv.app ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
          (P.isoLeftDerivedObj (G ⋙ U) n).inv) h₁
    _ = U.map iF ≫
        (U.map m ≫ e.inv.app
          ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)) ≫
            (P.isoLeftDerivedObj (G ⋙ U) n).inv := by
      simp only [Category.assoc]
    _ = U.map iF ≫
        (e.inv.app ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
          H'.map ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map φ)) ≫
            (P.isoLeftDerivedObj (G ⋙ U) n).inv :=
      congrArg (fun f => U.map iF ≫ f ≫
        (P.isoLeftDerivedObj (G ⋙ U) n).inv) h₂
    _ = U.map iF ≫
        e.inv.app ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫
          (H'.map ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) ≫
            (P.isoLeftDerivedObj (G ⋙ U) n).inv) := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun f => U.map iF ≫
      e.inv.app ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≫ f) h₃

end CategoryTheory.Functor
