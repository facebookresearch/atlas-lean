/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison

/-!
# Right derivation and homology-preserving target changes

Let `C`, `D`, `E` be abelian categories, with injective resolutions in `C`.
For additive `F : C → D` and additive homology-preserving `U : D → E`,
the comparison `U(R^nF(X)) ≅ R^n(F ⋙ U)(X)` is computed through the
cohomology of an injective resolution of `X`. These comparisons commute
with every natural transformation between such target functors.

The source, intermediate and target object and morphism universes are
independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uSource vSource uMiddle vMiddle uTarget vTarget

namespace CategoryTheory.Functor

variable {C : Type uSource} [Category.{vSource} C] [Abelian C]
  {D : Type uMiddle} [Category.{vMiddle} D] [Abelian D]
  {E : Type uTarget} [Category.{vTarget} E] [Abelian E]
  [HasInjectiveResolutions C]

/-- Let `C`, `D`, `E` be abelian, with injective resolutions in `C`,
`F : C → D` additive and `U : D → E` additive and preserving homology.
For the chosen injective resolution `I` of `X`, the forward comparison
`U(R^nF(X)) → R^n(F ⋙ U)(X)` is the composite through
`U(Hⁿ(F(I)))` and `Hⁿ(U(F(I)))` using the two resolution comparisons
and the homology-preservation isomorphism. -/
theorem rightDerivedCompIsoOfPreservesHomology_hom_app
    (F : C ⥤ D) [F.Additive] (U : D ⥤ E) [U.Additive] [U.PreservesHomology]
    (n : ℕ) (X : C) :
    let R := injectiveResolution X
    let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
    (F.rightDerivedCompIsoOfPreservesHomology U n).hom.app X =
      U.map (R.isoRightDerivedObj F n).hom ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n U).inv.app K ≫
          (R.isoRightDerivedObj (F ⋙ U) n).inv := by
  rfl

/-- Let `C`, `D`, `E` be abelian, with injective resolutions in `C`,
`F : C → D` additive and `U : D → E` additive and preserving homology.
For the chosen injective resolution `I` of `X`, the inverse comparison
`R^n(F ⋙ U)(X) → U(R^nF(X))` passes through
`Hⁿ(U(F(I)))` and `U(Hⁿ(F(I)))` in that order. -/
theorem rightDerivedCompIsoOfPreservesHomology_inv_app
    (F : C ⥤ D) [F.Additive] (U : D ⥤ E) [U.Additive] [U.PreservesHomology]
    (n : ℕ) (X : C) :
    let R := injectiveResolution X
    let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
    (F.rightDerivedCompIsoOfPreservesHomology U n).inv.app X =
      (R.isoRightDerivedObj (F ⋙ U) n).hom ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n U).hom.app K ≫
          U.map (R.isoRightDerivedObj F n).inv := by
  let R := injectiveResolution X
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let B := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n U).app K
  let J := R.isoRightDerivedObj (F ⋙ U) n
  change (J.hom ≫ B.hom) ≫ U.map (R.isoRightDerivedObj F n).inv =
    J.hom ≫ B.hom ≫ U.map (R.isoRightDerivedObj F n).inv
  exact Category.assoc _ _ _

/-- Let `C`, `D`, `E` be abelian, with injective resolutions in `C`,
`F : C → D` additive and `U,V : D → E` additive and preserving homology.
For `τ : U → V`, the forward comparison satisfies
`τ_(R^nF) ≫ e_V = e_U ≫ R^n(F ⋙ τ)` as natural transformations. -/
theorem rightDerivedCompIsoOfPreservesHomology_hom_naturality_target
    (F : C ⥤ D) [F.Additive] (U V : D ⥤ E)
    [U.Additive] [V.Additive] [U.PreservesHomology] [V.PreservesHomology]
    (τ : U ⟶ V) (n : ℕ) :
    whiskerLeft (F.rightDerived n) τ ≫ (F.rightDerivedCompIsoOfPreservesHomology V n).hom =
      (F.rightDerivedCompIsoOfPreservesHomology U n).hom ≫
        NatTrans.rightDerived (whiskerLeft F τ) n := by
  apply NatTrans.ext
  funext X
  let R := injectiveResolution X
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n
  let A := (F.rightDerived n).obj X
  let A' := (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj K
  let I := R.isoRightDerivedObj F n
  let B_U := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n U).app K
  let B_V := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n V).app K
  let J_U := R.isoRightDerivedObj (F ⋙ U) n
  let J_V := R.isoRightDerivedObj (F ⋙ V) n
  let δ := (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app K
  let r := (NatTrans.rightDerived (whiskerLeft F τ) n).app X
  have hδ : (NatTrans.mapHomologicalComplex (whiskerLeft F τ) (ComplexShape.up ℕ)).app
      R.cocomplex = δ := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have ha : τ.app A ≫ V.map I.hom = U.map I.hom ≫ τ.app A' :=
    (τ.naturality I.hom).symm
  have hB : H.map δ ≫ B_V.hom = B_U.hom ≫ τ.app A' :=
    HomologicalComplex.mapHomologyFunctorIso_naturality_transformation K n U V τ
  have hb : τ.app A' ≫ B_V.inv = B_U.inv ≫ H.map δ := by
    apply (cancel_mono B_V.hom).1
    calc
      (τ.app A' ≫ B_V.inv) ≫ B_V.hom = τ.app A' := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = B_U.inv ≫ (B_U.hom ≫ τ.app A') := by
        simp only [Iso.inv_hom_id_assoc]
      _ = B_U.inv ≫ (H.map δ ≫ B_V.hom) :=
        congrArg (fun f => B_U.inv ≫ f) hB.symm
      _ = (B_U.inv ≫ H.map δ) ≫ B_V.hom := (Category.assoc _ _ _).symm
  have hc : H.map δ ≫ J_V.inv = J_U.inv ≫ r := by
    have h := R.isoRightDerivedObj_inv_naturality_functor (whiskerLeft F τ) n
    rw [hδ] at h
    exact h
  have sa : CommSq (U.map I.hom) (τ.app A) (τ.app A') (V.map I.hom) := ⟨ha.symm⟩
  have sb : CommSq B_U.inv (τ.app A') (H.map δ) B_V.inv := ⟨hb.symm⟩
  have sc : CommSq J_U.inv (H.map δ) r J_V.inv := ⟨hc.symm⟩
  simp only [NatTrans.comp_app]
  rw [rightDerivedCompIsoOfPreservesHomology_hom_app F U n X,
    rightDerivedCompIsoOfPreservesHomology_hom_app F V n X]
  change τ.app A ≫ (V.map I.hom ≫ B_V.inv ≫ J_V.inv) =
    (U.map I.hom ≫ B_U.inv ≫ J_U.inv) ≫ r
  exact (sa.horiz_comp (sb.horiz_comp sc)).w.symm

/-- Let `C`, `D`, `E` be abelian, with injective resolutions in `C`,
`F : C → D` additive and `U,V : D → E` additive and preserving homology.
For `τ : U → V`, the inverse comparisons satisfy
`R^n(F ⋙ τ) ≫ e_V⁻¹ = e_U⁻¹ ≫ τ_(R^nF)`. -/
theorem rightDerivedCompIsoOfPreservesHomology_inv_naturality_target
    (F : C ⥤ D) [F.Additive] (U V : D ⥤ E)
    [U.Additive] [V.Additive] [U.PreservesHomology] [V.PreservesHomology]
    (τ : U ⟶ V) (n : ℕ) :
    NatTrans.rightDerived (whiskerLeft F τ) n ≫
        (F.rightDerivedCompIsoOfPreservesHomology V n).inv =
      (F.rightDerivedCompIsoOfPreservesHomology U n).inv ≫ whiskerLeft (F.rightDerived n) τ := by
  let e_U := F.rightDerivedCompIsoOfPreservesHomology U n
  let e_V := F.rightDerivedCompIsoOfPreservesHomology V n
  let a := whiskerLeft (F.rightDerived n) τ
  let b := NatTrans.rightDerived (whiskerLeft F τ) n
  have h : a ≫ e_V.hom = e_U.hom ≫ b :=
    rightDerivedCompIsoOfPreservesHomology_hom_naturality_target F U V τ n
  apply (cancel_epi e_U.hom).1
  calc
    e_U.hom ≫ (b ≫ e_V.inv) = (e_U.hom ≫ b) ≫ e_V.inv := (Category.assoc _ _ _).symm
    _ = (a ≫ e_V.hom) ≫ e_V.inv := congrArg (fun f => f ≫ e_V.inv) h.symm
    _ = a := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = e_U.hom ≫ (e_U.inv ≫ a) := by simp only [Iso.hom_inv_id_assoc]

/-- Let `C`, `D`, `E` be abelian, with injective resolutions in `C`,
`F : C → D` additive and `U,V : D → E` additive and preserving homology.
At `X`, a transformation `τ : U → V` satisfies
`τ_(R^nF(X)) ≫ e_V,X = e_U,X ≫ R^n(F ⋙ τ)_X`. -/
theorem rightDerivedCompIsoOfPreservesHomology_hom_naturality_target_app
    (F : C ⥤ D) [F.Additive] (U V : D ⥤ E)
    [U.Additive] [V.Additive] [U.PreservesHomology] [V.PreservesHomology]
    (τ : U ⟶ V) (n : ℕ) (X : C) :
    τ.app ((F.rightDerived n).obj X) ≫ (F.rightDerivedCompIsoOfPreservesHomology V n).hom.app X =
      (F.rightDerivedCompIsoOfPreservesHomology U n).hom.app X ≫
        (NatTrans.rightDerived (whiskerLeft F τ) n).app X :=
  congrArg (fun f => f.app X)
    (rightDerivedCompIsoOfPreservesHomology_hom_naturality_target F U V τ n)

/-- Let `C`, `D`, `E` be abelian, with injective resolutions in `C`,
`F : C → D` additive and `U,V : D → E` additive and preserving homology.
At `X`, a transformation `τ : U → V` satisfies
`R^n(F ⋙ τ)_X ≫ e_V,X⁻¹ = e_U,X⁻¹ ≫ τ_(R^nF(X))`. -/
theorem rightDerivedCompIsoOfPreservesHomology_inv_naturality_target_app
    (F : C ⥤ D) [F.Additive] (U V : D ⥤ E)
    [U.Additive] [V.Additive] [U.PreservesHomology] [V.PreservesHomology]
    (τ : U ⟶ V) (n : ℕ) (X : C) :
    (NatTrans.rightDerived (whiskerLeft F τ) n).app X ≫
        (F.rightDerivedCompIsoOfPreservesHomology V n).inv.app X =
      (F.rightDerivedCompIsoOfPreservesHomology U n).inv.app X ≫
        τ.app ((F.rightDerived n).obj X) :=
  congrArg (fun f => f.app X)
    (rightDerivedCompIsoOfPreservesHomology_inv_naturality_target F U V τ n)

end CategoryTheory.Functor
