/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison

/-!
# Naturality of right derivation under exact target transformations

The existing comparison uses the chosen injective resolution and canonical homology transport. Its
target-transformation square is obtained from the homology square and the resolution comparison.
The transformation need not be invertible. Source, intermediate and target object and morphism
universes remain independent.
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

/-- The hom component uses the chosen resolution and canonical homology comparison. -/
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

/-- The inverse component reverses the same maps. -/
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

/-- The canonical comparison is natural in an arbitrary transformation of exact targets. -/
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

/-- The inverse comparison is natural for the same noninvertible transformation. -/
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

/-- The hom square is available on each source object, for evaluation diagrams. -/
theorem rightDerivedCompIsoOfPreservesHomology_hom_naturality_target_app
    (F : C ⥤ D) [F.Additive] (U V : D ⥤ E)
    [U.Additive] [V.Additive] [U.PreservesHomology] [V.PreservesHomology]
    (τ : U ⟶ V) (n : ℕ) (X : C) :
    τ.app ((F.rightDerived n).obj X) ≫ (F.rightDerivedCompIsoOfPreservesHomology V n).hom.app X =
      (F.rightDerivedCompIsoOfPreservesHomology U n).hom.app X ≫
        (NatTrans.rightDerived (whiskerLeft F τ) n).app X :=
  congrArg (fun f => f.app X)
    (rightDerivedCompIsoOfPreservesHomology_hom_naturality_target F U V τ n)

/-- The inverse square is likewise available on each source object. -/
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
