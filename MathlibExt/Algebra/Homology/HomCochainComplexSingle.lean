/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.HomCochainComplex
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.SingleHomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- `Hom(-, G)` on the `0`-single chain complex is the `0`-single cochain. -/
noncomputable def homCochainComplexSingle₀Iso (R G : C) :
    (homCochainComplexFunctor C G).obj
        (Opposite.op ((ChainComplex.single₀ C).obj R)) ≅
      (CochainComplex.single₀ AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of (R ⟶ G)) :=
  Hom.isoOfComponents
    (fun n =>
      if h : n = 0 then by
        subst n
        exact (preadditiveYoneda.obj G).mapIso
          ((singleObjXSelf (ComplexShape.down ℕ) 0 R).symm.op)
      else by
        have hs : IsZero
            (((homCochainComplexFunctor C G).obj
              (Opposite.op ((ChainComplex.single₀ C).obj R))).X n) := by
          let _ : Subsingleton
              (((homCochainComplexFunctor C G).obj
                (Opposite.op ((ChainComplex.single₀ C).obj R))).X n) :=
            ⟨fun f g =>
              (isZero_single_obj_X (ComplexShape.down ℕ) 0 R n h).eq_of_src f g⟩
          exact AddCommGrpCat.isZero_of_subsingleton _
        exact hs.iso
          (isZero_single_obj_X (ComplexShape.up ℕ) 0
            (AddCommGrpCat.of (R ⟶ G)) n h))
    (fun i j _ => by
      have hY :
          ((CochainComplex.single₀ AddCommGrpCat.{v}).obj
            (AddCommGrpCat.of (R ⟶ G))).d i j = 0 :=
        rfl
      have hX :
          ((homCochainComplexFunctor C G).obj
            (Opposite.op ((ChainComplex.single₀ C).obj R))).d i j = 0 := by
        change (preadditiveYoneda.obj G).map
          (((ChainComplex.single₀ C).obj R).d j i).op = 0
        simp [single_obj_d]
      simp only [hY, hX, comp_zero, zero_comp])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma homCochainComplexSingle₀Iso_hom_f_zero (R G : C) :
    (homCochainComplexSingle₀Iso (C := C) R G).hom.f 0 = 𝟙 _ := by
  change (preadditiveYoneda.obj G).map (𝟙 (Opposite.op R)) = 𝟙 _
  ext f
  exact Category.id_comp f

/-- Functor `G ↦ Hom(single₀ R, G)` as a cochain complex. -/
noncomputable def homCochainComplexSingle₀Functor (R : C) :
    C ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  homCochainComplexBifunctor C ⋙
    (evaluation _ _).obj (Opposite.op ((ChainComplex.single₀ C).obj R))

/-- `Hom(single₀ R, -)` is naturally isomorphic to `single₀ (R ⟶ -)`. -/
noncomputable def homCochainComplexSingle₀NatIso (R : C) :
    homCochainComplexSingle₀Functor (C := C) R ≅
      preadditiveCoyoneda.obj (Opposite.op R) ⋙
        CochainComplex.single₀ AddCommGrpCat.{v} :=
  NatIso.ofComponents
    (fun G => homCochainComplexSingle₀Iso (C := C) R G)
    (fun {G G'} f => by
      apply Hom.ext
      funext n
      by_cases hn : n = 0
      · subst n
        ext g
        simp only [homCochainComplexSingle₀Iso_hom_f_zero, comp_f]
        change g ≫ f = g ≫ f
        rfl
      · exact
          (isZero_single_obj_X (ComplexShape.up ℕ) 0
            (AddCommGrpCat.of (R ⟶ G')) n hn).eq_of_tgt _ _)

/-- `H⁰(Hom(single₀ R, -))` as coefficient functors is `Hom(R, -)`. -/
noncomputable def homCochainComplexHomologyFunctorSingle₀Iso (R : C) :
    homCochainComplexHomologyFunctor C ((ChainComplex.single₀ C).obj R) 0 ≅
      preadditiveCoyoneda.obj (Opposite.op R) := by
  let F := preadditiveCoyoneda.obj (Opposite.op R)
  let S := CochainComplex.single₀ AddCommGrpCat.{v}
  let H := homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) 0
  change (homCochainComplexSingle₀Functor R ⋙ H) ≅ F
  exact
    Functor.isoWhiskerRight (homCochainComplexSingle₀NatIso R) H ≪≫
      Functor.associator F S H ≪≫
      Functor.isoWhiskerLeft F
        (homologyFunctorSingleIso AddCommGrpCat.{v}
          (ComplexShape.up ℕ) 0) ≪≫
      F.rightUnitor

/-- Functor `G ↦ Hom(single_j R, G)` as cochain complexes. -/
noncomputable def homCochainComplexSingleFunctor (R : C) (j : ℕ) :
    C ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  homCochainComplexBifunctor C ⋙
    (evaluation _ _).obj
      (Opposite.op ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R))

/-- `Hom(single R j, -)` evaluated at `j` is `Hom(R, -)`. -/
noncomputable def homCochainComplexSingleEvalIso (R : C) (j : ℕ) :
    homCochainComplexSingleFunctor (C := C) R j ⋙
        HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) j ≅
      preadditiveCoyoneda.obj (Opposite.op R) :=
  preadditiveCoyoneda.mapIso ((singleObjXSelf (ComplexShape.down ℕ) j R).symm.op)

/-- `Hom(single_j R, -)` at degree `j` corresponds to `single_j (R ⟶ -)` at `j`. -/
noncomputable def homCochainComplexSingleSupportedIso (R : C) (j : ℕ) :
    homCochainComplexSingleFunctor (C := C) R j ⋙
        HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) j ≅
      preadditiveCoyoneda.obj (Opposite.op R) ⋙
        HomologicalComplex.single AddCommGrpCat.{v} (ComplexShape.up ℕ) j ⋙
          HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) j :=
  homCochainComplexSingleEvalIso (C := C) R j ≪≫
    (Functor.isoWhiskerLeft (preadditiveCoyoneda.obj (Opposite.op R))
      (HomologicalComplex.singleCompEvalIsoSelf AddCommGrpCat.{v}
        (ComplexShape.up ℕ) j)).symm

/-- `Hom(-, G)` on the `j`-single complex equals the `j`-single cochain. -/
noncomputable def homCochainComplexSingleIso (R G : C) (j : ℕ) :
    (homCochainComplexFunctor C G).obj
        (Opposite.op ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R)) ≅
      (HomologicalComplex.single AddCommGrpCat.{v} (ComplexShape.up ℕ) j).obj
        (AddCommGrpCat.of (R ⟶ G)) :=
  Hom.isoOfComponents
    (fun n =>
      if h : n = j then by
        subst h
        exact (homCochainComplexSingleSupportedIso (C := C) R n).app G
      else by
        have hs : IsZero
            (((homCochainComplexFunctor C G).obj
              (Opposite.op
                ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R))).X n) := by
          let _ : Subsingleton
              (((homCochainComplexFunctor C G).obj
                (Opposite.op
                  ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R))).X n) :=
            ⟨fun f g =>
              (isZero_single_obj_X (ComplexShape.down ℕ) j R n h).eq_of_src f g⟩
          exact AddCommGrpCat.isZero_of_subsingleton _
        exact hs.iso
          (isZero_single_obj_X (ComplexShape.up ℕ) j
            (AddCommGrpCat.of (R ⟶ G)) n h))
    (fun a b _ => by
      have hY :
          ((HomologicalComplex.single AddCommGrpCat.{v} (ComplexShape.up ℕ) j).obj
              (AddCommGrpCat.of (R ⟶ G))).d a b = 0 :=
        rfl
      have hX :
          ((homCochainComplexFunctor C G).obj
              (Opposite.op
                ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R))).d a b = 0 := by
        change (preadditiveYoneda.obj G).map
            (((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R).d b a).op = 0
        simp [single_obj_d]
      simp only [hY, hX, comp_zero, zero_comp])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma homCochainComplexSingleIso_hom_f_self (R G : C) (j : ℕ) :
    (homCochainComplexSingleIso (C := C) R G j).hom.f j =
      (homCochainComplexSingleSupportedIso (C := C) R j).hom.app G := by
  unfold homCochainComplexSingleIso
  simp [Hom.isoOfComponents]

set_option backward.isDefEq.respectTransparency.types false in
/-- `Hom(single_j R, -)` as `single_j (R ⟶ -)`, natural in the coefficient. -/
noncomputable def homCochainComplexSingleNatIso (R : C) (j : ℕ) :
    homCochainComplexSingleFunctor (C := C) R j ≅
      preadditiveCoyoneda.obj (Opposite.op R) ⋙
        HomologicalComplex.single AddCommGrpCat.{v} (ComplexShape.up ℕ) j :=
  NatIso.ofComponents
    (fun G => homCochainComplexSingleIso (C := C) R G j)
    (fun {G G'} f => by
      apply Hom.ext
      funext n
      by_cases hn : n = j
      · have h := (homCochainComplexSingleSupportedIso (C := C) R j).hom.naturality f
        subst hn
        simp only [comp_f, homCochainComplexSingleIso_hom_f_self,
          homCochainComplexSingleFunctor, Functor.comp_map, evaluation_obj_map,
          eval_map] at h ⊢
        exact h
      · exact
          (isZero_single_obj_X (ComplexShape.up ℕ) j (AddCommGrpCat.of (R ⟶ G')) n hn).eq_of_tgt
            _ _)

/-- `H^j(Hom(single_j R, -))` is `Hom(R, -)` as coefficient functors. -/
noncomputable def homCochainComplexHomologyFunctorSingleIso (R : C) (j : ℕ) :
    homCochainComplexHomologyFunctor C
        ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R) j ≅
      preadditiveCoyoneda.obj (Opposite.op R) := by
  let F := preadditiveCoyoneda.obj (Opposite.op R)
  let S := HomologicalComplex.single AddCommGrpCat.{v} (ComplexShape.up ℕ) j
  let H := homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) j
  change (homCochainComplexSingleFunctor (C := C) R j ⋙ H) ≅ F
  exact
    Functor.isoWhiskerRight (homCochainComplexSingleNatIso (C := C) R j) H ≪≫
      Functor.associator F S H ≪≫
      Functor.isoWhiskerLeft F
        (homologyFunctorSingleIso AddCommGrpCat.{v} (ComplexShape.up ℕ) j) ≪≫
      F.rightUnitor

/-- `H^n(Hom(single_j R, -))` vanishes for `n ≠ j`. -/
theorem isZero_homCochainComplexHomologyFunctorSingle (R : C) (j n : ℕ) (hn : n ≠ j) :
    IsZero (homCochainComplexHomologyFunctor C
        ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R) n) := by
  let F := preadditiveCoyoneda.obj (Opposite.op R)
  let S := HomologicalComplex.single AddCommGrpCat.{v} (ComplexShape.up ℕ) j
  let H := homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) n
  have hIso : homCochainComplexHomologyFunctor C
        ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R) n ≅
        F ⋙ S ⋙ H := by
    change (homCochainComplexSingleFunctor (C := C) R j ⋙ H) ≅ (F ⋙ S ⋙ H)
    exact Functor.isoWhiskerRight (homCochainComplexSingleNatIso (C := C) R j) H ≪≫
      Functor.associator F S H
  have hZero : IsZero (F ⋙ S ⋙ H) := by
    apply Functor.isZero
    intro G
    exact isZero_single_obj_homology (ComplexShape.up ℕ) j
      (AddCommGrpCat.of (R ⟶ G)) n hn
  exact (Iso.isZero_iff hIso).mpr hZero

end HomologicalComplex

namespace HomologicalComplex.HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- `H^j(Hom(K, -))` transported along `K ≃ single_j R`. -/
noncomputable def homCochainComplexHomologyFunctorIsoOfSingle
    {K : ChainComplex C ℕ} {R : C} {j : ℕ}
    (e : HomotopyEquiv K ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R)) :
    homCochainComplexHomologyFunctor C K j ≅
      preadditiveCoyoneda.obj (Opposite.op R) :=
  (homCochainComplexHomologyNatIso e j).symm ≪≫
    homCochainComplexHomologyFunctorSingleIso (C := C) R j

/-- `H^n(Hom(K, -))` vanishes for `n ≠ j` when `K ≃ single_j R`. -/
theorem isZero_homCochainComplexHomologyFunctor_of_single
    {K : ChainComplex C ℕ} {R : C} {j : ℕ}
    (e : HomotopyEquiv K ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R))
    {n : ℕ} (hn : n ≠ j) :
    IsZero (homCochainComplexHomologyFunctor C K n) := by
  have h := isZero_homCochainComplexHomologyFunctorSingle (C := C) R j n hn
  exact (Iso.isZero_iff (homCochainComplexHomologyNatIso e n)).mp h

/-- `H⁰(Hom(K, -))` transported along `K ≃ single₀ R`. -/
noncomputable def homCochainComplexHomologyFunctorIsoOfSingle₀
    {K : ChainComplex C ℕ} {R : C}
    (e : HomotopyEquiv K ((ChainComplex.single₀ C).obj R)) :
    homCochainComplexHomologyFunctor C K 0 ≅
      preadditiveCoyoneda.obj (Opposite.op R) :=
  homCochainComplexHomologyFunctorIsoOfSingle (C := C) e

/-- `Hⁿ(Hom(K, -))` is zero for `n ≠ 0` when `K ≃ single₀ R`. -/
theorem isZero_homCochainComplexHomologyFunctor_of_single₀
    {K : ChainComplex C ℕ} {R : C}
    (e : HomotopyEquiv K ((ChainComplex.single₀ C).obj R))
    {n : ℕ} (hn : n ≠ 0) :
    IsZero (homCochainComplexHomologyFunctor C K n) :=
  isZero_homCochainComplexHomologyFunctor_of_single (C := C) e hn

end HomologicalComplex.HomotopyEquiv
