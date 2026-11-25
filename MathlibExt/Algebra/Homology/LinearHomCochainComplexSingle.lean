/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.LinearHomCochainHomotopyEquiv
public import Mathlib.Algebra.Homology.SingleHomology

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomologicalComplex

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [HasZeroObject C]

/-- `Hom(-, G)` on the `0`-single chain complex is the `0`-single cochain. -/
noncomputable def linearHomCochainComplexSingle₀Iso (M G : C) :
    (linearHomCochainComplexFunctor R C G).obj
        (Opposite.op ((ChainComplex.single₀ C).obj M)) ≅
      (CochainComplex.single₀ (ModuleCat.{v} R)).obj
        (ModuleCat.of R (M ⟶ G)) :=
  Hom.isoOfComponents
    (fun n =>
      if h : n = 0 then by
        subst n
        exact ((linearYoneda R C).obj G).mapIso
          ((singleObjXSelf (ComplexShape.down ℕ) 0 M).symm.op)
      else by
        have hs : IsZero
            (((linearHomCochainComplexFunctor R C G).obj
              (Opposite.op ((ChainComplex.single₀ C).obj M))).X n) := by
          let _ : Subsingleton
              (((linearHomCochainComplexFunctor R C G).obj
                (Opposite.op ((ChainComplex.single₀ C).obj M))).X n) :=
            ⟨fun f g =>
              (isZero_single_obj_X (ComplexShape.down ℕ) 0 M n h).eq_of_src
                f g⟩
          exact ModuleCat.isZero_of_subsingleton _
        exact hs.iso
          (isZero_single_obj_X (ComplexShape.up ℕ) 0
            (ModuleCat.of R (M ⟶ G)) n h))
    (fun i j _ => by
      have hY :
          ((CochainComplex.single₀ (ModuleCat.{v} R)).obj
            (ModuleCat.of R (M ⟶ G))).d i j = 0 :=
        rfl
      have hX :
          ((linearHomCochainComplexFunctor R C G).obj
            (Opposite.op ((ChainComplex.single₀ C).obj M))).d i j = 0 := by
        change ((linearYoneda R C).obj G).map
          (((ChainComplex.single₀ C).obj M).d j i).op = 0
        simp only [single_obj_d]
        ext f
        change (0 : _ ⟶ _) ≫ f = 0
        exact zero_comp
      simp only [hY, hX, comp_zero, zero_comp])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma linearHomCochainComplexSingle₀Iso_hom_f_zero (M G : C) :
    (linearHomCochainComplexSingle₀Iso R M G).hom.f 0 = 𝟙 _ := by
  change ((linearYoneda R C).obj G).map (𝟙 (Opposite.op M)) = 𝟙 _
  ext f
  exact Category.id_comp f

/-- Functor `G ↦ Hom(single₀ M, G)` as a cochain complex. -/
noncomputable def linearHomCochainComplexSingle₀Functor (M : C) :
    C ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  linearHomCochainComplexBifunctor R C ⋙
    (evaluation _ _).obj (Opposite.op ((ChainComplex.single₀ C).obj M))

/-- `Hom(single₀ M, -)` is naturally isomorphic to `single₀ (M ⟶ -)`. -/
noncomputable def linearHomCochainComplexSingle₀NatIso (M : C) :
    linearHomCochainComplexSingle₀Functor R M ≅
      (linearCoyoneda R C).obj (Opposite.op M) ⋙
        CochainComplex.single₀ (ModuleCat.{v} R) :=
  NatIso.ofComponents
    (fun G => linearHomCochainComplexSingle₀Iso R M G)
    (fun {G G'} f => by
      apply Hom.ext
      funext n
      by_cases hn : n = 0
      · subst n
        ext g
        simp only [linearHomCochainComplexSingle₀Iso_hom_f_zero, comp_f]
        change g ≫ f = g ≫ f
        rfl
      · exact
          (isZero_single_obj_X (ComplexShape.up ℕ) 0
            (ModuleCat.of R (M ⟶ G')) n hn).eq_of_tgt _ _)

/-- `H⁰(Hom(single₀ M, -))` as coefficient functors is `Hom(M, -)`. -/
noncomputable def linearHomCochainComplexHomologyFunctorSingle₀Iso (M : C) :
    linearHomCochainComplexHomologyFunctor R C
        ((ChainComplex.single₀ C).obj M) 0 ≅
      (linearCoyoneda R C).obj (Opposite.op M) := by
  let F := (linearCoyoneda R C).obj (Opposite.op M)
  let S := CochainComplex.single₀ (ModuleCat.{v} R)
  let H := homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℕ) 0
  change (linearHomCochainComplexSingle₀Functor R M ⋙ H) ≅ F
  exact
    Functor.isoWhiskerRight (linearHomCochainComplexSingle₀NatIso R M) H ≪≫
      Functor.associator F S H ≪≫
      Functor.isoWhiskerLeft F
        (homologyFunctorSingleIso (ModuleCat.{v} R) (ComplexShape.up ℕ) 0) ≪≫
      F.rightUnitor

end HomologicalComplex

namespace HomologicalComplex.HomotopyEquiv

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [HasZeroObject C]
variable {K : ChainComplex C ℕ} {M : C}

/-- `H⁰(Hom(K, -))` transported along `K ≃ single₀ M`. -/
noncomputable def linearHomCochainComplexHomologyFunctorIsoOfSingle₀
    (e : HomotopyEquiv K ((ChainComplex.single₀ C).obj M)) :
    HomologicalComplex.linearHomCochainComplexHomologyFunctor R C K 0 ≅
      (linearCoyoneda R C).obj (Opposite.op M) :=
  (linearHomCochainComplexHomologyNatIso R e 0).symm ≪≫
    HomologicalComplex.linearHomCochainComplexHomologyFunctorSingle₀Iso R M

/-- `Hⁿ(Hom(K, -))` is zero for `n ≠ 0` when `K ≃ single₀ M`. -/
theorem isZero_linearHomCochainComplexHomologyFunctor_of_single₀
    (e : HomotopyEquiv K ((ChainComplex.single₀ C).obj M))
    {n : ℕ} (hn : n ≠ 0) :
    IsZero (HomologicalComplex.linearHomCochainComplexHomologyFunctor R C K n) := by
  let F := (linearCoyoneda R C).obj (Opposite.op M)
  let S := CochainComplex.single₀ (ModuleCat.{v} R)
  let H := homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℕ) n
  have hIso :
      HomologicalComplex.linearHomCochainComplexHomologyFunctor R C
        ((ChainComplex.single₀ C).obj M) n ≅ F ⋙ S ⋙ H := by
    change (HomologicalComplex.linearHomCochainComplexSingle₀Functor R M ⋙
      H) ≅ (F ⋙ S ⋙ H)
    exact Functor.isoWhiskerRight
        (HomologicalComplex.linearHomCochainComplexSingle₀NatIso R M) H ≪≫
      Functor.associator F S H
  have hZero : IsZero (F ⋙ S ⋙ H) := by
    apply Functor.isZero
    intro G
    exact isZero_single_obj_homology (ComplexShape.up ℕ) 0
      (ModuleCat.of R (M ⟶ G)) n hn
  have hSingle : IsZero
      (HomologicalComplex.linearHomCochainComplexHomologyFunctor R C
        ((ChainComplex.single₀ C).obj M) n) :=
    (Iso.isZero_iff hIso).mpr hZero
  exact (Iso.isZero_iff (linearHomCochainComplexHomologyNatIso R e n)).mp hSingle

end HomologicalComplex.HomotopyEquiv
