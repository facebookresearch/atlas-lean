/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.LinearHomCochainHomotopyEquiv
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Linear Hom cochains of a single complex

Let R be a ring and C a preadditive R-linear category with a zero object. The scalar, object and
morphism universes are independent. For M,G∈C, Hom_C(M[0],G) is canonically the cochain complex
concentrated in degree zero at Hom_C(M,G). Its degree-zero comparison is the identity under the
single-term identification, and it is natural in G.

Consequently the coefficient functor G↦H^0(Hom_C(M[0],G)) is Hom_C(M,-). A specified homotopy
equivalence K≃M[0] transports this isomorphism to G↦H^0(Hom_C(K,G)). In every positive degree n,
the latter cohomology functor is zero. All Hom and homology modules have carriers in the
morphism universe.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomologicalComplex

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [HasZeroObject C]

/-- Let R be a ring in universe w and C a preadditive R-linear category with a zero object, object
universe u and morphism universe v, independently. For M,G∈C, this is the canonical cochain
isomorphism Hom_C(M[0],G)≅Hom_C(M,G)[0] in R-modules of carrier universe v. The source chain
single and target cochain single are both concentrated in degree zero; every positive-degree Hom
term has zero source. -/
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
/-- Let R be a ring in universe w and C a preadditive R-linear category with a zero object, object
universe u and morphism universe v, independently. For M,G∈C, the forward degree-zero component
of Hom_C(M[0],G)≅Hom_C(M,G)[0] is id_{Hom_C(M,G)} under the canonical identification (M[0])_0=M.
The equality fixes the comparison's map on the full degree-zero Hom module. -/
@[simp]
lemma linearHomCochainComplexSingle₀Iso_hom_f_zero (M G : C) :
    (linearHomCochainComplexSingle₀Iso R M G).hom.f 0 = 𝟙 _ := by
  change ((linearYoneda R C).obj G).map (𝟙 (Opposite.op M)) = 𝟙 _
  ext f
  exact Category.id_comp f

/-- Let R be a ring in universe w and C a preadditive R-linear category with a zero object, object
universe u and morphism universe v, independently. For fixed M∈C, this functor sends G to the
nonnegative cochain complex Hom_C(M[0],G) and a coefficient map G→G′ to postcomposition in every
Hom term. Its cochain modules lie in v. -/
noncomputable def linearHomCochainComplexSingle₀Functor (M : C) :
    C ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  linearHomCochainComplexBifunctor R C ⋙
    (evaluation _ _).obj (Opposite.op ((ChainComplex.single₀ C).obj M))

/-- Let R be a ring in universe w and C a preadditive R-linear category with a zero object, object
universe u and morphism universe v, independently. For fixed M∈C, the isomorphisms
Hom_C(M[0],G)≅Hom_C(M,G)[0] form a natural isomorphism of coefficient functors on C. A map G→G′
acts by postcomposition on the degree-zero Hom modules, and all positive-degree components are
zero. -/
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

/-- Let R be a ring in universe w and C a preadditive R-linear category with a zero object, object
universe u and morphism universe v, independently. For M∈C, there is a natural isomorphism
G↦H^0(Hom_C(M[0],G))≅Hom_C(M,G) of functors C→R-Mod_v. It applies degree-zero homology to the
single-cochain comparison and then uses the homology isomorphism of a degree-zero single
complex. -/
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

/-- Let R be a ring in universe w and C a preadditive R-linear category with a zero object, object
universe u and morphism universe v, independently. For a chain complex K of shape down ℕ and a
specified homotopy equivalence e:K≃M[0], the coefficient functor G↦H^0(Hom_C(K,G)) is naturally
isomorphic to Hom_C(M,G). Its forward map uses precomposition by the inverse leg M[0]→K,
followed by the single-source Hom cohomology comparison. -/
noncomputable def linearHomCochainComplexHomologyFunctorIsoOfSingle₀
    (e : HomotopyEquiv K ((ChainComplex.single₀ C).obj M)) :
    HomologicalComplex.linearHomCochainComplexHomologyFunctor R C K 0 ≅
      (linearCoyoneda R C).obj (Opposite.op M) :=
  (linearHomCochainComplexHomologyNatIso R e 0).symm ≪≫
    HomologicalComplex.linearHomCochainComplexHomologyFunctorSingle₀Iso R M

/-- Let R be a ring in universe w and C a preadditive R-linear category with a zero object, object
universe u and morphism universe v, independently. Let K be a chain complex of shape down ℕ with
a specified homotopy equivalence e:K≃M[0]. For n∈ℕ with n≠0, the entire coefficient functor
G↦H^n(Hom_C(K,G)) is zero in C→R-Mod_v. The homotopy equivalence compares it to the Hom cochains
of the degree-zero single, whose positive cohomology vanishes. -/
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
