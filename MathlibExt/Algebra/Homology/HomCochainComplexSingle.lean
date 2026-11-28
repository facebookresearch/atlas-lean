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

/-!
# Hom cochains of a single chain object

Let `C` be a preadditive category with a zero object. For an object `A` placed in natural
chain degree `j`, the Hom cochain complex into `G` is naturally the single cochain complex in
degree `j` on the additive group `Hom_C(A,G)`.

Its cohomology is that Hom group in degree `j` and zero in every other natural degree. The
degree-zero versions use the canonical zero-single functors. A homotopy equivalence from a
chain complex to such a single complex transports these coefficient-natural cohomology
descriptions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- Coefficient Hom cochain functor of an object in degree j.

For fixed `A` and natural `j`, take `G` to the Hom cochain complex of the chain single object
`A[j]` into `G`. -/
noncomputable def homCochainComplexSingleFunctor (R : C) (j : ℕ) :
    C ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  homCochainComplexBifunctor C ⋙
    (evaluation _ _).obj
      (Opposite.op ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R))

/-- Evaluation in the supported Hom degree is the Hom group.

Evaluate the coefficient Hom cochain functor of `A[j]` in cochain degree `j`; the resulting
functor is naturally isomorphic to `Hom_C(A,-)`. -/
noncomputable def homCochainComplexSingleEvalIso (R : C) (j : ℕ) :
    homCochainComplexSingleFunctor (C := C) R j ⋙
        HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) j ≅
      preadditiveCoyoneda.obj (Opposite.op R) :=
  preadditiveCoyoneda.mapIso ((singleObjXSelf (ComplexShape.down ℕ) j R).symm.op)

/-- Supported coordinate matches the single cochain Hom construction.

The degree-`j` evaluation of Hom cochains from `A[j]` is naturally isomorphic to `Hom_C(A,-)`
followed by the degree-`j` single cochain functor and evaluation at `j`. -/
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

/-- Hom cochains of a single chain object are a single cochain Hom group.

For objects `A`, `G` and natural degree `j`, the Hom cochain complex of `A[j]` into `G` is
isomorphic to the single cochain complex in degree `j` on `Hom_C(A,G)`. -/
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
/-- Supported component of the single Hom cochain isomorphism.

The forward component of the single Hom cochain isomorphism in degree `j` is the supported
evaluation-coordinate isomorphism at coefficient `G`. -/
@[simp]
lemma homCochainComplexSingleIso_hom_f_self (R G : C) (j : ℕ) :
    (homCochainComplexSingleIso (C := C) R G j).hom.f j =
      (homCochainComplexSingleSupportedIso (C := C) R j).hom.app G := by
  unfold homCochainComplexSingleIso
  simp [Hom.isoOfComponents]

set_option backward.isDefEq.respectTransparency.types false in
/-- Single-degree Hom cochain isomorphism is coefficient-natural.

The coefficient Hom functor of the single chain object `A[j]` is naturally isomorphic to
`Hom_C(A,-)` followed by the single cochain functor in degree `j`. -/
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

/-- Supported cohomology of a single-object Hom complex is Coyoneda.

The degree-`j` cohomology coefficient functor of Hom cochains from `A[j]` is naturally
isomorphic to `Hom_C(A,-)`. -/
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

/-- Hom cochains of a degree-zero single object use the general single-degree comparison. -/
noncomputable def homCochainComplexSingle₀Iso (R G : C) :
    (homCochainComplexFunctor C G).obj
        (Opposite.op ((ChainComplex.single₀ C).obj R)) ≅
      (CochainComplex.single₀ AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of (R ⟶ G)) :=
  homCochainComplexSingleIso (C := C) R G 0

/-- The degree-zero coefficient functor is the degree-zero general single functor. -/
noncomputable def homCochainComplexSingle₀Functor (R : C) :
    C ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  homCochainComplexSingleFunctor (C := C) R 0

/-- The degree-zero natural comparison uses the general coefficient-natural comparison. -/
noncomputable def homCochainComplexSingle₀NatIso (R : C) :
    homCochainComplexSingle₀Functor (C := C) R ≅
      preadditiveCoyoneda.obj (Opposite.op R) ⋙
        CochainComplex.single₀ AddCommGrpCat.{v} :=
  homCochainComplexSingleNatIso (C := C) R 0

/-- Zeroth single-object Hom cohomology uses the general supported cohomology comparison. -/
noncomputable def homCochainComplexHomologyFunctorSingle₀Iso (R : C) :
    homCochainComplexHomologyFunctor C ((ChainComplex.single₀ C).obj R) 0 ≅
      preadditiveCoyoneda.obj (Opposite.op R) :=
  homCochainComplexHomologyFunctorSingleIso (C := C) R 0

set_option backward.isDefEq.respectTransparency.types false in
/-- The retained degree-zero Hom comparison is the identity on the Hom group. -/
@[simp]
lemma homCochainComplexSingle₀Iso_hom_f_zero (R G : C) :
    (homCochainComplexSingle₀Iso (C := C) R G).hom.f 0 = 𝟙 _ := by
  rw [homCochainComplexSingle₀Iso, homCochainComplexSingleIso_hom_f_self]
  simp [homCochainComplexSingleSupportedIso, homCochainComplexSingleEvalIso,
    singleObjXSelf, singleObjXIsoOfEq, HomologicalComplex.singleCompEvalIsoSelf,
    HomologicalComplex.single, preadditiveCoyoneda] <;>
    ext f <;> rfl

/-- Single-object Hom cohomology vanishes away from its degree.

For `n ≠ j`, the degree-`n` cohomology coefficient functor of Hom cochains from the single
object `A[j]` is zero. -/
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

/-- Homotopy equivalence to a single object identifies supported Hom cohomology.

If `K` is homotopy equivalent to `A[j]`, then its degree-`j` Hom cochain cohomology
coefficient functor is naturally isomorphic to `Hom_C(A,-)`. -/
noncomputable def homCochainComplexHomologyFunctorIsoOfSingle
    {K : ChainComplex C ℕ} {R : C} {j : ℕ}
    (e : HomotopyEquiv K ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R)) :
    homCochainComplexHomologyFunctor C K j ≅
      preadditiveCoyoneda.obj (Opposite.op R) :=
  (homCochainComplexHomologyNatIso e j).symm ≪≫
    homCochainComplexHomologyFunctorSingleIso (C := C) R j

/-- Homotopy-single chain complex has no other Hom cohomology.

For a homotopy equivalence `K ≃ A[j]` and `n ≠ j`, the degree-`n` Hom cochain cohomology
coefficient functor of `K` is zero. -/
theorem isZero_homCochainComplexHomologyFunctor_of_single
    {K : ChainComplex C ℕ} {R : C} {j : ℕ}
    (e : HomotopyEquiv K ((HomologicalComplex.single C (ComplexShape.down ℕ) j).obj R))
    {n : ℕ} (hn : n ≠ j) :
    IsZero (homCochainComplexHomologyFunctor C K n) := by
  have h := isZero_homCochainComplexHomologyFunctorSingle (C := C) R j n hn
  exact (Iso.isZero_iff (homCochainComplexHomologyNatIso e n)).mp h

/-- Homotopy equivalence to degree zero identifies zeroth Hom cohomology.

If `K` is homotopy equivalent to the degree-zero single object `A[0]`, its zeroth Hom cochain
cohomology coefficient functor is naturally isomorphic to `Hom_C(A,-)`. -/
noncomputable def homCochainComplexHomologyFunctorIsoOfSingle₀
    {K : ChainComplex C ℕ} {R : C}
    (e : HomotopyEquiv K ((ChainComplex.single₀ C).obj R)) :
    homCochainComplexHomologyFunctor C K 0 ≅
      preadditiveCoyoneda.obj (Opposite.op R) :=
  homCochainComplexHomologyFunctorIsoOfSingle (C := C) e

/-- Homotopy degree-zero single complex has vanishing positive Hom cohomology.

If `K` is homotopy equivalent to `A[0]`, its degree-`n` Hom cochain cohomology coefficient
functor is zero whenever `n ≠ 0`. -/
theorem isZero_homCochainComplexHomologyFunctor_of_single₀
    {K : ChainComplex C ℕ} {R : C}
    (e : HomotopyEquiv K ((ChainComplex.single₀ C).obj R))
    {n : ℕ} (hn : n ≠ 0) :
    IsZero (homCochainComplexHomologyFunctor C K n) :=
  isZero_homCochainComplexHomologyFunctor_of_single (C := C) e hn

end HomologicalComplex.HomotopyEquiv
