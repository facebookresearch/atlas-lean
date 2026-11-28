/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.ColumnZeroAugmentation
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyZeroShortExact
import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence

/-!
# The original-degree-zero vertical-homology augmentation

Let P be Cartan–Eilenberg data for a nonnegative complex L in an abelian category. Its boundary
resolution PB₀ resolves the zero outgoing boundary, so PB₀.complex is acyclic. The inclusion of
PH₀ into the zero-degree vertical- homology complex is consequently a quasi-isomorphism.

The canonical row augmentation restricts along this inclusion to the augmentation of PH₀. It is
a quasi-isomorphism to H₀(L)[0].
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace HomologicalComplex.CartanEilenbergResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

private theorem boundaryFromZero_isZero : IsZero (L.boundaryFrom 0) :=
  (CategoryTheory.Limits.isZero_zero C).of_iso
    L.boundaryFromZeroIso

private theorem boundarySingleZero_isZero :
    IsZero ((ChainComplex.single₀ C).obj (L.boundaryFrom 0)) :=
  (ChainComplex.single₀ C).map_isZero
    (boundaryFromZero_isZero (L := L))

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. The
outgoing boundary B₀⁽out⁾ is zero, so the chosen projective resolution PB₀ has zero homology in
every resolution degree. Its terms are not required to be individually zero. -/
theorem boundaryResolutionZero_acyclic :
    (P.boundaryResolution 0).complex.Acyclic := by
  intro a
  exact (exactAt_iff_of_quasiIsoAt
    (P.boundaryResolution 0).π a).2
      ((HomologicalComplex.acyclic_of_isZero _
        (boundarySingleZero_isZero (L := L))) a)

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. The
canonical inclusion PH₀.complex → P.bicomplex.verticalHomologyComplex(0) is a quasi-isomorphism,
since its short exact quotient PB₀.complex is acyclic. -/
theorem cartanEilenbergVerticalHomologyZeroι_quasiIso :
    QuasiIso P.cartanEilenbergVerticalHomologyZeroι := by
  exact (P.cartanEilenbergVerticalHomologyZeroShortExact.quasiIso_f_iff).2
    P.boundaryResolutionZero_acyclic

private noncomputable def rowHomologyZeroOpcyclesCoordinateIso :
    (P.bicomplex.X 0).opcycles 0 ≅
      (P.homologyResolution 0).complex.X 0 ⊞
        (P.boundaryResolution 0).complex.X 0 :=
  (P.bicomplex.X 0).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    (P.rowHomologyZeroRightData 0).opcyclesIso

private noncomputable def rowHomologyZeroInclusionRepresentative :
    (P.homologyResolution 0).complex.X 0 ⟶
      (P.bicomplex.X 0).X 0 :=
  (P.cyclesComponentSplitting 0 0).s ≫
    (P.termComponentShortComplex 0 0).f

private noncomputable def rowHomologyZeroCanonicalQuotient :
    (P.bicomplex.X 0).X 0 ⟶ (P.bicomplex.X 0).homology 0 :=
  (ChainComplex.cycles₀Iso (P.bicomplex.X 0)).inv ≫
    (P.bicomplex.X 0).homologyπ 0

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem rowHomologyZeroIso_hom_eq_homologyι_comp
    : (P.rowHomologyZeroIso 0).hom =
      (P.bicomplex.X 0).homologyι 0 ≫
        (rowHomologyZeroOpcyclesCoordinateIso P).hom := by
  change (((P.bicomplex.X 0).homologyIsoSc' 1 0 0
      (by simp) (by simp)).hom ≫
        (P.rowHomologyZeroRightData 0).homologyIso.hom) = _
  calc
    ((P.bicomplex.X 0).homologyIsoSc' 1 0 0
        (by simp) (by simp)).hom ≫
          (P.rowHomologyZeroRightData 0).homologyIso.hom =
      ((P.bicomplex.X 0).homologyIsoSc' 1 0 0
        (by simp) (by simp)).hom ≫
          ((P.rowHomologyZeroRightData 0).homologyIso.hom ≫
            (P.rowHomologyZeroRightData 0).ι) := by
        change _ = _ ≫ (_ ≫ 𝟙 _)
        simp
    _ = ((P.bicomplex.X 0).homologyIsoSc' 1 0 0
        (by simp) (by simp)).hom ≫
          (((P.bicomplex.X 0).sc' 1 0 0).homologyι ≫
            (P.rowHomologyZeroRightData 0).opcyclesIso.hom) := by
      rw [(P.rowHomologyZeroRightData 0).homologyIso_hom_comp_ι]
    _ = ((((P.bicomplex.X 0).homologyIsoSc' 1 0 0
        (by simp) (by simp)).hom ≫
          ((P.bicomplex.X 0).sc' 1 0 0).homologyι) ≫
            (P.rowHomologyZeroRightData 0).opcyclesIso.hom) := by
      simp only [Category.assoc]
    _ = ((((P.bicomplex.X 0).homologyι 0 ≫
        ((P.bicomplex.X 0).opcyclesIsoSc' 1 0 0
          (by simp) (by simp)).hom)) ≫
            (P.rowHomologyZeroRightData 0).opcyclesIso.hom) := by
      rw [HomologicalComplex.homologyIsoSc'_hom_ι]
    _ = (P.bicomplex.X 0).homologyι 0 ≫
        (rowHomologyZeroOpcyclesCoordinateIso P).hom := by
      exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem pOpcycles_comp_rowHomologyZeroOpcyclesCoordinateIso :
    (P.bicomplex.X 0).pOpcycles 0 ≫
        (rowHomologyZeroOpcyclesCoordinateIso P).hom =
      P.rowHomologyZeroProjection 0 := by
  change (P.bicomplex.X 0).pOpcycles 0 ≫
      (((P.bicomplex.X 0).opcyclesIsoSc' 1 0 0
        (by simp) (by simp)).hom ≫
          (P.rowHomologyZeroRightData 0).opcyclesIso.hom) =
    P.rowHomologyZeroProjection 0
  convert P.rowHomologyZero_pOpcycles_comp_explicitQuotient 0 using 1

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem rowHomologyZeroCanonicalQuotient_comp_iso :
    rowHomologyZeroCanonicalQuotient P ≫
        (P.rowHomologyZeroIso 0).hom =
      P.rowHomologyZeroProjection 0 := by
  rw [rowHomologyZeroIso_hom_eq_homologyι_comp P]
  dsimp only [rowHomologyZeroCanonicalQuotient]
  simp only [Category.assoc]
  rw [HomologicalComplex.homology_π_ι_assoc]
  change (ChainComplex.cycles₀Iso (P.bicomplex.X 0)).inv ≫
      (ChainComplex.cycles₀Iso (P.bicomplex.X 0)).hom ≫
      (P.bicomplex.X 0).pOpcycles 0 ≫
        (rowHomologyZeroOpcyclesCoordinateIso P).hom =
    P.rowHomologyZeroProjection 0
  rw [Iso.inv_hom_id_assoc]
  exact pOpcycles_comp_rowHomologyZeroOpcyclesCoordinateIso P

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem rowHomologyZeroInclusionRepresentative_comp_projection :
    rowHomologyZeroInclusionRepresentative P ≫
        P.rowHomologyZeroProjection 0 =
      biprod.inl := by
  change ((P.cyclesComponentSplitting 0 0).s ≫
      (P.termComponentShortComplex 0 0).f) ≫
        P.rowHomologyZeroProjection 0 = biprod.inl
  calc
    ((P.cyclesComponentSplitting 0 0).s ≫
        (P.termComponentShortComplex 0 0).f) ≫
          P.rowHomologyZeroProjection 0 =
      (P.cyclesComponentSplitting 0 0).s ≫
        ((P.termComponentShortComplex 0 0).f ≫
          P.rowHomologyZeroProjection 0) :=
      Category.assoc _ _ _
    _ = (P.cyclesComponentSplitting 0 0).s ≫
        ((P.cyclesComponentShortComplex 0 0).g ≫ biprod.inl) := by
      rw [P.termComponent_f_comp_rowHomologyZeroProjection 0]
    _ = ((P.cyclesComponentSplitting 0 0).s ≫
        (P.cyclesComponentShortComplex 0 0).g) ≫ biprod.inl :=
      (Category.assoc _ _ _).symm
    _ = biprod.inl := by
      rw [(P.cyclesComponentSplitting 0 0).s_g, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem rowHomologyZeroInclusionRepresentative_comp_quotient :
    rowHomologyZeroInclusionRepresentative P ≫
        rowHomologyZeroCanonicalQuotient P =
      (P.cartanEilenbergVerticalHomologyZeroι).f 0 := by
  apply (cancel_mono (P.rowHomologyZeroIso 0).hom).1
  simp only [Category.assoc]
  rw [rowHomologyZeroCanonicalQuotient_comp_iso P]
  rw [rowHomologyZeroInclusionRepresentative_comp_projection P]
  exact
    (P.cartanEilenbergVerticalHomologyZeroι_f_comp_rowHomologyZeroIso_hom 0).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem termHorseshoe_i_augmentation_f_zero :
    (P.termComponentShortComplex 0 0).f ≫
        (P.termResolution 0).π.f 0 =
      (P.cyclesResolution 0).π.f 0 ≫ L.iCycles 0 := by
  have h := HomologicalComplex.congr_hom
    (P.termHorseshoe 0).i_augmentation 0
  simpa only [HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero,
    CartanEilenbergResolution.termComponentShortComplex,
    CartanEilenbergResolution.termShortComplex,
    ShortComplex.map_f, HomologicalComplex.eval_map,
    cyclesTermBoundaryShortComplex] using h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem cyclesHorseshoe_p_augmentation_f_zero :
    (P.cyclesComponentShortComplex 0 0).g ≫
        (P.homologyResolution 0).π.f 0 =
      (P.cyclesResolution 0).π.f 0 ≫ L.homologyπ 0 := by
  have h := HomologicalComplex.congr_hom
    (P.cyclesHorseshoe 0).p_augmentation 0
  simpa only [HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero,
    CartanEilenbergResolution.cyclesComponentShortComplex,
    CartanEilenbergResolution.cyclesShortComplex,
    ShortComplex.map_g, HomologicalComplex.eval_map,
    boundaryCyclesHomologyShortComplex] using h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem rowHomologyZeroCanonicalQuotient_comp_augmentation_ι :
    rowHomologyZeroCanonicalQuotient P ≫
        P.termColumnZeroHomologyAugmentation 0 ≫ L.homologyι 0 =
      P.termColumnZeroAugmentation.f 0 ≫ L.pOpcycles 0 := by
  rw [P.termColumnZeroHomologyAugmentation_eq_homologyMap]
  dsimp only [rowHomologyZeroCanonicalQuotient]
  simp only [Category.assoc]
  rw [HomologicalComplex.homologyι_naturality]
  rw [HomologicalComplex.homology_π_ι_assoc]
  change (ChainComplex.cycles₀Iso (P.bicomplex.X 0)).inv ≫
      (ChainComplex.cycles₀Iso (P.bicomplex.X 0)).hom ≫
      (P.bicomplex.X 0).pOpcycles 0 ≫
        HomologicalComplex.opcyclesMap P.termColumnZeroAugmentation 0 =
    P.termColumnZeroAugmentation.f 0 ≫ L.pOpcycles 0
  rw [Iso.inv_hom_id_assoc]
  exact HomologicalComplex.p_opcyclesMap P.termColumnZeroAugmentation 0

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem
    cartanEilenbergVerticalHomologyZeroι_f_zero_comp_augmentation :
    (P.cartanEilenbergVerticalHomologyZeroι).f 0 ≫
        P.termColumnZeroHomologyAugmentation 0 =
      (P.homologyResolution 0).π.f 0 := by
  apply (cancel_mono (L.homologyι 0)).1
  rw [← rowHomologyZeroInclusionRepresentative_comp_quotient P]
  simp only [Category.assoc]
  rw [rowHomologyZeroCanonicalQuotient_comp_augmentation_ι P]
  rw [P.termColumnZeroAugmentation_f]
  dsimp only [rowHomologyZeroInclusionRepresentative]
  simp only [Category.assoc]
  rw [termHorseshoe_i_augmentation_f_zero_assoc P]
  have hπi :
      (P.cyclesComponentSplitting 0 0).s ≫
          (P.cyclesResolution 0).π.f 0 ≫
          L.iCycles 0 ≫ L.pOpcycles 0 =
        (P.cyclesComponentSplitting 0 0).s ≫
          (P.cyclesResolution 0).π.f 0 ≫
          L.homologyπ 0 ≫ L.homologyι 0 := by
    have h := congrArg
      (fun f => ((P.cyclesComponentSplitting 0 0).s ≫
        (P.cyclesResolution 0).π.f 0) ≫ f)
      (L.homology_π_ι 0).symm
    simpa only [Category.assoc] using h
  rw [hπi]
  have hcycles :
      (P.cyclesComponentSplitting 0 0).s ≫
          (P.cyclesResolution 0).π.f 0 ≫
          L.homologyπ 0 ≫ L.homologyι 0 =
        (P.cyclesComponentSplitting 0 0).s ≫
          (P.cyclesComponentShortComplex 0 0).g ≫
          (P.homologyResolution 0).π.f 0 ≫ L.homologyι 0 := by
    have h := congrArg
      (fun f => ((P.cyclesComponentSplitting 0 0).s ≫ f) ≫
        L.homologyι 0)
      (cyclesHorseshoe_p_augmentation_f_zero P).symm
    simpa only [Category.assoc] using h
  rw [hcycles]
  rw [(P.cyclesComponentSplitting 0 0).s_g_assoc]

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. The
inclusion PH₀.complex → verticalHomology(0), followed by the canonical row augmentation to
H₀(L)[0], equals the stored augmentation PH₀.complex → H₀(L)[0]. -/
@[reassoc]
theorem cartanEilenbergVerticalHomologyZeroι_comp_rowHomologyAugmentation :
    P.cartanEilenbergVerticalHomologyZeroι ≫
        P.rowHomologyAugmentation 0 =
      (P.homologyResolution 0).π := by
  apply HomologicalComplex.hom_ext
  intro a
  rcases a with _ | n
  · change (P.cartanEilenbergVerticalHomologyZeroι).f 0 ≫
        (P.rowHomologyAugmentation 0).f 0 =
      (P.homologyResolution 0).π.f 0
    rw [P.rowHomologyAugmentation_f_zero]
    exact
      cartanEilenbergVerticalHomologyZeroι_f_zero_comp_augmentation P
  · change (P.cartanEilenbergVerticalHomologyZeroι).f (n + 1) ≫
        (P.rowHomologyAugmentation 0).f (n + 1) =
      (P.homologyResolution 0).π.f (n + 1)
    rw [P.rowHomologyAugmentation_f_succ,
      (P.homologyResolution 0).π_f_succ]
    exact comp_zero

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. The
canonical augmentation P.bicomplex.verticalHomologyComplex(0) → H₀(L)[0], induced by the
term-resolution column-zero augmentation, is a quasi-isomorphism. -/
theorem rowHomologyZeroAugmentation_quasiIso :
    QuasiIso (P.rowHomologyAugmentation 0) := by
  let _ : QuasiIso P.cartanEilenbergVerticalHomologyZeroι :=
    P.cartanEilenbergVerticalHomologyZeroι_quasiIso
  let _ : QuasiIso
      (P.cartanEilenbergVerticalHomologyZeroι ≫
        P.rowHomologyAugmentation 0) := by
    rw [P.cartanEilenbergVerticalHomologyZeroι_comp_rowHomologyAugmentation]
    infer_instance
  exact quasiIso_of_comp_left
    P.cartanEilenbergVerticalHomologyZeroι
    (P.rowHomologyAugmentation 0)

end HomologicalComplex.CartanEilenbergResolution

end
