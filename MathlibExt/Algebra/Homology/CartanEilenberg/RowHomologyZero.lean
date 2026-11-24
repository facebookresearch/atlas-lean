/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import MathlibExt.Algebra.Homology.CartanEilenberg.Bicomplex
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowSplittings
public import MathlibExt.Algebra.Homology.ShortComplex.SplittingComp
public import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Degree-zero row homology of a Cartan--Eilenberg resolution

This file identifies the degree-zero homology of each vertical row with the
biproduct of the stored degree-zero homology- and boundary-resolution terms.
It deliberately stops before assembling the horizontal differential or short
exact sequence.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.CartanEilenbergResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

/-- The selected cokernel of the composite cycles/term inclusions in
resolution degree `a`. -/
noncomputable def rowHomologyZeroCompositeCofork (a : ℕ) :
    CokernelCofork
      ((P.cyclesComponentShortComplex a 0).f ≫
        (P.termComponentShortComplex a 0).f) :=
  ShortComplex.Splitting.compLeftCokernelCofork
    (f₁ := (P.cyclesComponentShortComplex a 0).f)
    (g₁ := (P.cyclesComponentShortComplex a 0).g)
    (w₁ := (P.cyclesComponentShortComplex a 0).zero)
    (P.termComponentSplitting a 0)

/-- The selected quotient map from the term-resolution component to the
homology/boundary biproduct. -/
noncomputable def rowHomologyZeroProjection (a : ℕ) :
    (P.termResolution 0).complex.X a ⟶
      (P.homologyResolution 0).complex.X a ⊞
        (P.boundaryResolution 0).complex.X a :=
  (P.rowHomologyZeroCompositeCofork a).π

@[simp]
theorem rowHomologyZeroProjection_eq (a : ℕ) :
    P.rowHomologyZeroProjection a =
      biprod.lift
        ((P.termComponentSplitting a 0).r ≫
          (P.cyclesComponentShortComplex a 0).g)
        (P.termComponentShortComplex a 0).g :=
  rfl

private theorem rowHomologyZeroProjection_comp_fst (a : ℕ) :
    P.rowHomologyZeroProjection a ≫ biprod.fst =
      (P.termComponentSplitting a 0).r ≫
        (P.cyclesComponentShortComplex a 0).g := by
  rw [P.rowHomologyZeroProjection_eq a]
  simp

private theorem rowHomologyZeroProjection_comp_snd (a : ℕ) :
    P.rowHomologyZeroProjection a ≫ biprod.snd =
      (P.termComponentShortComplex a 0).g := by
  rw [P.rowHomologyZeroProjection_eq a]
  simp

/-- The term-row inclusion followed by the selected q=0 quotient lands in
the homology-resolution coordinate. -/
@[reassoc]
theorem termComponent_f_comp_rowHomologyZeroProjection (a : ℕ) :
    (P.termComponentShortComplex a 0).f ≫
        P.rowHomologyZeroProjection a =
      (P.cyclesComponentShortComplex a 0).g ≫ biprod.inl := by
  apply biprod.hom_ext
  · calc
      ((P.termComponentShortComplex a 0).f ≫
          P.rowHomologyZeroProjection a) ≫ biprod.fst =
        (P.termComponentShortComplex a 0).f ≫
          (P.rowHomologyZeroProjection a ≫ biprod.fst) :=
        Category.assoc _ _ _
      _ = (P.termComponentShortComplex a 0).f ≫
          ((P.termComponentSplitting a 0).r ≫
            (P.cyclesComponentShortComplex a 0).g) := by
        rw [rowHomologyZeroProjection_comp_fst P a]
      _ = ((P.termComponentShortComplex a 0).f ≫
          (P.termComponentSplitting a 0).r) ≫
            (P.cyclesComponentShortComplex a 0).g :=
        (Category.assoc _ _ _).symm
      _ = (P.cyclesComponentShortComplex a 0).g := by
        rw [(P.termComponentSplitting a 0).f_r, Category.id_comp]
      _ = ((P.cyclesComponentShortComplex a 0).g ≫ biprod.inl) ≫
          biprod.fst := by simp
  · calc
      ((P.termComponentShortComplex a 0).f ≫
          P.rowHomologyZeroProjection a) ≫ biprod.snd =
        (P.termComponentShortComplex a 0).f ≫
          (P.rowHomologyZeroProjection a ≫ biprod.snd) :=
        Category.assoc _ _ _
      _ = (P.termComponentShortComplex a 0).f ≫
          (P.termComponentShortComplex a 0).g := by
        rw [rowHomologyZeroProjection_comp_snd P a]
      _ = 0 := (P.termComponentShortComplex a 0).zero
      _ = ((P.cyclesComponentShortComplex a 0).g ≫ biprod.inl) ≫
          biprod.snd := by simp

/-- The selected quotient is a cokernel of the composite cycles/term
inclusion. -/
noncomputable def rowHomologyZeroCompositeCoforkIsColimit (a : ℕ) :
    IsColimit (P.rowHomologyZeroCompositeCofork a) :=
  ShortComplex.Splitting.compLeftCokernelCoforkIsColimit
    (P.cyclesComponentSplitting a 0) (P.termComponentSplitting a 0)

set_option backward.isDefEq.respectTransparency false in
/-- The selected cokernel of the incoming row differential together with its universal property. -/
noncomputable def rowHomologyZeroCokernelPackage (a : ℕ) :
    Σ c : CokernelCofork ((P.bicomplex.X a).d 1 0), IsColimit c := by
  let _ : Epi ((P.termHorseshoe 1).p.f a) := by
    change Epi (P.termComponentShortComplex a 1).g
    exact (P.termComponentSplitting a 1).epi_g
  have hd : (P.bicomplex.X a).d 1 0 =
      (P.termHorseshoe 1).p.f a ≫
        ((P.cyclesComponentShortComplex a 0).f ≫
          (P.termComponentShortComplex a 0).f) := by
    rw [P.bicomplex_d₂ a 0]
    change (P.termDifferential 0).f a = _
    have h := HomologicalComplex.congr_hom (P.termDifferential_eq 0) a
    simpa only [Nat.zero_add, cyclesComponentShortComplex,
      termComponentShortComplex,
      CartanEilenbergResolution.cyclesShortComplex,
      CartanEilenbergResolution.termShortComplex,
      ShortComplex.map_f, HomologicalComplex.eval_map,
      HomologicalComplex.comp_f, Category.assoc] using h
  have h := isCokernelEpiComp
    (P.rowHomologyZeroCompositeCoforkIsColimit a)
    ((P.termHorseshoe 1).p.f a) hd
  exact ⟨_, h⟩

/-- The selected cokernel cofork of the incoming row differential. -/
noncomputable def rowHomologyZeroCofork (a : ℕ) :
    CokernelCofork ((P.bicomplex.X a).d 1 0) :=
  (P.rowHomologyZeroCokernelPackage a).1

set_option backward.isDefEq.respectTransparency false in
/-- The incoming-differential cofork uses the explicit homology/boundary projection. -/
@[simp]
theorem rowHomologyZeroCofork_π (a : ℕ) :
    (P.rowHomologyZeroCofork a).π =
      P.rowHomologyZeroProjection a := by
  rfl

/-- The selected q=0 quotient is a cokernel of the incoming row differential. -/
noncomputable def rowHomologyZeroCoforkIsColimit (a : ℕ) :
    IsColimit (P.rowHomologyZeroCofork a) :=
  (P.rowHomologyZeroCokernelPackage a).2

set_option backward.isDefEq.respectTransparency false in
/-- Right homology data computing degree-zero row homology by the explicit
homology/boundary quotient. -/
noncomputable def rowHomologyZeroRightData (a : ℕ) :
    ((P.bicomplex.X a).sc' 1 0 0).RightHomologyData :=
  ShortComplex.RightHomologyData.ofIsColimitCokernelCofork
    ((P.bicomplex.X a).sc' 1 0 0)
      ((P.bicomplex.X a).shape 0 0 (by simp))
      (P.rowHomologyZeroCofork a)
      (P.rowHomologyZeroCoforkIsColimit a)

set_option backward.isDefEq.respectTransparency.types false in
/-- In each resolution degree, q=0 row homology is the biproduct of the
stored homology- and boundary-resolution terms. -/
noncomputable def rowHomologyZeroIso (a : ℕ) :
    (P.bicomplex.X a).homology 0 ≅
      (P.homologyResolution 0).complex.X a ⊞
        (P.boundaryResolution 0).complex.X a := by
  change (P.bicomplex.X a).homology 0 ≅
    (P.rowHomologyZeroRightData a).H
  exact (P.bicomplex.X a).homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    (P.rowHomologyZeroRightData a).homologyIso

/-- The selected q=0 opcycles quotient is the explicit
homology/boundary projection. -/
@[reassoc]
theorem rowHomologyZero_sc_pOpcycles_comp_opcyclesIso (a : ℕ) :
    ((P.bicomplex.X a).sc' 1 0 0).pOpcycles ≫
        (P.rowHomologyZeroRightData a).opcyclesIso.hom =
      P.rowHomologyZeroProjection a := by
  exact (P.rowHomologyZeroRightData a).pOpcycles_comp_opcyclesIso_hom

/-- The original selected opcycles quotient, transported to the explicit
q=0 homology/boundary projection. -/
@[reassoc]
theorem rowHomologyZero_pOpcycles_comp_explicitQuotient (a : ℕ) :
    (P.bicomplex.X a).pOpcycles 0 ≫
        ((P.bicomplex.X a).opcyclesIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
        (P.rowHomologyZeroRightData a).opcyclesIso.hom =
      P.rowHomologyZeroProjection a := by
  rw [HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc]
  exact P.rowHomologyZero_sc_pOpcycles_comp_opcyclesIso a

end HomologicalComplex.CartanEilenbergResolution

end
