/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Abelian.Projective.AugmentedExactComparison
import MathlibExt.CategoryTheory.Abelian.Projective.ComplexLift
import MathlibExt.CategoryTheory.Abelian.Ext.DerivedCoyoneda
import MathlibExt.Algebra.Homology.ZeroDifferentialHomology
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Nonexact projective sources and torsion Ext representatives

The free-term chain complex with zero differentials and augmentation to
the integers has nonzero positive homology. It still admits comparison
maps to an exact target concentrated in degree zero at the nonprojective
module Z/6Z, and lifts into a projective resolution of that module.

A degree-zero cocycle representing multiplication by two modulo six
defines a nonzero Ext class. Its image under the inverse derived
Coyoneda comparison remains nonzero and has the stated resolution
representative.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ProjectiveAndDerivedRepresentativesTests

private abbrev Z : ModuleCat ℤ := ModuleCat.of ℤ ℤ
private abbrev N : ModuleCat ℤ := ModuleCat.of ℤ (ZMod 6)
private abbrev quotient : Z ⟶ N :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (ZMod 6) 1)
private abbrev P : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun _ => Z) (fun _ => 0) (by intro n; simp)

private theorem dP (i j : ℕ) : P.d i j = 0 := by
  simp [P, ChainComplex.of.d]

private theorem hP (n : ℕ) : Projective (P.X n) := by
  change Projective Z
  infer_instance

private abbrev ε : P ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj Z :=
  (ChainComplex.toSingle₀Equiv P Z).symm ⟨𝟙 Z, by rw [dP]; simp⟩

private theorem ε_zero : ε.f 0 = 𝟙 Z :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

example : ¬ HomologicalComplex.QuasiIso ε := by
  intro h
  let _ : HomologicalComplex.QuasiIso ε := h
  have hex : P.ExactAt 1 :=
    (HomologicalComplex.exactAt_iff_of_quasiIsoAt ε 1).mpr
      (ChainComplex.exactAt_succ_single_obj Z 0)
  have hz : IsZero Z :=
    hex.isZero_homology.of_iso
      (HomologicalComplex.zeroDifferentialHomologyIso P 1 dP).symm
  have h1 : (1 : ℤ) = 0 := by
    simpa using ConcreteCategory.congr_hom (hz.eq_of_src (𝟙 Z) 0) (1 : ℤ)
  norm_num at h1

example : ¬ Projective N := by
  intro hp
  let _ : Projective N := hp
  let _ : Epi quotient := (ModuleCat.epi_iff_surjective quotient).mpr (by
    intro a
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective a
    refine ⟨z, ?_⟩
    simpa [quotient, LinearMap.toSpanSingleton_apply, zsmul_eq_mul] using hz)
  let s : N ⟶ Z := Projective.factorThru (𝟙 N) quotient
  have hs : s ≫ quotient = 𝟙 N := Projective.factorThru_comp _ _
  have h6 : (6 : ℤ) • (s.hom (1 : ZMod 6)) = 0 := by
    rw [← map_smul]
    have h61 : (6 : ℤ) • (1 : ZMod 6) = 0 := by norm_num
    rw [h61, map_zero]
  have h0 : s.hom (1 : ZMod 6) = 0 :=
    (smul_eq_zero.mp h6).resolve_left (by norm_num)
  have hh := ConcreteCategory.congr_hom hs (1 : ZMod 6)
  change quotient.hom (s.hom (1 : ZMod 6)) = 1 at hh
  rw [h0, map_zero] at hh
  exact (by decide : (0 : ZMod 6) ≠ 1) hh

private abbrev Q : ChainComplex (ModuleCat ℤ) ℕ :=
  (ChainComplex.single₀ (ModuleCat ℤ)).obj N

example : ∃ a : P ⟶ Q,
    a ≫ 𝟙 Q = ε ≫ (ChainComplex.single₀ (ModuleCat ℤ)).map quotient :=
  exists_projectiveAugmentedExactComparison ε (𝟙 Q) hP quotient

private abbrev resolution : ProjectiveResolution N := projectiveResolution N
private abbrev lift : P ⟶ resolution.complex :=
  ProjectiveResolution.liftFromComplex quotient P ε resolution hP

example : (resolution.π.f 0).hom ((lift.f 0).hom 2) = (2 : ZMod 6) := by
  have h := ProjectiveResolution.liftFromComplex_f_zero_comp
    quotient P ε resolution hP
  rw [ε_zero, Category.id_comp] at h
  simpa [quotient, LinearMap.toSpanSingleton_apply, zsmul_eq_mul] using
    ConcreteCategory.congr_hom h (2 : ℤ)

example : (resolution.π.f 0).hom ((lift.f 0).hom 2) ≠ (0 : ZMod 6) := by
  have h := ProjectiveResolution.liftFromComplex_f_zero_comp
    quotient P ε resolution hP
  rw [ε_zero, Category.id_comp] at h
  have h2 : (resolution.π.f 0).hom ((lift.f 0).hom 2) = (2 : ZMod 6) := by
    simpa [quotient, LinearMap.toSpanSingleton_apply, zsmul_eq_mul] using
      ConcreteCategory.congr_hom h (2 : ℤ)
  rw [h2]
  decide

private abbrev I : InjectiveResolution N := injectiveResolution N
private abbrev twice : Z ⟶ N :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (ZMod 6) 2)
private abbrev representative : Z ⟶ I.cocomplex.X 0 := twice ≫ I.ι.f 0
private theorem representative_cycle :
    representative ≫ I.cocomplex.d 0 1 = 0 := by
  change (twice ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0
  rw [Category.assoc, I.ι_f_zero_comp_complex_d, comp_zero]
private abbrev e : CategoryTheory.Abelian.Ext Z N 0 :=
  I.extMk representative 1 rfl representative_cycle

private theorem e_nonzero : e ≠ 0 := by
  intro he
  have hr : representative = 0 :=
    DerivedCoyoneda.extMk_zero_eq_zero Z I representative_cycle he
  have ht : twice = 0 := (cancel_mono (I.ι.f 0)).mp (by simpa using hr)
  have h2 : (2 : ZMod 6) = 0 := by
    simpa [twice, LinearMap.toSpanSingleton_apply] using
      ConcreteCategory.congr_hom ht (1 : ℤ)
  exact (by decide : (2 : ZMod 6) ≠ 0) h2

private abbrev comparison :
    ((preadditiveCoyoneda.obj (Opposite.op Z)).rightDerived 0).obj N ≅
      AddCommGrpCat.of (CategoryTheory.Abelian.Ext Z N 0) :=
  (CategoryTheory.Abelian.rightDerivedCoyonedaIsoExtFunctorObj Z 0).app N
private abbrev derivedClass := comparison.inv e

example : derivedClass ≠ 0 := by
  intro h
  have hc := ConcreteCategory.congr_hom comparison.inv_hom_id e
  change comparison.hom derivedClass = e at hc
  rw [h, map_zero] at hc
  exact e_nonzero hc.symm

example :
    let hE := DerivedCoyoneda.homologyDataExt Z I 0
    let c : hE.K := ⟨representative, representative_cycle⟩
    comparison.inv e =
      (I.isoRightDerivedObj (preadditiveCoyoneda.obj (Opposite.op Z)) 0).inv
        (((DerivedCoyoneda.mappedCocomplex Z I).sc 0).homologyπ (hE.cyclesIso.inv c)) :=
  CategoryTheory.Abelian.rightDerivedCoyonedaIsoExtFunctorObj_inv_extMk
    Z N 0 representative representative_cycle

end ProjectiveAndDerivedRepresentativesTests
