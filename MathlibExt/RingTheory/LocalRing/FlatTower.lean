/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map.lean`
and
`P2M/Sol/S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map.lean`
and the local flatness criterion it uses, from
`Theorems/Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_
  tor_one_residueField_isZero.lean`


and
`P2M/Sol/S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_
  tor_one_residueField_isZero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.Basic

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

universe u

set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

namespace TorPort

/-! Tor machinery shared by both criteria below: the long exact sequence of `Tor` in
its first argument, the vanishing of higher `Tor` of flat and zero modules, and the
naturality of the canonical map from `Tor₀` to the tensor product. -/

private abbrev Tor1ResVanishing (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  IsZero (((Tor (ModuleCat.{u} R) 1).obj
    (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))

section TorLES
variable {R : Type u} [CommRing R]

private theorem torLES_tensorRight_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (M : ModuleCat.{u} R) [Module.Flat R M] :
    (S.map (tensorRight M)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight M))
    (hS.map_of_exact (tensorLeft M))

@[reducible, simps]
private noncomputable def torLES_resolutionTensorSES (S : ShortComplex (ModuleCat.{u} R))
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
    (by
      ext i : 1
      change S.f ▷ (P.complex.X i) ≫ S.g ▷ (P.complex.X i) = 0
      rw [← comp_whiskerRight, S.zero, MonoidalPreadditive.zero_whiskerRight])

private theorem torLES_resolutionTensorSES_shortExact (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) :
    (torLES_resolutionTensorSES S P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact torLES_tensorRight_shortExact hS (P.complex.X i)

variable {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y)

include P in
private noncomputable def torLES_torIso (P : ProjectiveResolution Y) (X : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).obj X).obj Y ≅
      ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology n :=
  P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) n

include P in
private theorem torLES_torMap_app_eq {X X' : ModuleCat.{u} R} (f : X ⟶ X') (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).map f).app Y =
      (torLES_torIso (P := P) X n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) n ≫
        (torLES_torIso (P := P) X' n).inv :=
  ProjectiveResolution.leftDerived_app_eq ((curriedTensor (ModuleCat.{u} R)).map f) P n

include P in
private noncomputable def torLES_torDelta (P : ProjectiveResolution Y)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj Y ⟶
      ((Tor (ModuleCat.{u} R) n).obj S.X₁).obj Y :=
  (torLES_torIso (P := P) S.X₃ (n + 1)).hom ≫
    (torLES_resolutionTensorSES_shortExact S hS P).δ (n + 1) n (by simp) ≫
    (torLES_torIso (P := P) S.X₁ n).inv

include P in

include P in
private theorem torLES_torMap_comp_eq_zero (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).map S.f).app Y ≫
      ((Tor (ModuleCat.{u} R) n).map S.g).app Y = 0 := by
  have hz : HomologicalComplex.homologyMap (torLES_resolutionTensorSES S P).f n ≫
      HomologicalComplex.homologyMap (torLES_resolutionTensorSES S P).g n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, (torLES_resolutionTensorSES S P).zero,
      HomologicalComplex.homologyMap_zero]
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  rw [torLES_torMap_app_eq (P := P) S.f n, torLES_torMap_app_eq (P := P) S.g n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

include P in
private theorem torLES_torMap_comp_torDelta_eq_zero (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) (n + 1)).map S.g).app Y ≫ torLES_torDelta (P := P) S hS n = 0 := by
  have hz := (torLES_resolutionTensorSES_shortExact S hS P).comp_δ (n + 1) n (by simp)
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  dsimp only [torLES_torDelta]
  rw [torLES_torMap_app_eq (P := P) S.g (n + 1)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

include P in
private theorem torLES_torDelta_comp_eq_zero (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    torLES_torDelta (P := P) S hS n ≫ ((Tor (ModuleCat.{u} R) n).map S.f).app Y = 0 := by
  have hz := (torLES_resolutionTensorSES_shortExact S hS P).δ_comp (n + 1) n (by simp)
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  dsimp only [torLES_torDelta]
  rw [torLES_torMap_app_eq (P := P) S.f n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

include P in
private theorem torLES_tor_exact₂ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat.{u} R) n).map S.f).app Y)
      (((Tor (ModuleCat.{u} R) n).map S.g).app Y)
      (torLES_torMap_comp_eq_zero (P := P) S n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso (P := P) S.X₁ n).symm (torLES_torIso (P := P) S.X₂ n).symm
      (torLES_torIso (P := P) S.X₃ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₂ n)
  · dsimp only
    rw [torLES_torMap_app_eq (P := P) S.f n]
    simp
  · dsimp only
    rw [torLES_torMap_app_eq (P := P) S.g n]
    simp

include P in
private theorem torLES_tor_exact₃ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat.{u} R) (n + 1)).map S.g).app Y)
      (torLES_torDelta (P := P) S hS n)
      (torLES_torMap_comp_torDelta_eq_zero (P := P) S hS n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso (P := P) S.X₂ (n + 1)).symm
      (torLES_torIso (P := P) S.X₃ (n + 1)).symm (torLES_torIso (P := P) S.X₁ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₃ (n + 1) n (by simp))
  · dsimp only
    rw [torLES_torMap_app_eq (P := P) S.g (n + 1)]
    simp
  · dsimp only [torLES_torDelta]
    simp

include P in
private theorem torLES_tor_exact₁ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (torLES_torDelta (P := P) S hS n)
      (((Tor (ModuleCat.{u} R) n).map S.f).app Y)
      (torLES_torDelta_comp_eq_zero (P := P) S hS n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso (P := P) S.X₃ (n + 1)).symm
      (torLES_torIso (P := P) S.X₁ n).symm (torLES_torIso (P := P) S.X₂ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₁ (n + 1) n (by simp))
  · dsimp only [torLES_torDelta]
    simp
  · dsimp only
    rw [torLES_torMap_app_eq (P := P) S.f n]
    simp

include P in

include P in
private theorem torLES_tor_isZero_X₂ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) (h₁ : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₁).obj Y))
    (h₃ : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj Y)) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₂).obj Y) :=
  (torLES_tor_exact₂ (P := P) S hS (n + 1)).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end TorLES

section TorFV
variable {R : Type u} [CommRing R]

private theorem torFV_resolutionTensor_exactAt (M : ModuleCat.{u} R) [Module.Flat R M]
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) (n : ℕ) :
    ((((curriedTensor (ModuleCat.{u} R)).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).ExactAt (n + 1) :=
  Module.Flat.lTensor_shortComplex_exact M (P.complex.sc (n + 1))
    (P.complex_exactAt_succ n)

private theorem torFV_tor_succ_isZero_of_flat_res (M : ModuleCat.{u} R) [Module.Flat R M]
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj Y) := by
  refine IsZero.of_iso ?_ (torLES_torIso (P := P) M (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact torFV_resolutionTensor_exactAt M P n

private theorem torFV_tor_succ_isZero_of_flat (M : ModuleCat.{u} R) [Module.Flat R M]
    (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  exact torFV_tor_succ_isZero_of_flat_res M P n

private theorem torFV_tor_one_isZero_of_flat (M : ModuleCat.{u} R) [Module.Flat R M]
    (Y : ModuleCat.{u} R) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj M).obj Y) :=
  torFV_tor_succ_isZero_of_flat M Y 0

private theorem torFV_tor_succ_isZero_of_isZero (X : ModuleCat.{u} R) (hX : IsZero X)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj X).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  refine IsZero.of_iso ?_ (torLES_torIso (P := P) X (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.ExactAt.of_isZero
    ((tensorRight (P.complex.X (n + 1))).map_isZero hX)

private theorem torFV_tor_one_isZero_of_isZero (X : ModuleCat.{u} R) (hX : IsZero X)
    (Y : ModuleCat.{u} R) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj X).obj Y) :=
  torFV_tor_succ_isZero_of_isZero X hX Y 0

end TorFV

section TorZeroBridge
variable {R : Type u} [CommRing R]

private theorem ar_opcyclesMap_fromLeftDerivedZero'_naturality
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) {X X' : ModuleCat.{u} R}
    (f : X ⟶ X') :
    HomologicalComplex.opcyclesMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X') =
      P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X) ≫
        ((curriedTensor (ModuleCat.{u} R)).map f).app Y := by
  rw [← cancel_epi (HomologicalComplex.pOpcycles
    ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex) 0)]
  rw [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero', ← Category.assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  exact (((curriedTensor (ModuleCat.{u} R)).map f).naturality (P.π.f 0)).symm

private theorem ar_tor0_map_fromLeftDerivedZero_naturality
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) {X X' : ModuleCat.{u} R}
    (f : X ⟶ X') :
    ((Tor (ModuleCat.{u} R) 0).map f).app Y ≫
        ((curriedTensor (ModuleCat.{u} R)).obj X').fromLeftDerivedZero.app Y =
      ((curriedTensor (ModuleCat.{u} R)).obj X).fromLeftDerivedZero.app Y ≫
        ((curriedTensor (ModuleCat.{u} R)).map f).app Y := by
  have hM : ((Tor (ModuleCat.{u} R) 0).map f).app Y =
      (torLES_torIso (P := P) X 0).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) 0 ≫
        (torLES_torIso (P := P) X' 0).inv :=
    torLES_torMap_app_eq (P := P) f 0
  have hF : ((curriedTensor (ModuleCat.{u} R)).obj X).fromLeftDerivedZero.app Y =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) 0).hom ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X) :=
    ProjectiveResolution.fromLeftDerivedZero_eq P
      ((curriedTensor (ModuleCat.{u} R)).obj X)
  have hG : ((curriedTensor (ModuleCat.{u} R)).obj X').fromLeftDerivedZero.app Y =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X') 0).hom ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X') :=
    ProjectiveResolution.fromLeftDerivedZero_eq P
      ((curriedTensor (ModuleCat.{u} R)).obj X')
  have hι : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 =
      HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) 0 := by
    apply HomologicalComplex.homologyι_naturality
  have hO := ar_opcyclesMap_fromLeftDerivedZero'_naturality P f
  have hbr : ∀ {Z : ModuleCat.{u} R}
      (h : ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology 0 ⟶ Z),
      (torLES_torIso (P := P) X' 0).inv ≫
        (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X') 0).hom ≫ h = h :=
    fun {Z} h => (torLES_torIso (P := P) X' 0).inv_hom_id_assoc h
  have hbr2 : (torLES_torIso (P := P) X 0).hom =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) 0).hom := rfl
  have htor : ∀ Z : ModuleCat.{u} R, torLES_torIso (P := P) Z 0 =
      P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj Z) 0 := fun _ => rfl
  rw [hM, hF, hG]
  have hstep : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
      ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homologyι 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X') =
      ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homologyι 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X) ≫
          ((curriedTensor (ModuleCat.{u} R)).map f).app Y :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hι).trans
        ((Category.assoc _ _ _).trans (congrArg _ hO)))
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((torLES_torIso (P := P) X 0).hom ≫ ·)
    (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun k => (torLES_torIso (P := P) X 0).hom ≫
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
        (ComplexShape.down ℕ)).app P.complex) 0 ≫ k) (hbr _)).trans ?_
  refine (congrArg (· ≫ _) hbr2).trans ?_
  refine (congrArg ((P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) 0).hom ≫ ·)
    hstep).trans ?_
  exact ((Category.assoc _ _ _).trans
    (congrArg ((P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) 0).hom ≫ ·)
      (Category.assoc _ _ _))).symm

end TorZeroBridge

end TorPort

namespace MK00Port

open TorPort

section TorZeroBridge
variable {R : Type u} [CommRing R]

private theorem ar_rTensor_injective_of_tor1_isZero
    {A B M : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] (e : A →ₗ[R] B) (he : Function.Injective e)
    (h1 : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (B ⧸ LinearMap.range e))).obj (ModuleCat.of R M))) :
    Function.Injective (LinearMap.rTensor M e) := by
  classical
  set S₀ : ShortComplex (ModuleCat.{u} R) := ShortComplex.mk (ModuleCat.ofHom e)
    (ModuleCat.ofHom (LinearMap.range e).mkQ)
    (by
      have hz : (LinearMap.range e).mkQ ∘ₗ e = 0 := LinearMap.ext fun a => by
        simpa [Submodule.Quotient.mk_eq_zero] using LinearMap.mem_range_self e a
      rw [← ModuleCat.ofHom_comp, hz]
      rfl) with hS₀def
  have hS : S₀.ShortExact := by
    refine ModuleCat.shortComplex_shortExact S₀ ?_ ?_ ?_
    · exact LinearMap.exact_map_mkQ_range e
    · exact he
    · exact Submodule.mkQ_surjective _
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution (ModuleCat.of R M)) :=
    HasProjectiveResolution.out
  have hδ : torLES_torDelta (P := P) S₀ hS 0 = 0 := h1.eq_of_src _ _
  haveI hmono : Mono (((Tor (ModuleCat.{u} R) 0).map S₀.f).app (ModuleCat.of R M)) :=
    (torLES_tor_exact₁ (P := P) S₀ hS 0).mono_g hδ
  haveI : PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).obj S₀.X₁) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  haveI : PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hsq := ar_tor0_map_fromLeftDerivedZero_naturality P S₀.f
  have hfac : ((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M) =
      inv (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₁).fromLeftDerivedZero.app
        (ModuleCat.of R M)) ≫
      (((Tor (ModuleCat.{u} R) 0).map S₀.f).app (ModuleCat.of R M) ≫
      ((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂).fromLeftDerivedZero.app
        (ModuleCat.of R M)) :=
    (IsIso.eq_inv_comp (((curriedTensor (ModuleCat.{u} R)).obj
      S₀.X₁).fromLeftDerivedZero.app (ModuleCat.of R M))).mpr hsq.symm
  haveI hmono₂ : Mono (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂).fromLeftDerivedZero.app
      (ModuleCat.of R M)) := IsIso.mono_of_iso _
  haveI hmono₁ : Mono (inv (((curriedTensor (ModuleCat.{u} R)).obj
      S₀.X₁).fromLeftDerivedZero.app (ModuleCat.of R M))) := IsIso.mono_of_iso _
  have hm2 : Mono (((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M)) := by
    rw [hfac]
    exact mono_comp' hmono₁ (mono_comp' hmono hmono₂)
  exact (ModuleCat.mono_iff_injective
    (((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M))).mp hm2

end TorZeroBridge

section FiniteLengthSupply
variable {R : Type u} [CommRing R]

private theorem ar_isSemisimpleModule_of_isTorsionBySet_isMaximal
    (I : Ideal R) [I.IsMaximal] (M : Type u) [AddCommGroup M] [Module R M]
    (htor : Module.IsTorsionBySet R M (I : Set R)) :
    IsSemisimpleModule R M := by
  letI := htor.module
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  exact htor.isSemisimpleModule_iff.mp inferInstance

private theorem ar_isFiniteLength_of_finite_of_torsionBySet_pow
    [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M]
    (htor : Module.IsTorsionBySet R M ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) :
    IsFiniteLength R M := by
  revert M
  induction n with
  | zero =>
    intro M _ _ _ htor
    haveI : Subsingleton M := by
      refine ⟨fun a b => ?_⟩
      have h1 : (1 : R) ∈ ((IsLocalRing.maximalIdeal R ^ 0 : Ideal R) : Set R) := by
        rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      have ha : (1 : R) • a = 0 := htor (a := ⟨(1 : R), h1⟩)
      have hb : (1 : R) • b = 0 := htor (a := ⟨(1 : R), h1⟩)
      rw [one_smul] at ha hb
      rw [ha, hb]
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    intro M _ _ _ htor

    have htorN : Module.IsTorsionBySet R
        (↥((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M))
        ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
      rintro ⟨v, hv⟩ ⟨a, ha⟩
      have hav : a • v = 0 := by
        refine Submodule.smul_induction_on hv (fun r hr m _ => ?_)
          (fun u w hu hw => by rw [smul_add, hu, hw, add_zero])
        rw [smul_smul]
        have hmem : a * r ∈ ((IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) : Set R) := by
          rw [mul_comm, pow_succ]
          exact Ideal.mul_mem_mul hr ha
        exact htor (a := ⟨a * r, hmem⟩)
      exact Subtype.ext hav
    haveI hssN : IsSemisimpleModule R
        ↥((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M) :=
      ar_isSemisimpleModule_of_isTorsionBySet_isMaximal
        (IsLocalRing.maximalIdeal R) _ htorN
    haveI : Module.Finite R
        ↥((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M) :=
      Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    haveI hartN : IsArtinian R
        ↥((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M) := inferInstance

    have hquot : IsFiniteLength R
        (M ⧸ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M)) := by
      refine ih _ ?_
      intro x a
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
        ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R M) x
      have hsm : Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
            Submodule R M) ((a : R) • m) =
          (a : R) • Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
            Submodule R M) m :=
        map_smul (Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
          Submodule R M)) (a : R) m
      rw [← hsm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul a.2 Submodule.mem_top
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hquot ⊢
    exact ⟨(isNoetherian_iff_submodule_quotient _).mpr ⟨inferInstance, hquot.1⟩,
      (isArtinian_iff_submodule_quotient _).mpr ⟨hartN, hquot.2⟩⟩

private theorem ar_isFiniteLength_quotient_pow_smul [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) :
    IsFiniteLength R
      (R ⧸ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R R)) := by
  refine ar_isFiniteLength_of_finite_of_torsionBySet_pow n _ ?_
  intro x a
  obtain ⟨r, rfl⟩ :=
    Submodule.mkQ_surjective ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ : Submodule R R) x
  have hsm : Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
        Submodule R R) ((a : R) • r) =
      (a : R) • Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
        Submodule R R) r :=
    map_smul (Submodule.mkQ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) • ⊤ :
      Submodule R R)) (a : R) r
  rw [← hsm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul a.2 Submodule.mem_top

end FiniteLengthSupply

section DepthBookkeeping
variable {R : Type u} [CommRing R]

private theorem ar_tmul_mem_smul_top {B M : Type u} [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] (a : Ideal R) (P : Submodule R B) {v : B}
    (hv : v ∈ a • P) (m : M) (hvP : v ∈ P) :
    ((⟨v, hvP⟩ : ↥P) ⊗ₜ[R] m) ∈ a • (⊤ : Submodule R (↥P ⊗[R] M)) := by
  have H : v ∈ P ∧ ∀ (h' : v ∈ P),
      ((⟨v, h'⟩ : ↥P) ⊗ₜ[R] m) ∈ a • (⊤ : Submodule R (↥P ⊗[R] M)) := by
    refine Submodule.smul_induction_on hv (fun r hr u hu => ?_) (fun x y hx hy => ?_)
    · refine ⟨P.smul_mem r hu, fun h' => ?_⟩
      have hmk : (⟨r • u, h'⟩ : ↥P) = r • (⟨u, hu⟩ : ↥P) := rfl
      rw [hmk, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · refine ⟨P.add_mem hx.1 hy.1, fun h' => ?_⟩
      have hmk : (⟨x + y, h'⟩ : ↥P) = (⟨x, hx.1⟩ : ↥P) + (⟨y, hy.1⟩ : ↥P) := rfl
      rw [hmk, TensorProduct.add_tmul]
      exact Submodule.add_mem _ (hx.2 hx.1) (hy.2 hy.1)
  exact H.2 hvP

private theorem ar_rTensor_inclusion_apply_mem_smul {B M : Type u} [AddCommGroup B]
    [Module R B] [AddCommGroup M] [Module R M] (a : Ideal R) {N P : Submodule R B}
    (hNP : N ≤ P) (hNa : N ≤ a • P) (y : ↥N ⊗[R] M) :
    LinearMap.rTensor M (Submodule.inclusion hNP) y ∈
      a • (⊤ : Submodule R (↥P ⊗[R] M)) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul w m =>
    rw [LinearMap.rTensor_tmul]
    exact ar_tmul_mem_smul_top a P (hNa w.2) m (hNP w.2)
  | add y₁ y₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂

private theorem ar_mem_smul_pow_extend {S : Type u} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] {W : Type u}
    [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W] (k : ℕ) {z : W}
    (hz : z ∈ ((IsLocalRing.maximalIdeal R ^ k : Ideal R) • ⊤ : Submodule R W)) :
    z ∈ ((IsLocalRing.maximalIdeal S ^ k : Ideal S) • ⊤ : Submodule S W) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_)
    (fun u v hu hv => Submodule.add_mem _ hu hv)
  rw [← algebraMap_smul S r w]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  have h1 : algebraMap R S r ∈ (IsLocalRing.maximalIdeal R ^ k).map (algebraMap R S) :=
    Ideal.mem_map_of_mem _ hr
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le (algebraMap R S)) k h1

private theorem ar_finite_tensorProduct_left (S : Type u) [CommRing S] [Algebra R S]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module.Finite S M] [Module.Finite R N] :
    Module.Finite S (M ⊗[R] N) := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (R := R) (M := N)
  have hsurj : Function.Surjective
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : M →ₗ[S] M) π) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul m y =>
      obtain ⟨v, rfl⟩ := hπ y
      exact ⟨m ⊗ₜ v, by simp⟩
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨w₁, rfl⟩ := h₁
      obtain ⟨w₂, rfl⟩ := h₂
      exact ⟨w₁ + w₂, map_add _ _ _⟩
  haveI : Module.Finite S (M ⊗[R] (Fin n → R)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight R S M (Fin n)).symm
  exact Module.Finite.of_surjective _ hsurj

end DepthBookkeeping

section ArtinReesTail
variable {R : Type u} [CommRing R]

private theorem ar_mem_range_rTensor_inf_of_ker {M : Type u} [AddCommGroup M]
    [Module R M] (I : Ideal R) (J : Submodule R R)
    (htor1 : ∀ W : Submodule R (R ⧸ J),
      IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R ((R ⧸ J) ⧸ W))).obj
        (ModuleCat.of R M)))
    {x : ↥I ⊗[R] M} (hx : LinearMap.rTensor M (Submodule.subtype I) x = 0) :
    x ∈ Set.range (LinearMap.rTensor M
      (Submodule.inclusion (inf_le_right : J ⊓ (I : Submodule R R) ≤ I))) := by
  classical
  set g : ↥I →ₗ[R] R ⧸ J := J.mkQ ∘ₗ Submodule.subtype I with hg
  have hker : LinearMap.ker g.rangeRestrict =
      LinearMap.range (Submodule.inclusion
        (inf_le_right : J ⊓ (I : Submodule R R) ≤ I)) := by
    rw [LinearMap.ker_rangeRestrict, hg, LinearMap.ker_comp, Submodule.ker_mkQ,
      Submodule.range_inclusion, Submodule.comap_inf, Submodule.comap_subtype_self,
      inf_top_eq]
  have hexact : Function.Exact
      (Submodule.inclusion (inf_le_right : J ⊓ (I : Submodule R R) ≤ I))
      g.rangeRestrict := LinearMap.exact_iff.mpr hker
  have htex := rTensor_exact M hexact
    (LinearMap.surjective_rangeRestrict (f := g))
  have hinj : Function.Injective
      (LinearMap.rTensor M (Submodule.subtype (LinearMap.range g))) :=
    ar_rTensor_injective_of_tor1_isZero (Submodule.subtype (LinearMap.range g))
      (Submodule.injective_subtype _)
      (htor1 (LinearMap.range (Submodule.subtype (LinearMap.range g))))
  have hfac : (LinearMap.range g).subtype ∘ₗ g.rangeRestrict = g := rfl
  have h0 : LinearMap.rTensor M g.rangeRestrict x = 0 := by
    apply hinj
    rw [← LinearMap.rTensor_comp_apply, hfac, hg, LinearMap.rTensor_comp_apply, hx,
      map_zero, map_zero]
  exact (htex x).mp h0

private theorem ar_flat_of_finiteLength_tor1_isZero (R' S M : Type u) [CommRing R']
    [CommRing S] [Algebra R' S] [IsLocalRing R'] [IsLocalRing S] [AddCommGroup M]
    [Module R' M] [Module S M] [IsScalarTower R' S M] (hR : IsNoetherianRing R')
    (hS : IsNoetherianRing S) (hloc : IsLocalHom (algebraMap R' S))
    (hfin : Module.Finite S M)
    (htor : ∀ (N : Type u) [AddCommGroup N] [Module R' N], IsFiniteLength R' N →
      IsZero (((Tor (ModuleCat.{u} R') 1).obj (ModuleCat.of R' N)).obj
        (ModuleCat.of R' M))) :
    Module.Flat R' M := by
  haveI := hR
  haveI := hS
  haveI := hloc
  haveI := hfin
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  haveI : Module.Finite R' (↥I) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian I)
  haveI : Module.Finite S (M ⊗[R'] ↥I) :=
    ar_finite_tensorProduct_left S M ↥I
  obtain ⟨c, hc⟩ :=
    Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal R') (I : Submodule R' R')

  have hxk : ∀ k : ℕ,
      x ∈ ((IsLocalRing.maximalIdeal R' ^ k : Ideal R') • ⊤ :
        Submodule R' (↥I ⊗[R'] M)) := by
    intro k
    have htor1 : ∀ W : Submodule R'
        (R' ⧸ ((IsLocalRing.maximalIdeal R' ^ (c + k) : Ideal R') • ⊤ : Submodule R' R')),
        IsZero (((Tor (ModuleCat.{u} R') 1).obj
          (ModuleCat.of R'
            ((R' ⧸ ((IsLocalRing.maximalIdeal R' ^ (c + k) : Ideal R') • ⊤ :
              Submodule R' R')) ⧸ W))).obj (ModuleCat.of R' M)) := by
      intro W
      refine htor _ ?_
      exact (ar_isFiniteLength_quotient_pow_smul (c + k)).of_surjective
        (Submodule.mkQ_surjective W)
    obtain ⟨y, hy⟩ := ar_mem_range_rTensor_inf_of_ker I
      ((IsLocalRing.maximalIdeal R' ^ (c + k) : Ideal R') • ⊤) htor1 hx
    have hAR : ((IsLocalRing.maximalIdeal R' ^ (c + k) : Ideal R') • ⊤ : Submodule R' R')
        ⊓ (I : Submodule R' R') ≤
        (IsLocalRing.maximalIdeal R' ^ k : Ideal R') • (I : Submodule R' R') := by
      have h1 := hc (c + k) (Nat.le_add_right c k)
      have h2 : c + k - c = k := by omega
      rw [h1, h2]
      exact Submodule.smul_mono le_rfl inf_le_right
    rw [← hy]
    exact ar_rTensor_inclusion_apply_mem_smul _ inf_le_right hAR y

  set y := TensorProduct.comm R' (↥I) M x with hydef
  have hyk : ∀ k : ℕ,
      y ∈ ((IsLocalRing.maximalIdeal S ^ k : Ideal S) • ⊤ :
        Submodule S (M ⊗[R'] ↥I)) := by
    intro k
    refine ar_mem_smul_pow_extend (R := R') k ?_
    have hmap := Submodule.mem_map_of_mem
      (f := (TensorProduct.comm R' (↥I) M).toLinearMap) (hxk k)
    rw [Submodule.map_smul''] at hmap
    exact Submodule.smul_mono le_rfl le_top hmap
  have hy0 : y = 0 := by
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
      (M := M ⊗[R'] ↥I) (IsLocalRing.maximalIdeal S)
      (Ideal.IsMaximal.ne_top inferInstance)
    have hmem : y ∈ (⨅ k : ℕ, (IsLocalRing.maximalIdeal S ^ k : Ideal S) • ⊤ :
        Submodule S (M ⊗[R'] ↥I)) := Submodule.mem_iInf _ |>.mpr hyk
    rw [hbot] at hmem
    simpa using hmem
  have := (LinearEquiv.map_eq_zero_iff (TensorProduct.comm R' (↥I) M)).mp
    (by rw [← hydef]; exact hy0)
  exact this

private theorem ar_flat_of_finiteLength_tor1_isZero_00MK (R' S M : Type u) [CommRing R']
    [CommRing S] [Algebra R' S] [IsLocalRing R'] [IsLocalRing S] [AddCommGroup M]
    [Module R' M] [Module S M] [IsScalarTower R' S M] (hR : IsNoetherianRing R')
    (hS : IsNoetherianRing S) (hloc : IsLocalHom (algebraMap R' S))
    (hfin : Module.Finite S M)
    (htor : ∀ (N : Type u) [AddCommGroup N] [Module R' N], IsFiniteLength R' N →
      IsZero (((Tor (ModuleCat R') 1).obj (ModuleCat.of R' N)).obj
        (ModuleCat.of R' M))) :
    Module.Flat R' M :=
  ar_flat_of_finiteLength_tor1_isZero R' S M hR hS hloc hfin htor

end ArtinReesTail

section Devissage
variable {R : Type u} [CommRing R]

private theorem dv_tor_isZero_of_iso {X X' Y : ModuleCat.{u} R} (e : X ≅ X') (n : ℕ)
    (h : IsZero (((Tor (ModuleCat.{u} R) n).obj X').obj Y)) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj X).obj Y) :=
  h.of_iso (((Tor (ModuleCat.{u} R) n).mapIso e).app Y)

private theorem dv_simple_equiv_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    Nonempty (S ≃ₗ[R] IsLocalRing.ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := S)).mp ‹_›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

private theorem dv_tor1_simple_isZero (R : Type u) [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M)))
    (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R S)).obj (ModuleCat.of R M)) := by
  obtain ⟨e⟩ := dv_simple_equiv_residueField R S
  exact dv_tor_isZero_of_iso e.toModuleIso 1 hκ

private theorem dv_tor1_isZero_of_isFiniteLength {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M)))
    (N : Type u) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) := by
  induction hN with
  | @of_subsingleton N _ _ _ =>
    exact torFV_tor_one_isZero_of_isZero (ModuleCat.of R N)
      (ModuleCat.isZero_of_subsingleton _) (ModuleCat.of R M)
  | @of_simple_quotient N _ _ N' _ _ ih =>
    obtain ⟨P⟩ : Nonempty (ProjectiveResolution (ModuleCat.of R M)) :=
      HasProjectiveResolution.out
    refine torLES_tor_isZero_X₂ (P := P) (LinearMap.shortComplexKer (N'.mkQ))
      (LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective N')) 0 ?_ ?_
    · exact dv_tor_isZero_of_iso
        (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ N')).toModuleIso 1 ih
    · exact dv_tor1_simple_isZero R hκ (N ⧸ N')

private theorem dv_tor1_isZero_of_isFiniteLength_00MK (R M : Type u) [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M]
    (hκ : Tor1ResVanishing R M)
    (N : Type u) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) :=
  dv_tor1_isZero_of_isFiniteLength hκ N hN

end Devissage
end MK00Port

/-- Local flatness criterion, `Tor₁` form: let `R → S` be a local homomorphism of
Noetherian local rings and `M` a finitely generated `S`-module whose `R`-module
structure comes from `S`. If `Tor₁^R(κ, M) = 0` for the residue field `κ` of `R`,
then `M` is flat over `R`. -/
public theorem
  Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M :=
  MK00Port.ar_flat_of_finiteLength_tor1_isZero_00MK R S M ‹_› ‹_› ‹_› ‹_›
    (fun N _ _ hN => MK00Port.dv_tor1_isZero_of_isFiniteLength_00MK R M hκ N hN)

namespace LocalCritPort

open TorPort

section FF9Engine
variable {R : Type u} [CommRing R]

private theorem kwFF9_tor0_map_mono_of_rTensor_injective {X X' : ModuleCat.{u} R}
    (f : X ⟶ X') (Y : ModuleCat.{u} R)
    (hinj : Function.Injective (LinearMap.rTensor Y f.hom)) :
    Mono (((Tor (ModuleCat.{u} R) 0).map f).app Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  haveI : PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).obj X) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  haveI : PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).obj X') :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hsq := ar_tor0_map_fromLeftDerivedZero_naturality P f
  rw [ModuleCat.mono_iff_injective]
  intro a b hab
  have hpt : ∀ z,
      ((((curriedTensor (ModuleCat.{u} R)).obj X').fromLeftDerivedZero.app Y).hom)
        (((((Tor (ModuleCat.{u} R) 0).map f).app Y).hom) z) =
      ((((curriedTensor (ModuleCat.{u} R)).map f).app Y).hom)
        (((((curriedTensor (ModuleCat.{u} R)).obj X).fromLeftDerivedZero.app Y).hom) z) :=
    fun z => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hsq) z
  have hinj' : Function.Injective
      ((((curriedTensor (ModuleCat.{u} R)).map f).app Y).hom) := hinj
  have hiso : Function.Injective
      ((((curriedTensor (ModuleCat.{u} R)).obj X).fromLeftDerivedZero.app Y).hom) :=
    (ModuleCat.mono_iff_injective _).mp (IsIso.mono_of_iso _)
  apply hiso; apply hinj'; rw [← hpt a, ← hpt b, hab]

private theorem kwFF9_idealSES_shortExact {S : Type u} [CommRing S] (I : Ideal S) :
    (ShortComplex.mk (ModuleCat.ofHom I.subtype) (ModuleCat.ofHom (Submodule.mkQ I))
      (by rw [← ModuleCat.ofHom_comp]; exact congrArg _ (LinearMap.ext fun a =>
        (Submodule.Quotient.mk_eq_zero _).mpr a.2))).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact (LinearMap.exact_subtype_mkQ I)
  · exact Submodule.injective_subtype I
  · exact Submodule.mkQ_surjective I

private theorem kwFF12_tor1_isZero_of_tor1_of_rTensor_inj
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (Y : ModuleCat.{u} R)
    (h2 : IsZero (((Tor (ModuleCat.{u} R) 1).obj S.X₂).obj Y))
    (hinj : Function.Injective (LinearMap.rTensor Y S.f.hom)) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj S.X₃).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  haveI : Mono (((Tor (ModuleCat.{u} R) 0).map S.f).app Y) :=
    kwFF9_tor0_map_mono_of_rTensor_injective S.f Y hinj
  have hδ : torLES_torDelta (P := P) S hS 0 = 0 := by
    rw [← cancel_mono (((Tor (ModuleCat.{u} R) 0).map S.f).app Y),
      torLES_torDelta_comp_eq_zero (P := P) S hS 0, zero_comp]
  exact (torLES_tor_exact₃ (P := P) S hS 0).isZero_X₂ (h2.eq_of_src _ _) hδ

private theorem kwFF9_tor1_isZero_of_flat_of_rTensor_inj
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) [Module.Flat R S.X₂]
    (Y : ModuleCat.{u} R)
    (hinj : Function.Injective (LinearMap.rTensor Y S.f.hom)) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj S.X₃).obj Y) :=
  kwFF12_tor1_isZero_of_tor1_of_rTensor_inj S hS Y
    (torFV_tor_one_isZero_of_flat S.X₂ Y) hinj

end FF9Engine

private abbrev KwFF3Tor1IdealVanishing (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  Limits.IsZero
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M))

private abbrev KwFibralFlatTor1Vanish : Prop :=
  ∀ (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')],
    Module.Flat R S' →
    KwFF3Tor1IdealVanishing S ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) S'

private abbrev KwFF9IdealRTensorInj : Prop :=
  ∀ (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')],
    Module.Flat R S' →
    Function.Injective
      (((IsLocalRing.maximalIdeal R).map (algebraMap R S)).subtype.rTensor S')

private theorem kwFF9_torVanish_of_idealRTensorInj (hInj : KwFF9IdealRTensorInj.{u}) :
    KwFibralFlatTor1Vanish.{u} := by
  intro R S S' _ _ _ _ _ _ _ _ _ _ _ _ hflat
  haveI : Module.Flat S (ModuleCat.of S S) := inferInstanceAs (Module.Flat S S)
  exact kwFF9_tor1_isZero_of_flat_of_rTensor_inj _
    (kwFF9_idealSES_shortExact ((IsLocalRing.maximalIdeal R).map (algebraMap R S)))
    (ModuleCat.of S S') (hInj R S S' hflat)

private abbrev KwFF10IdealTowerTensorFactor : Prop :=
  ∀ (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')],
    let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    ∃ γ : (IsLocalRing.maximalIdeal R) ⊗[R] S' → I ⊗[S] S',
      Function.Surjective γ ∧
      ∀ z, (TensorProduct.lid S S') (I.subtype.rTensor S' (γ z))
        = (TensorProduct.lid R S') ((IsLocalRing.maximalIdeal R).subtype.rTensor S' z)

private theorem kwFF10_idealRTensorInj_of_towerFactor (hFactor : KwFF10IdealTowerTensorFactor.{u}) :
    KwFF9IdealRTensorInj.{u} := by
  intro R S S' _ _ _ _ _ _ _ _ _ _ _ _ hflat
  obtain ⟨γ, hγ, hcomm⟩ := hFactor R S S'
  have hRinj : Function.Injective ((IsLocalRing.maximalIdeal R).subtype.rTensor S') :=
    Module.Flat.iff_rTensor_injective'.mp hflat (IsLocalRing.maximalIdeal R)
  intro a b hab
  obtain ⟨x, rfl⟩ := hγ a; obtain ⟨y, rfl⟩ := hγ b
  refine congrArg γ (((TensorProduct.lid R S').injective.comp hRinj) ?_)
  exact (hcomm x).symm.trans
    ((congrArg (⇑(TensorProduct.lid S S')) hab).trans (hcomm y))

private theorem kwFF11_idealTowerTensorFactor_proved : KwFF10IdealTowerTensorFactor.{u} := by
  intro R S S' _ _ _ _ _ _ _ _ _ _ _ _

  set mR := IsLocalRing.maximalIdeal R
  set I := mR.map (algebraMap R S) with hI_def

  let toI : mR → I := fun m => ⟨algebraMap R S m.1, Ideal.mem_map_of_mem _ m.2⟩

  let γbil : mR →ₗ[R] S' →ₗ[R] I ⊗[S] S' :=
    { toFun := fun m =>
        { toFun := fun s' => toI m ⊗ₜ[S] s'
          map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
          map_smul' := fun r s' =>
            show toI m ⊗ₜ[S] (r • s') = r • toI m ⊗ₜ[S] s' from
              TensorProduct.tmul_smul r (toI m) s' }
      map_add' := fun m₁ m₂ => LinearMap.ext fun s' => by
        show toI (m₁ + m₂) ⊗ₜ[S] s' = toI m₁ ⊗ₜ[S] s' + toI m₂ ⊗ₜ[S] s'
        rw [← TensorProduct.add_tmul]; congr 1; exact Subtype.ext (by simp [toI])
      map_smul' := fun r m => LinearMap.ext fun s' => by
        show toI (r • m) ⊗ₜ[S] s' = r • toI m ⊗ₜ[S] s'
        rw [TensorProduct.smul_tmul']; congr 1
        exact Subtype.ext (by simp [toI, Algebra.smul_def]) }
  refine ⟨TensorProduct.lift γbil, ?_, ?_⟩
  ·
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | add w₁ w₂ h₁ h₂ =>
        obtain ⟨z₁, hz₁⟩ := h₁; obtain ⟨z₂, hz₂⟩ := h₂
        exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂]⟩
    | tmul i s' =>

        suffices h : ∀ (x : S) (hx : x ∈ I) (t : S'),
            ∃ z, TensorProduct.lift γbil z = (⟨x, hx⟩ : I) ⊗ₜ[S] t from h i.1 i.2 s'
        intro x hx
        refine Submodule.span_induction
          (p := fun x hx => ∀ t : S',
            ∃ z, TensorProduct.lift γbil z = (⟨x, hx⟩ : I) ⊗ₜ[S] t)
          ?_ ?_ ?_ ?_ hx
        ·
          rintro _ ⟨r, hr, rfl⟩ t
          exact ⟨(⟨r, hr⟩ : mR) ⊗ₜ[R] t, by
            simp only [lift.tmul, γbil, LinearMap.coe_mk, AddHom.coe_mk]; rfl⟩
        ·
          intro t; exact ⟨0, (map_zero _).trans (TensorProduct.zero_tmul _ t).symm⟩
        ·
          intro x y hx hy hpx hpy t
          obtain ⟨z₁, hz₁⟩ := hpx t; obtain ⟨z₂, hz₂⟩ := hpy t
          exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂, ← TensorProduct.add_tmul]; rfl⟩
        ·
          intro a x hx hpx t
          obtain ⟨z, hz⟩ := hpx (a • t)
          exact ⟨z, by rw [hz, ← TensorProduct.smul_tmul]; rfl⟩
  ·
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul m s' =>
        simp only [lift.tmul, γbil, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.rTensor_tmul, Submodule.coe_subtype, TensorProduct.lid_tmul]
        exact IsScalarTower.algebraMap_smul S (m : R) s'

private theorem kwFF12_residueQuotSES_shortExact {S : Type u} [CommRing S] [IsLocalRing S]
    (I : Ideal S) (hI_le : I ≤ IsLocalRing.maximalIdeal S) :
    (ShortComplex.mk
      (ModuleCat.ofHom
        (Submodule.map (Submodule.mkQ I) (IsLocalRing.maximalIdeal S)).subtype)
      (ModuleCat.ofHom (Submodule.liftQ I
        (Submodule.mkQ (IsLocalRing.maximalIdeal S)) (by rwa [Submodule.ker_mkQ])))
      (by rw [← ModuleCat.ofHom_comp]; exact congrArg _ (LinearMap.ext fun a => by
        obtain ⟨x, hx, hxa⟩ := Submodule.mem_map.mp a.2
        simp only [LinearMap.comp_apply, Submodule.coe_subtype, ← hxa]
        exact (Submodule.Quotient.mk_eq_zero _).mpr hx))).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  ·
    exact LinearMap.exact_iff.mpr ((Submodule.ker_liftQ _ _ _).trans
      (by simp only [Submodule.ker_mkQ]; exact (Submodule.range_subtype _).symm))
  · exact Submodule.injective_subtype _
  ·
    exact LinearMap.range_eq_top.mp
      ((Submodule.range_liftQ _ _ _).trans (Submodule.range_mkQ _))

private abbrev KwFF13Stacks10_99_8Pinned : Prop :=
  ∀ (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')],
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    KwFF3Tor1IdealVanishing S ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) S' →
    Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
      (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Tor1ResVanishing S S'

private abbrev KwFF13ResidueQuotKerTensorInjPinned : Prop :=
  ∀ (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')],
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    let K : Submodule S (S ⧸ I) :=
      Submodule.map (Submodule.mkQ I) (IsLocalRing.maximalIdeal S)
    Module.Flat (S ⧸ I) (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Function.Injective (K.subtype.rTensor S')

section BaseChange
set_option synthInstance.maxHeartbeats 240000
variable {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S']
variable (I : Ideal S)

private theorem kwFF13_idealMap_restrictScalars_eq_submoduleMap (J : Ideal S) :
    ((J.map (Ideal.Quotient.mk I) : Ideal (S ⧸ I)) : Submodule (S ⧸ I) (S ⧸ I)).restrictScalars S
      = Submodule.map (Submodule.mkQ I) (J : Submodule S S) := by
  ext z
  simp only [Submodule.restrictScalars_mem, Submodule.mem_map, Submodule.mkQ_apply]
  exact ⟨fun h => (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h,
    fun ⟨x, hx, hxz⟩ => hxz ▸ Ideal.mem_map_of_mem _ hx⟩

private theorem kwFF13_restrictScalars_subtype_rTensor_inj_of_flat
    (K' : Ideal (S ⧸ I)) [Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] S')] :
    Function.Injective
      ((Submodule.subtype ((K' : Submodule (S ⧸ I) (S ⧸ I)).restrictScalars S)).rTensor S') := by

  have hinjQ : Function.Injective (K'.subtype.rTensor ((S ⧸ I) ⊗[S] S')) :=
    Module.Flat.rTensor_preserves_injective_linearMap K'.subtype
      (Submodule.injective_subtype K')

  let eK : ↥K' ⊗[S ⧸ I] ((S ⧸ I) ⊗[S] S') →ₗ[S ⧸ I] ↥K' ⊗[S] S' :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⧸ I) (S ⧸ I) K' S').toLinearMap
  let eQ : (S ⧸ I) ⊗[S ⧸ I] ((S ⧸ I) ⊗[S] S') →ₗ[S ⧸ I] (S ⧸ I) ⊗[S] S' :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⧸ I) (S ⧸ I) (S ⧸ I) S').toLinearMap
  have hnat : ∀ w, (Submodule.subtype
        ((K' : Submodule (S ⧸ I) (S ⧸ I)).restrictScalars S)).rTensor S' (eK w)
      = eQ (K'.subtype.rTensor ((S ⧸ I) ⊗[S] S') w) := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact map_zero _
    | tmul k ab =>
      induction ab using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]; exact map_zero _
      | tmul a n => rfl
      | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add]
        exact (map_add _ _ _).trans (congrArg₂ HAdd.hAdd hx hy)
    | add x y hx hy =>
      simp only [map_add]; exact (map_add _ _ _).trans (congrArg₂ HAdd.hAdd hx hy)

  intro z₁ z₂ hz
  obtain ⟨w₁, rfl⟩ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⧸ I) (S ⧸ I) K' S').surjective z₁
  obtain ⟨w₂, rfl⟩ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⧸ I) (S ⧸ I) K' S').surjective z₂
  exact congrArg eK (hinjQ
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S (S ⧸ I) (S ⧸ I)
      (S ⧸ I) S').injective ((hnat w₁).symm.trans (hz.trans (hnat w₂)))))

end BaseChange

private theorem kwFF13_residueQuotKerTensorInjPinned_proved :
    KwFF13ResidueQuotKerTensorInjPinned.{u} := by
  intro R S S' _ _ _ _ _ _ _ _ _ _ _ _ I K hflat

  letI : Algebra (S ⧸ I) (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
      (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))

  have heq : I.map (algebraMap S S') = (IsLocalRing.maximalIdeal R).map (algebraMap R S') := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S']

  haveI : Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] S') := by
    refine (Module.Flat.equiv_iff ?_).mpr hflat
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S' I).symm.toLinearEquiv.trans
      { __ := Submodule.quotEquivOfEq _ _ heq
        map_smul' := fun c x => by
          induction c using Quotient.inductionOn'
          induction x using Quotient.inductionOn'
          rfl }

  show Function.Injective ((Submodule.map (Submodule.mkQ I)
    (IsLocalRing.maximalIdeal S)).subtype.rTensor S')
  rw [← kwFF13_idealMap_restrictScalars_eq_submoduleMap I (IsLocalRing.maximalIdeal S)]
  exact kwFF13_restrictScalars_subtype_rTensor_inj_of_flat I
    ((IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk I))

private theorem kwFF13_stacks10_99_8Pinned_of_KPinned
    (hKp : KwFF13ResidueQuotKerTensorInjPinned.{u}) : KwFF13Stacks10_99_8Pinned.{u} := by
  intro R S S' _ _ _ _ _ _ _ _ _ _ _ _ htor hflat
  have hI_le : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤
      IsLocalRing.maximalIdeal S :=
    IsLocalRing.le_maximalIdeal (ne_of_lt
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)))
  exact kwFF12_tor1_isZero_of_tor1_of_rTensor_inj _
    (kwFF12_residueQuotSES_shortExact
      ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) hI_le)
    (ModuleCat.of S S') htor (hKp R S S' hflat)

private theorem localCriterion00MK_stub {R S M : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [IsLocalRing S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    (hR : IsNoetherianRing R) (hS : IsNoetherianRing S)
    (hloc : IsLocalHom (algebraMap R S)) (hfin : Module.Finite S M)
    (hκ : Tor1ResVanishing R M) : Module.Flat R M := by
  haveI := hR; haveI := hS; haveI := hloc; haveI := hfin
  exact Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero
    (S := S) hκ
end LocalCritPort

/-- Local flatness criterion in a tower of local rings: if `S'` is flat over
`R` and the closed fibre `S' ⧸ 𝔪_R S'` is flat over `S ⧸ 𝔪_R S`, then `S'`
is flat over `S`. -/
public theorem IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [IsNoetherianRing S] [IsNoetherianRing S'] :
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    Module.Flat R S' →
    Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Module.Flat S S' := by
  intro hflat hfib
  exact LocalCritPort.localCriterion00MK_stub (R := S) (S := S') (M := S') ‹_› ‹_› inferInstance
    inferInstance
    ((LocalCritPort.kwFF13_stacks10_99_8Pinned_of_KPinned
      LocalCritPort.kwFF13_residueQuotKerTensorInjPinned_proved)
      R S S'
      ((LocalCritPort.kwFF9_torVanish_of_idealRTensorInj
        (LocalCritPort.kwFF10_idealRTensorInj_of_towerFactor
          LocalCritPort.kwFF11_idealTowerTensorFactor_proved))
        R S S' hflat)
      hfib)
