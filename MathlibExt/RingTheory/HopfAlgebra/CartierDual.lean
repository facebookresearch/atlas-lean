/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_HopfAlgebra_CartierDual.lean`
and
`Definitions/Def_HopfAlgebra_CartierDualInstances.lean`
and
`Definitions/Def_HopfAlgebra_CartierDualMap.lean`
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

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Convolution

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

@[expose] public section


open Coalgebra
open scoped TensorProduct

universe u v w x

def CartierDual (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A] :
    Type (max u v) :=
  Module.Dual R A

namespace CartierDual

noncomputable section

section TransposeOfComul

variable (R : Type u) (A : Type v) [CommRing R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

omit [Coalgebra R A] in

theorem dualDistrib_tmul_eq_mul'_comp_map (f g : Module.Dual R A) :
    TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g) =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f g := by
  apply TensorProduct.ext'
  intro a b
  rw [TensorProduct.dualDistrib_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply]

theorem convMul_ofConv (f g : Module.Dual R A) :
    (WithConv.toConv f * WithConv.toConv g).ofConv =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f g ∘ₗ Coalgebra.comul :=
  congrArg WithConv.ofConv (LinearMap.convMul_def (WithConv.toConv f) (WithConv.toConv g))

theorem convMul_ofConv_apply (f g : Module.Dual R A) (a : A) :
    (WithConv.toConv f * WithConv.toConv g).ofConv a =
      TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g) (Coalgebra.comul a) := by
  rw [convMul_ofConv, dualDistrib_tmul_eq_mul'_comp_map]
  rfl

def dualMul : Module.Dual R A ⊗[R] Module.Dual R A →ₗ[R] Module.Dual R A :=
  (Coalgebra.comul (R := R) (A := A)).dualMap ∘ₗ TensorProduct.dualDistrib R A A

theorem dualMul_tmul (f g : Module.Dual R A) :
    dualMul R A (f ⊗ₜ[R] g) =
      (Coalgebra.comul (R := R) (A := A)).dualMap (TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g)) :=
  rfl

theorem dualMul_pairing (f g : Module.Dual R A) (a : A) :
    dualMul R A (f ⊗ₜ[R] g) a =
      TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g) (Coalgebra.comul a) := by
  rw [dualMul_tmul, LinearMap.dualMap_apply]

theorem dualMul_tmul_eq_convMul (f g : Module.Dual R A) :
    dualMul R A (f ⊗ₜ[R] g) = (WithConv.toConv f * WithConv.toConv g).ofConv := by
  ext a
  rw [convMul_ofConv_apply, dualMul_pairing]

theorem convOne_ofConv_eq_counit :
    ((1 : WithConv (Module.Dual R A))).ofConv = Coalgebra.counit (R := R) (A := A) := by
  ext a
  show algebraMap R R (Coalgebra.counit a) = Coalgebra.counit a
  simp

end TransposeOfComul

section TransposeOfMul

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]

theorem dualDistribEquiv_apply_eq (w : Module.Dual R A ⊗[R] Module.Dual R A) :
    TensorProduct.dualDistribEquiv R A A w = TensorProduct.dualDistrib R A A w := by
  rw [← LinearEquiv.coe_toLinearMap, TensorProduct.toLinearMap_dualDistribEquiv]

def dualComul : Module.Dual R A →ₗ[R] Module.Dual R A ⊗[R] Module.Dual R A :=
  (TensorProduct.dualDistribEquiv R A A).symm.toLinearMap ∘ₗ (LinearMap.mul' R A).dualMap

theorem dualDistrib_dualComul (φ : Module.Dual R A) :
    TensorProduct.dualDistrib R A A (dualComul R A φ) = (LinearMap.mul' R A).dualMap φ := by
  have h : dualComul R A φ =
      (TensorProduct.dualDistribEquiv R A A).symm ((LinearMap.mul' R A).dualMap φ) := rfl
  rw [h, ← dualDistribEquiv_apply_eq, LinearEquiv.apply_symm_apply]

theorem dualComul_pairing (φ : Module.Dual R A) (a b : A) :
    TensorProduct.dualDistrib R A A (dualComul R A φ) (a ⊗ₜ[R] b) = φ (a * b) := by
  rw [dualDistrib_dualComul, LinearMap.dualMap_apply, LinearMap.mul'_apply]

theorem dualComul_eq_of_dualDistrib_eq {φ : Module.Dual R A}
    {w : Module.Dual R A ⊗[R] Module.Dual R A}
    (h : TensorProduct.dualDistrib R A A w = (LinearMap.mul' R A).dualMap φ) :
    dualComul R A φ = w := by
  apply (TensorProduct.dualDistribEquiv R A A).injective
  rw [dualDistribEquiv_apply_eq, dualDistribEquiv_apply_eq, dualDistrib_dualComul, h]

theorem dualDistribEquiv_comp_dualComul :
    (TensorProduct.dualDistribEquiv R A A).toLinearMap ∘ₗ dualComul R A =
      (LinearMap.mul' R A).dualMap := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, dualDistribEquiv_apply_eq,
    dualDistrib_dualComul]

end TransposeOfMul

section UnitCounit

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

def dualOneEquiv : Module.Dual R R ≃ₗ[R] R := LinearMap.ringLmapEquivSelf R R R

theorem dualOneEquiv_apply (ψ : Module.Dual R R) : dualOneEquiv R ψ = ψ 1 := rfl

theorem dualOneEquiv_symm_apply (r x : R) : (dualOneEquiv R).symm r x = x * r := by
  have h1 : ((dualOneEquiv R).symm r) 1 = r := by
    have h := (dualOneEquiv R).apply_symm_apply r
    rwa [dualOneEquiv_apply] at h
  calc ((dualOneEquiv R).symm r) x = ((dualOneEquiv R).symm r) (x • (1 : R)) := by
        rw [smul_eq_mul, mul_one]
    _ = x • ((dualOneEquiv R).symm r) 1 := map_smul _ x 1
    _ = x * r := by rw [h1, smul_eq_mul]

def dualCounit : Module.Dual R A →ₗ[R] R :=
  (dualOneEquiv R).toLinearMap ∘ₗ (Algebra.linearMap R A).dualMap

theorem dualCounit_apply (φ : Module.Dual R A) : dualCounit R A φ = φ 1 := by
  have h : dualCounit R A φ = ((Algebra.linearMap R A).dualMap φ) 1 := rfl
  rw [h, LinearMap.dualMap_apply, Algebra.linearMap_apply, map_one]

def dualUnit : R →ₗ[R] Module.Dual R A :=
  (Coalgebra.counit (R := R) (A := A)).dualMap ∘ₗ (dualOneEquiv R).symm.toLinearMap

theorem dualUnit_apply (r : R) (a : A) :
    dualUnit R A r a = Coalgebra.counit (R := R) a * r := by
  have h : dualUnit R A r a = ((dualOneEquiv R).symm r) (Coalgebra.counit (R := R) a) := rfl
  rw [h, dualOneEquiv_symm_apply]

theorem dualUnit_eq_smul_counit (r : R) :
    dualUnit R A r = r • Coalgebra.counit (R := R) (A := A) := by
  ext a
  rw [dualUnit_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm]

theorem dualUnit_one : dualUnit R A 1 = Coalgebra.counit (R := R) (A := A) := by
  rw [dualUnit_eq_smul_counit, one_smul]

theorem convOne_ofConv_eq_dualUnit_one :
    ((1 : WithConv (Module.Dual R A))).ofConv = dualUnit R A 1 := by
  rw [dualUnit_one, convOne_ofConv_eq_counit]

end UnitCounit

section DerivableAxioms

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

theorem dualCounit_counit :
    dualCounit R A (Coalgebra.counit (R := R) (A := A)) = 1 := by
  rw [dualCounit_apply]
  exact Bialgebra.counit_one

theorem dualCounit_dualMul (f g : Module.Dual R A) :
    dualCounit R A (dualMul R A (f ⊗ₜ[R] g)) = dualCounit R A f * dualCounit R A g := by
  rw [dualCounit_apply, dualCounit_apply, dualCounit_apply, dualMul_pairing,
    Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.dualDistrib_apply]

variable [Module.Finite R A] [Module.Free R A]

theorem dualComul_counit :
    dualComul R A (Coalgebra.counit (R := R) (A := A)) =
      (Coalgebra.counit (R := R) (A := A)) ⊗ₜ[R] (Coalgebra.counit (R := R) (A := A)) := by
  apply dualComul_eq_of_dualDistrib_eq
  apply TensorProduct.ext'
  intro a b
  rw [TensorProduct.dualDistrib_apply, LinearMap.dualMap_apply, LinearMap.mul'_apply,
    Bialgebra.counit_mul]

end DerivableAxioms

section HeldLayer

variable (R : Type u) (A : Type v)

structure DualBialgebraAxioms [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] : Prop where

  coassoc_apply : ∀ φ : Module.Dual R A,
    TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
        ((dualComul R A).rTensor (Module.Dual R A) (dualComul R A φ)) =
      (dualComul R A).lTensor (Module.Dual R A) (dualComul R A φ)

  rTensor_counit_comul : ∀ φ : Module.Dual R A,
    (dualCounit R A).rTensor (Module.Dual R A) (dualComul R A φ) = (1 : R) ⊗ₜ[R] φ

  lTensor_counit_comul : ∀ φ : Module.Dual R A,
    (dualCounit R A).lTensor (Module.Dual R A) (dualComul R A φ) = φ ⊗ₜ[R] (1 : R)

  dualComul_dualMul : ∀ f g : Module.Dual R A,
    dualComul R A (dualMul R A (f ⊗ₜ[R] g)) =
      TensorProduct.map (dualMul R A) (dualMul R A)
        (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
          (Module.Dual R A) (Module.Dual R A) ((dualComul R A f) ⊗ₜ[R] (dualComul R A g)))

structure DualHopfAxioms [CommRing R] [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Free R A] : Prop extends DualBialgebraAxioms R A where

  mul_antipode_rTensor_comul : ∀ φ : Module.Dual R A,
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ)

  mul_antipode_lTensor_comul : ∀ φ : Module.Dual R A,
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ)

@[implicit_reducible] def coalgebraOfDualBialgebraAxioms [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] (h : DualBialgebraAxioms R A) :
    Coalgebra R (Module.Dual R A) where
  comul := dualComul R A
  counit := dualCounit R A
  coassoc := by
    apply LinearMap.ext
    intro φ
    simpa using h.coassoc_apply φ
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro φ
    simpa using h.rTensor_counit_comul φ
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro φ
    simpa using h.lTensor_counit_comul φ

end HeldLayer

end

noncomputable section

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

section PairingToolkit

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

instance : Module.Finite R (A ⊗[R] A) :=
  Module.Finite.of_basis (Module.Basis.tensorProduct
    (Module.Free.chooseBasis R A) (Module.Free.chooseBasis R A))

omit [Module.Finite R A] [Module.Free R A] in

theorem dualMul_apply_eq_pairing (w : Module.Dual R A ⊗[R] Module.Dual R A) (a : A) :
    dualMul R A w a = TensorProduct.dualDistrib R A A w (Coalgebra.comul a) := by
  show ((Coalgebra.comul (R := R) (A := A)).dualMap (TensorProduct.dualDistrib R A A w)) a = _
  rw [LinearMap.dualMap_apply]

theorem dualDistribEquiv_apply_eq₂ (w : Module.Dual R A ⊗[R] Module.Dual R (A ⊗[R] A)) :
    TensorProduct.dualDistribEquiv R A (A ⊗[R] A) w =
      TensorProduct.dualDistrib R A (A ⊗[R] A) w := by
  rw [← LinearEquiv.coe_toLinearMap, TensorProduct.toLinearMap_dualDistribEquiv]

def dualDistribEquiv₃ :
    Module.Dual R A ⊗[R] (Module.Dual R A ⊗[R] Module.Dual R A) ≃ₗ[R]
      Module.Dual R (A ⊗[R] (A ⊗[R] A)) :=
  (TensorProduct.congr (LinearEquiv.refl R (Module.Dual R A))
      (TensorProduct.dualDistribEquiv R A A)).trans
    (TensorProduct.dualDistribEquiv R A (A ⊗[R] A))

theorem dualDistribEquiv₃_tmul_pairing (f : Module.Dual R A)
    (v : Module.Dual R A ⊗[R] Module.Dual R A) (a : A) (z : A ⊗[R] A) :
    dualDistribEquiv₃ R A (f ⊗ₜ[R] v) (a ⊗ₜ[R] z) =
      f a * TensorProduct.dualDistrib R A A v z := by
  unfold dualDistribEquiv₃
  rw [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    dualDistribEquiv_apply_eq, dualDistribEquiv_apply_eq₂, TensorProduct.dualDistrib_apply]

theorem eq_of_dualDistribEquiv₃_pairing
    {x y : Module.Dual R A ⊗[R] (Module.Dual R A ⊗[R] Module.Dual R A)}
    (h : ∀ a b c : A,
      dualDistribEquiv₃ R A x (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
        dualDistribEquiv₃ R A y (a ⊗ₜ[R] (b ⊗ₜ[R] c))) :
    x = y := by
  apply (dualDistribEquiv₃ R A).injective
  apply TensorProduct.ext_threefold'
  exact h

end PairingToolkit

section Coassoc

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

theorem dualDistribEquiv₃_lTensor_dualComul (w : Module.Dual R A ⊗[R] Module.Dual R A)
    (a b c : A) :
    dualDistribEquiv₃ R A ((dualComul R A).lTensor (Module.Dual R A) w)
        (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      TensorProduct.dualDistrib R A A w (a ⊗ₜ[R] (b * c)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [LinearMap.lTensor_tmul, dualDistribEquiv₃_tmul_pairing, dualComul_pairing,
        TensorProduct.dualDistrib_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

theorem dualDistribEquiv₃_assoc_tmul (u : Module.Dual R A ⊗[R] Module.Dual R A)
    (h : Module.Dual R A) (a b c : A) :
    dualDistribEquiv₃ R A
        (TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
          (u ⊗ₜ[R] h)) (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      TensorProduct.dualDistrib R A A u (a ⊗ₜ[R] b) * h c := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
      rw [TensorProduct.assoc_tmul, dualDistribEquiv₃_tmul_pairing,
        TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply, mul_assoc]
  | add u₁ u₂ ih₁ ih₂ =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, add_mul, ih₁, ih₂]

theorem dualDistribEquiv₃_assoc_rTensor_dualComul (w : Module.Dual R A ⊗[R] Module.Dual R A)
    (a b c : A) :
    dualDistribEquiv₃ R A
        (TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
          ((dualComul R A).rTensor (Module.Dual R A) w)) (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      TensorProduct.dualDistrib R A A w ((a * b) ⊗ₜ[R] c) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [LinearMap.rTensor_tmul, dualDistribEquiv₃_assoc_tmul, dualComul_pairing,
        TensorProduct.dualDistrib_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

theorem coassoc_dualComul (φ : Module.Dual R A) :
    TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
        ((dualComul R A).rTensor (Module.Dual R A) (dualComul R A φ)) =
      (dualComul R A).lTensor (Module.Dual R A) (dualComul R A φ) := by
  apply eq_of_dualDistribEquiv₃_pairing
  intro a b c
  rw [dualDistribEquiv₃_assoc_rTensor_dualComul, dualDistribEquiv₃_lTensor_dualComul,
    dualComul_pairing, dualComul_pairing, mul_assoc]

end Coassoc

section CounitLaws

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

theorem lid_rTensor_dualCounit_apply (w : Module.Dual R A ⊗[R] Module.Dual R A) (a : A) :
    TensorProduct.lid R (Module.Dual R A) ((dualCounit R A).rTensor (Module.Dual R A) w) a =
      TensorProduct.dualDistrib R A A w ((1 : A) ⊗ₜ[R] a) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, dualCounit_apply,
        LinearMap.smul_apply, smul_eq_mul, TensorProduct.dualDistrib_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

omit [Module.Finite R A] [Module.Free R A] in

theorem rid_lTensor_dualCounit_apply (w : Module.Dual R A ⊗[R] Module.Dual R A) (a : A) :
    TensorProduct.rid R (Module.Dual R A) ((dualCounit R A).lTensor (Module.Dual R A) w) a =
      TensorProduct.dualDistrib R A A w (a ⊗ₜ[R] (1 : A)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, dualCounit_apply,
        LinearMap.smul_apply, smul_eq_mul, TensorProduct.dualDistrib_apply]
      ring
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

theorem rTensor_dualCounit_dualComul (φ : Module.Dual R A) :
    (dualCounit R A).rTensor (Module.Dual R A) (dualComul R A φ) = (1 : R) ⊗ₜ[R] φ := by
  apply (TensorProduct.lid R (Module.Dual R A)).injective
  ext a
  rw [lid_rTensor_dualCounit_apply, dualComul_pairing, one_mul, TensorProduct.lid_tmul, one_smul]

theorem lTensor_dualCounit_dualComul (φ : Module.Dual R A) :
    (dualCounit R A).lTensor (Module.Dual R A) (dualComul R A φ) = φ ⊗ₜ[R] (1 : R) := by
  apply (TensorProduct.rid R (Module.Dual R A)).injective
  ext a
  rw [rid_lTensor_dualCounit_apply, dualComul_pairing, mul_one, TensorProduct.rid_tmul, one_smul]

end CounitLaws

section Multiplicativity

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

theorem dualDistrib_map_dualMul_dualMul
    (T : (Module.Dual R A ⊗[R] Module.Dual R A) ⊗[R]
      (Module.Dual R A ⊗[R] Module.Dual R A)) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (dualMul R A) (dualMul R A) T) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)
        (TensorProduct.map (TensorProduct.dualDistrib R A A) (TensorProduct.dualDistrib R A A) T)
        (Coalgebra.comul a ⊗ₜ[R] Coalgebra.comul b) := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
      simp only [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply,
        dualMul_apply_eq_pairing]
  | add T₁ T₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

omit [Module.Finite R A] [Module.Free R A] in

theorem dualDistrib_map_dualDistrib_ttcomm :
    (TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)) ∘ₗ
        (TensorProduct.map (TensorProduct.dualDistrib R A A)
          (TensorProduct.dualDistrib R A A)) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
          (Module.Dual R A) (Module.Dual R A)).toLinearMap =
      ((TensorProduct.tensorTensorTensorComm R A A A A).toLinearMap.dualMap) ∘ₗ
        (TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)) ∘ₗ
        (TensorProduct.map (TensorProduct.dualDistrib R A A)
          (TensorProduct.dualDistrib R A A)) := by
  apply TensorProduct.ext_fourfold'
  intro p q r s
  apply TensorProduct.ext_fourfold'
  intro x₁ x₂ y₁ y₂
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.dualMap_apply, TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
    TensorProduct.dualDistrib_apply]
  ring

omit [Module.Finite R A] [Module.Free R A] in

theorem dualDistrib_map_dualDistrib_ttcomm_apply
    (T : (Module.Dual R A ⊗[R] Module.Dual R A) ⊗[R]
      (Module.Dual R A ⊗[R] Module.Dual R A))
    (W : (A ⊗[R] A) ⊗[R] (A ⊗[R] A)) :
    TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)
        (TensorProduct.map (TensorProduct.dualDistrib R A A) (TensorProduct.dualDistrib R A A)
          (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
            (Module.Dual R A) (Module.Dual R A) T)) W =
      TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)
        (TensorProduct.map (TensorProduct.dualDistrib R A A) (TensorProduct.dualDistrib R A A) T)
        (TensorProduct.tensorTensorTensorComm R A A A A W) := by
  have h := LinearMap.congr_fun
    (LinearMap.congr_fun (dualDistrib_map_dualDistrib_ttcomm R A) T) W
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap,
    LinearMap.dualMap_apply] using h

omit [Module.Finite R A] [Module.Free R A] in

theorem dualDistrib_dualMap_mul'_tmul (f g : Module.Dual R A)
    (W : (A ⊗[R] A) ⊗[R] (A ⊗[R] A)) :
    TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)
        (((LinearMap.mul' R A).dualMap f) ⊗ₜ[R] ((LinearMap.mul' R A).dualMap g)) W =
      TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g)
        (TensorProduct.map (LinearMap.mul' R A) (LinearMap.mul' R A) W) := by
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul Z W' =>
      simp only [TensorProduct.dualDistrib_apply, LinearMap.dualMap_apply,
        TensorProduct.map_tmul]
  | add W₁ W₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

omit [Module.Finite R A] [Module.Free R A] in

theorem map_mul'_mul'_ttcomm (X Y : A ⊗[R] A) :
    TensorProduct.map (LinearMap.mul' R A) (LinearMap.mul' R A)
        (TensorProduct.tensorTensorTensorComm R A A A A (X ⊗ₜ[R] Y)) = X * Y := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ x₂ =>
      induction Y using TensorProduct.induction_on with
      | zero => simp
      | tmul y₁ y₂ =>
          rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
            LinearMap.mul'_apply, LinearMap.mul'_apply, Algebra.TensorProduct.tmul_mul_tmul]
      | add Y₁ Y₂ ihY₁ ihY₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, ihY₁, ihY₂, mul_add]
  | add X₁ X₂ ihX₁ ihX₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add, ihX₁, ihX₂, add_mul]

theorem dualComul_dualMul_tmul (f g : Module.Dual R A) :
    dualComul R A (dualMul R A (f ⊗ₜ[R] g)) =
      TensorProduct.map (dualMul R A) (dualMul R A)
        (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
          (Module.Dual R A) (Module.Dual R A) ((dualComul R A f) ⊗ₜ[R] (dualComul R A g))) := by
  apply dualComul_eq_of_dualDistrib_eq
  apply TensorProduct.ext'
  intro a b
  rw [dualDistrib_map_dualMul_dualMul, dualDistrib_map_dualDistrib_ttcomm_apply,
    TensorProduct.map_tmul, dualDistrib_dualComul, dualDistrib_dualComul,
    dualDistrib_dualMap_mul'_tmul, map_mul'_mul'_ttcomm,
    LinearMap.dualMap_apply, LinearMap.mul'_apply, dualMul_pairing, Bialgebra.comul_mul]

end Multiplicativity

section BialgebraBundle

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

theorem dualBialgebraAxioms_of_finite_free : DualBialgebraAxioms R A where
  coassoc_apply := coassoc_dualComul R A
  rTensor_counit_comul := rTensor_dualCounit_dualComul R A
  lTensor_counit_comul := lTensor_dualCounit_dualComul R A
  dualComul_dualMul := dualComul_dualMul_tmul R A

@[implicit_reducible] def dualCoalgebraOfFiniteFree : Coalgebra R (Module.Dual R A) :=
  coalgebraOfDualBialgebraAxioms R A (dualBialgebraAxioms_of_finite_free R A)

end BialgebraBundle

section HopfDischarge

variable [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

theorem dualDistrib_rTensor_dualMap (S : A →ₗ[R] A)
    (w : Module.Dual R A ⊗[R] Module.Dual R A) :
    TensorProduct.dualDistrib R A A ((S.dualMap).rTensor (Module.Dual R A) w) =
      (TensorProduct.dualDistrib R A A w) ∘ₗ (S.rTensor A) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.rTensor_tmul, TensorProduct.dualDistrib_apply, LinearMap.comp_apply,
        LinearMap.dualMap_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, LinearMap.add_comp]

omit [Module.Finite R A] [Module.Free R A] in

theorem dualDistrib_lTensor_dualMap (S : A →ₗ[R] A)
    (w : Module.Dual R A ⊗[R] Module.Dual R A) :
    TensorProduct.dualDistrib R A A ((S.dualMap).lTensor (Module.Dual R A) w) =
      (TensorProduct.dualDistrib R A A w) ∘ₗ (S.lTensor A) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.lTensor_tmul, TensorProduct.dualDistrib_apply, LinearMap.comp_apply,
        LinearMap.dualMap_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, LinearMap.add_comp]

theorem dualMul_antipode_rTensor_dualComul (φ : Module.Dual R A) :
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ) := by
  ext a
  rw [dualMul_apply_eq_pairing, dualDistrib_rTensor_dualMap, LinearMap.comp_apply,
    dualDistrib_dualComul, LinearMap.dualMap_apply,
    HopfAlgebra.mul_antipode_rTensor_comul_apply, Algebra.algebraMap_eq_smul_one, map_smul,
    smul_eq_mul, dualUnit_apply, dualCounit_apply]

theorem dualMul_antipode_lTensor_dualComul (φ : Module.Dual R A) :
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ) := by
  ext a
  rw [dualMul_apply_eq_pairing, dualDistrib_lTensor_dualMap, LinearMap.comp_apply,
    dualDistrib_dualComul, LinearMap.dualMap_apply,
    HopfAlgebra.mul_antipode_lTensor_comul_apply, Algebra.algebraMap_eq_smul_one, map_smul,
    smul_eq_mul, dualUnit_apply, dualCounit_apply]

theorem dualHopfAxioms_of_finite_free : DualHopfAxioms R A where
  toDualBialgebraAxioms := dualBialgebraAxioms_of_finite_free R A
  mul_antipode_rTensor_comul := dualMul_antipode_rTensor_dualComul R A
  mul_antipode_lTensor_comul := dualMul_antipode_lTensor_dualComul R A

end HopfDischarge

end

noncomputable section

section ConvIdentities

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

theorem dualMul_assoc (f g h : Module.Dual R A) :
    dualMul R A (dualMul R A (f ⊗ₜ[R] g) ⊗ₜ[R] h) =
      dualMul R A (f ⊗ₜ[R] dualMul R A (g ⊗ₜ[R] h)) := by
  simp only [dualMul_tmul_eq_convMul, WithConv.toConv_ofConv]
  exact congrArg WithConv.ofConv
    (mul_assoc (WithConv.toConv f) (WithConv.toConv g) (WithConv.toConv h))

theorem dualMul_counit_tmul (f : Module.Dual R A) :
    dualMul R A ((Coalgebra.counit (R := R) (A := A)) ⊗ₜ[R] f) = f := by
  rw [dualMul_tmul_eq_convMul, ← convOne_ofConv_eq_counit R A, WithConv.toConv_ofConv]
  exact congrArg WithConv.ofConv (one_mul (WithConv.toConv f))

theorem dualMul_tmul_counit (f : Module.Dual R A) :
    dualMul R A (f ⊗ₜ[R] (Coalgebra.counit (R := R) (A := A))) = f := by
  rw [dualMul_tmul_eq_convMul, ← convOne_ofConv_eq_counit R A, WithConv.toConv_ofConv]
  exact congrArg WithConv.ofConv (mul_one (WithConv.toConv f))

theorem dualMul_dualUnit_tmul (r : R) (f : Module.Dual R A) :
    dualMul R A (dualUnit R A r ⊗ₜ[R] f) = r • f := by
  rw [dualUnit_eq_smul_counit, ← TensorProduct.smul_tmul', map_smul, dualMul_counit_tmul]

theorem dualMul_tmul_dualUnit (f : Module.Dual R A) (r : R) :
    dualMul R A (f ⊗ₜ[R] dualUnit R A r) = r • f := by
  rw [dualUnit_eq_smul_counit, TensorProduct.tmul_smul, map_smul, dualMul_tmul_counit]

theorem dualUnit_mul (r s : R) :
    dualUnit R A (r * s) = dualMul R A (dualUnit R A r ⊗ₜ[R] dualUnit R A s) := by
  rw [dualMul_tmul_dualUnit R A (dualUnit R A r) s, dualUnit_eq_smul_counit R A r,
    dualUnit_eq_smul_counit R A (r * s), smul_smul, mul_comm s r]

end ConvIdentities

section RingCarrier

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

@[reducible] def dualConvRing : Ring (Module.Dual R A) where
  __ := (inferInstance : AddCommMonoid (Module.Dual R A))
  __ := (inferInstance : AddCommGroup (Module.Dual R A))
  mul f g := dualMul R A (f ⊗ₜ[R] g)
  one := Coalgebra.counit (R := R) (A := A)
  mul_assoc := dualMul_assoc R A
  one_mul := dualMul_counit_tmul R A
  mul_one := dualMul_tmul_counit R A
  left_distrib f g h := by
    show dualMul R A (f ⊗ₜ[R] (g + h)) = dualMul R A (f ⊗ₜ[R] g) + dualMul R A (f ⊗ₜ[R] h)
    rw [TensorProduct.tmul_add, map_add]
  right_distrib f g h := by
    show dualMul R A ((f + g) ⊗ₜ[R] h) = dualMul R A (f ⊗ₜ[R] h) + dualMul R A (g ⊗ₜ[R] h)
    rw [TensorProduct.add_tmul, map_add]
  zero_mul f := by
    show dualMul R A ((0 : Module.Dual R A) ⊗ₜ[R] f) = 0
    rw [TensorProduct.zero_tmul, map_zero]
  mul_zero f := by
    show dualMul R A (f ⊗ₜ[R] (0 : Module.Dual R A)) = 0
    rw [TensorProduct.tmul_zero, map_zero]

theorem dualConvRing_one :
    letI : Ring (Module.Dual R A) := dualConvRing R A;
    (1 : Module.Dual R A) = Coalgebra.counit (R := R) (A := A) := rfl

theorem dualConvRing_mul (f g : Module.Dual R A) :
    letI : Ring (Module.Dual R A) := dualConvRing R A;
    f * g = dualMul R A (f ⊗ₜ[R] g) := rfl

theorem dualConvRing_mul_eq_convMul (f g : Module.Dual R A) :
    letI : Ring (Module.Dual R A) := dualConvRing R A;
    f * g = (WithConv.toConv f * WithConv.toConv g).ofConv :=
  Eq.trans (dualConvRing_mul R A f g) (dualMul_tmul_eq_convMul R A f g)

@[reducible] def dualConvCommRing [IsCocomm R A] : CommRing (Module.Dual R A) where
  __ := dualConvRing R A
  mul_comm f g := by
    show dualMul R A (f ⊗ₜ[R] g) = dualMul R A (g ⊗ₜ[R] f)
    simp only [dualMul_tmul_eq_convMul]
    exact congrArg WithConv.ofConv (mul_comm (WithConv.toConv f) (WithConv.toConv g))

end RingCarrier

section AlgebraCarrier

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

attribute [local instance] dualConvRing

@[reducible] def dualConvAlgebra : Algebra R (Module.Dual R A) where
  toSMul := (inferInstance : SMul R (Module.Dual R A))
  algebraMap :=
    { toFun := fun r => dualUnit R A r
      map_one' := dualUnit_one R A
      map_mul' := fun r s => dualUnit_mul R A r s
      map_zero' := map_zero (dualUnit R A)
      map_add' := fun r s => map_add (dualUnit R A) r s }
  commutes' := fun r f => (dualMul_dualUnit_tmul R A r f).trans (dualMul_tmul_dualUnit R A f r).symm
  smul_def' := fun r f => (dualMul_dualUnit_tmul R A r f).symm

attribute [local instance] dualConvAlgebra

theorem dualConvAlgebra_algebraMap (r : R) :
    algebraMap R (Module.Dual R A) r = dualUnit R A r := rfl

theorem dualConvAlgebra_algebraMap_eq_smul_counit (r : R) :
    algebraMap R (Module.Dual R A) r = r • Coalgebra.counit (R := R) (A := A) :=
  (dualConvAlgebra_algebraMap R A r).trans (dualUnit_eq_smul_counit R A r)

end AlgebraCarrier

section BialgebraPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]

attribute [local instance] dualConvRing dualConvAlgebra dualCoalgebraOfFiniteFree

theorem dualComul_counit_eq_tensorOne :
    dualComul R A (Coalgebra.counit (R := R) (A := A)) =
      (1 : Module.Dual R A ⊗[R] Module.Dual R A) := by
  rw [Algebra.TensorProduct.one_def]
  exact dualComul_counit R A

theorem dualComul_dualMul_eq_mul (f g : Module.Dual R A) :
    dualComul R A (dualMul R A (f ⊗ₜ[R] g)) = dualComul R A f * dualComul R A g := by
  rw [dualComul_dualMul_tmul R A f g]
  generalize dualComul R A f = X
  generalize dualComul R A g = Y
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
      induction Y using TensorProduct.induction_on with
      | zero => simp
      | tmul r s =>
          rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul]
          exact (Algebra.TensorProduct.tmul_mul_tmul p r q s).symm
      | add Y₁ Y₂ ih₁ ih₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, mul_add, ih₁, ih₂]
  | add X₁ X₂ ih₁ ih₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add, add_mul, ih₁, ih₂]

@[reducible] def dualBialgebraOfFiniteFree : Bialgebra R (Module.Dual R A) :=
  Bialgebra.mk' R (Module.Dual R A)
    (dualCounit_counit R A)
    (fun {f g} => dualCounit_dualMul R A f g)
    (dualComul_counit_eq_tensorOne R A)
    (fun {f g} => dualComul_dualMul_eq_mul R A f g)

theorem dualBialgebraOfFiniteFree_toAlgebra :
    (dualBialgebraOfFiniteFree R A).toAlgebra = dualConvAlgebra R A := rfl

theorem dualBialgebraOfFiniteFree_toCoalgebra :
    (dualBialgebraOfFiniteFree R A).toCoalgebra = dualCoalgebraOfFiniteFree R A := rfl

end BialgebraPackage

section HopfPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]

attribute [local instance] dualConvRing dualConvAlgebra dualCoalgebraOfFiniteFree

theorem dualConv_mul'_antipode_rTensor_dualComul :
    LinearMap.mul' R (Module.Dual R A) ∘ₗ
        ((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A) ∘ₗ
        dualComul R A =
      Algebra.linearMap R (Module.Dual R A) ∘ₗ dualCounit R A := by
  refine LinearMap.ext fun φ => ?_
  simp only [LinearMap.comp_apply]
  show LinearMap.mul' R (Module.Dual R A)
      (((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A)
        (dualComul R A φ)) =
    dualUnit R A (dualCounit R A φ)
  have hmul' : ∀ w : Module.Dual R A ⊗[R] Module.Dual R A,
      LinearMap.mul' R (Module.Dual R A) w = dualMul R A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => exact LinearMap.mul'_apply
    | add w₁ w₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
  rw [hmul']
  exact dualMul_antipode_rTensor_dualComul R A φ

theorem dualConv_mul'_antipode_lTensor_dualComul :
    LinearMap.mul' R (Module.Dual R A) ∘ₗ
        ((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A) ∘ₗ
        dualComul R A =
      Algebra.linearMap R (Module.Dual R A) ∘ₗ dualCounit R A := by
  refine LinearMap.ext fun φ => ?_
  simp only [LinearMap.comp_apply]
  show LinearMap.mul' R (Module.Dual R A)
      (((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A)
        (dualComul R A φ)) =
    dualUnit R A (dualCounit R A φ)
  have hmul' : ∀ w : Module.Dual R A ⊗[R] Module.Dual R A,
      LinearMap.mul' R (Module.Dual R A) w = dualMul R A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => exact LinearMap.mul'_apply
    | add w₁ w₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
  rw [hmul']
  exact dualMul_antipode_lTensor_dualComul R A φ

@[reducible] def dualHopfAlgebraOfFiniteFree : HopfAlgebra R (Module.Dual R A) where
  toBialgebra := dualBialgebraOfFiniteFree R A
  antipode := (HopfAlgebra.antipode R (A := A)).dualMap
  mul_antipode_rTensor_comul := dualConv_mul'_antipode_rTensor_dualComul R A
  mul_antipode_lTensor_comul := dualConv_mul'_antipode_lTensor_dualComul R A

attribute [local instance] dualHopfAlgebraOfFiniteFree

theorem dualHopfAlgebraOfFiniteFree_antipode :
    HopfAlgebra.antipode R (A := Module.Dual R A) =
      (HopfAlgebra.antipode R (A := A)).dualMap := rfl

end HopfPackage

end

noncomputable section

section PairingSwap

variable (R : Type u) (A : Type v) [CommRing R] [AddCommMonoid A] [Module R A]

theorem dualDistrib_comm_apply (w : Module.Dual R A ⊗[R] Module.Dual R A) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) w) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R A A w (b ⊗ₜ[R] a) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [TensorProduct.comm_tmul, TensorProduct.dualDistrib_apply,
        TensorProduct.dualDistrib_apply]
      exact mul_comm (g a) (f b)
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

end PairingSwap

section Cocomm

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]

theorem dualDistrib_comm_dualComul_pairing (φ : Module.Dual R A) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) (dualComul R A φ))
        (a ⊗ₜ[R] b) =
      φ (b * a) := by
  rw [dualDistrib_comm_apply, dualComul_pairing]

theorem comm_dualComul (φ : Module.Dual R A) :
    TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) (dualComul R A φ) =
      dualComul R A φ := by
  symm
  apply dualComul_eq_of_dualDistrib_eq
  apply TensorProduct.ext'
  intro a b
  rw [dualDistrib_comm_dualComul_pairing, LinearMap.dualMap_apply, LinearMap.mul'_apply]
  exact congrArg φ (mul_comm b a)

theorem comm_comp_dualComul :
    (TensorProduct.comm R (Module.Dual R A) (Module.Dual R A)).toLinearMap ∘ₗ dualComul R A =
      dualComul R A :=
  LinearMap.ext fun φ => comm_dualComul R A φ

theorem dualCoalgebraOfFiniteFree_isCocomm :
    letI : Coalgebra R (Module.Dual R A) := dualCoalgebraOfFiniteFree R A
    Coalgebra.IsCocomm R (Module.Dual R A) := by
  letI : Coalgebra R (Module.Dual R A) := dualCoalgebraOfFiniteFree R A
  refine ⟨LinearMap.ext fun φ => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  show TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) (dualComul R A φ) =
    dualComul R A φ
  exact comm_dualComul R A φ

end Cocomm

section CommBialgebraPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]

attribute [local instance] dualConvCommRing dualConvAlgebra dualCoalgebraOfFiniteFree

@[reducible] def dualCommBialgebraOfFiniteFree : Bialgebra R (Module.Dual R A) :=
  Bialgebra.mk' R (Module.Dual R A)
    (dualCounit_counit R A)
    (fun {f g} => dualCounit_dualMul R A f g)
    (dualComul_counit_eq_tensorOne R A)
    (fun {f g} => dualComul_dualMul_eq_mul R A f g)

theorem dualCommBialgebraOfFiniteFree_toAlgebra :
    (dualCommBialgebraOfFiniteFree R A).toAlgebra = dualConvAlgebra R A := rfl

theorem dualCommBialgebraOfFiniteFree_toCoalgebra :
    (dualCommBialgebraOfFiniteFree R A).toCoalgebra = dualCoalgebraOfFiniteFree R A := rfl

theorem dualCommBialgebraOfFiniteFree_eq_dualBialgebraOfFiniteFree :
    dualCommBialgebraOfFiniteFree R A = dualBialgebraOfFiniteFree R A := rfl

theorem dualCommBialgebraOfFiniteFree_isCocomm :
    letI : Coalgebra R (Module.Dual R A) := (dualCommBialgebraOfFiniteFree R A).toCoalgebra
    Coalgebra.IsCocomm R (Module.Dual R A) := by
  letI : Coalgebra R (Module.Dual R A) := (dualCommBialgebraOfFiniteFree R A).toCoalgebra
  refine ⟨LinearMap.ext fun φ => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  show TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) (dualComul R A φ) =
    dualComul R A φ
  exact comm_dualComul R A φ

end CommBialgebraPackage

section CommHopfPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]

attribute [local instance] dualConvCommRing dualConvAlgebra dualCoalgebraOfFiniteFree

@[reducible] def dualCommHopfAlgebraOfFiniteFree : HopfAlgebra R (Module.Dual R A) where
  toBialgebra := dualCommBialgebraOfFiniteFree R A
  antipode := (HopfAlgebra.antipode R (A := A)).dualMap
  mul_antipode_rTensor_comul := dualConv_mul'_antipode_rTensor_dualComul R A
  mul_antipode_lTensor_comul := dualConv_mul'_antipode_lTensor_dualComul R A

theorem dualCommHopfAlgebraOfFiniteFree_toBialgebra :
    (dualCommHopfAlgebraOfFiniteFree R A).toBialgebra = dualCommBialgebraOfFiniteFree R A := rfl

theorem dualCommHopfAlgebraOfFiniteFree_eq_dualHopfAlgebraOfFiniteFree :
    dualCommHopfAlgebraOfFiniteFree R A = dualHopfAlgebraOfFiniteFree R A := rfl

attribute [local instance] dualCommHopfAlgebraOfFiniteFree

theorem dualCommHopfAlgebraOfFiniteFree_antipode :
    HopfAlgebra.antipode R (A := Module.Dual R A) =
      (HopfAlgebra.antipode R (A := A)).dualMap := rfl

end CommHopfPackage

end

noncomputable section

section Instances

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

instance instAddCommGroup : AddCommGroup (CartierDual R A) :=
  inferInstanceAs (AddCommGroup (Module.Dual R A))

instance instModule : Module R (CartierDual R A) :=
  inferInstanceAs (Module R (Module.Dual R A))

instance instRing : Ring (CartierDual R A) :=
  { instAddCommGroup R A, dualConvRing R A with }

instance instCommRing [IsCocomm R A] : CommRing (CartierDual R A) :=
  { instRing R A with mul_comm := fun f g => (dualConvCommRing R A).mul_comm f g }

instance instAlgebra : Algebra R (CartierDual R A) :=
  { dualConvAlgebra R A with toSMul := (instModule R A).toDistribMulAction.toMulAction.toSMul }

instance instFunLike : FunLike (CartierDual R A) A R :=
  inferInstanceAs (FunLike (A →ₗ[R] R) A R)

instance instLinearMapClass : LinearMapClass (CartierDual R A) R A R :=
  inferInstanceAs (LinearMapClass (A →ₗ[R] R) R A R)

def toDual : CartierDual R A ≃ₗ[R] Module.Dual R A where
  toFun φ := φ
  invFun φ := φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def ofDual : Module.Dual R A ≃ₗ[R] CartierDual R A := (toDual R A).symm

variable {R A}

@[simp] theorem toDual_apply (φ : CartierDual R A) (a : A) : toDual R A φ a = φ a := rfl
@[simp] theorem ofDual_apply (φ : Module.Dual R A) (a : A) : ofDual R A φ a = φ a := rfl
@[simp] theorem toDual_ofDual (φ : Module.Dual R A) : toDual R A (ofDual R A φ) = φ := rfl
@[simp] theorem ofDual_toDual (φ : CartierDual R A) : ofDual R A (toDual R A φ) = φ := rfl

@[ext] theorem ext {φ ψ : CartierDual R A} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  LinearMap.ext (M := A) (f := (φ : Module.Dual R A)) (g := (ψ : Module.Dual R A)) h

theorem mul_def (φ ψ : CartierDual R A) :
    φ * ψ = ofDual R A (dualMul R A (toDual R A φ ⊗ₜ[R] toDual R A ψ)) := rfl

theorem mul_apply (φ ψ : CartierDual R A) (a : A) :
    (φ * ψ) a = TensorProduct.dualDistrib R A A
      (toDual R A φ ⊗ₜ[R] toDual R A ψ) (Coalgebra.comul a) :=
  dualMul_pairing R A _ _ a

theorem mul_eq_convMul (φ ψ : CartierDual R A) :
    toDual R A (φ * ψ) = (WithConv.toConv (toDual R A φ) * WithConv.toConv (toDual R A ψ)).ofConv :=
  dualMul_tmul_eq_convMul R A _ _

theorem toDual_mul (φ ψ : CartierDual R A) :
    toDual R A (φ * ψ) = (WithConv.toConv (toDual R A φ) * WithConv.toConv (toDual R A ψ)).ofConv :=
  mul_eq_convMul φ ψ

theorem one_def : (1 : CartierDual R A) = ofDual R A (Coalgebra.counit (R := R) (A := A)) := rfl

@[simp] theorem one_apply (a : A) : (1 : CartierDual R A) a = Coalgebra.counit (R := R) a := rfl

theorem algebraMap_def (r : R) :
    algebraMap R (CartierDual R A) r = ofDual R A (dualUnit R A r) := rfl

@[simp] theorem algebraMap_apply (r : R) (a : A) :
    algebraMap R (CartierDual R A) r a = Coalgebra.counit (R := R) a * r :=
  dualUnit_apply R A r a

variable (R A)
variable [Module.Finite R A] [Module.Free R A]

instance instModuleFinite : Module.Finite R (CartierDual R A) :=
  inferInstanceAs (Module.Finite R (Module.Dual R A))

instance instModuleFree : Module.Free R (CartierDual R A) :=
  inferInstanceAs (Module.Free R (Module.Dual R A))

theorem finrank_eq [Nontrivial R] : Module.finrank R (CartierDual R A) = Module.finrank R A :=
  Module.finrank_linearMap_self R R A

instance instCoalgebra : Coalgebra R (CartierDual R A) := { dualCoalgebraOfFiniteFree R A with }

instance instBialgebra : Bialgebra R (CartierDual R A) :=
  { instAlgebra R A, instCoalgebra R A, dualBialgebraOfFiniteFree R A with }

instance instIsCocomm : IsCocomm R (CartierDual R A) :=
  ⟨(dualCoalgebraOfFiniteFree_isCocomm R A).comm_comp_comul⟩

variable {R A}

theorem comul_def (φ : CartierDual R A) :
    TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap
        (Coalgebra.comul (R := R) φ) =
      dualComul R A (toDual R A φ) := by
  have hid : TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap =
      (LinearMap.id : Module.Dual R A ⊗[R] Module.Dual R A →ₗ[R]
        Module.Dual R A ⊗[R] Module.Dual R A) :=
    TensorProduct.ext' fun _ _ => rfl
  rw [hid]
  rfl

theorem comul_pairing (φ : CartierDual R A) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap
          (Coalgebra.comul (R := R) φ))
        (a ⊗ₜ[R] b) = φ (a * b) := by
  rw [comul_def]
  exact dualComul_pairing R A _ a b

theorem comul_eq_dualComul (φ : CartierDual R A) :
    (Coalgebra.comul (R := R) φ : CartierDual R A ⊗[R] CartierDual R A) =
      dualComul R A (toDual R A φ) := rfl

theorem counit_eq_dualCounit (φ : CartierDual R A) :
    Coalgebra.counit (R := R) φ = dualCounit R A (toDual R A φ) := rfl

theorem tmul_eq_of_pairing_eq {x y : CartierDual R A ⊗[R] CartierDual R A}
    (h : ∀ a b : A,
      TensorProduct.dualDistrib R A A
          (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap x) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R A A
          (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap y) (a ⊗ₜ[R] b)) :
    x = y := by
  have hid : TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap =
      (LinearMap.id : Module.Dual R A ⊗[R] Module.Dual R A →ₗ[R]
        Module.Dual R A ⊗[R] Module.Dual R A) :=
    TensorProduct.ext' fun _ _ => rfl
  rw [hid] at h
  have hinj : Function.Injective (TensorProduct.dualDistrib R A A) := by
    rw [← TensorProduct.toLinearMap_dualDistribEquiv]
    exact (TensorProduct.dualDistribEquiv R A A).injective
  exact hinj (TensorProduct.ext' fun a b => h a b)

@[simp] theorem counit_apply (φ : CartierDual R A) : Coalgebra.counit (R := R) φ = φ 1 :=
  dualCounit_apply R A _

end Instances

section HopfInstance

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]

instance instHopfAlgebra : HopfAlgebra R (CartierDual R A) :=
  { instBialgebra R A, dualHopfAlgebraOfFiniteFree R A with }

variable {R A}

@[simp] theorem antipode_apply (φ : CartierDual R A) (a : A) :
    (HopfAlgebra.antipode R (A := CartierDual R A) φ) a =
      φ (HopfAlgebra.antipode R (A := A) a) := rfl

end HopfInstance

section BidualSanity
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]
example : Ring (CartierDual R (CartierDual R A)) := inferInstance
example : CommRing (CartierDual R (CartierDual R A)) := inferInstance
example : Bialgebra R (CartierDual R (CartierDual R A)) := inferInstance
example : IsCocomm R (CartierDual R (CartierDual R A)) := inferInstance
end BidualSanity

section BidualSanityHopf
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]
example : HopfAlgebra R (CartierDual R (CartierDual R A)) := inferInstance
end BidualSanityHopf

end


section Pairing

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

def pairing : CartierDual R A →ₗ[R] A →ₗ[R] R where
  toFun φ := toDual R A φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pairing_apply (φ : CartierDual R A) (a : A) : pairing R A φ a = φ a := rfl

end Pairing

section Map

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {B : Type w} [CommRing B] [Bialgebra R B] [Module.Finite R B] [Module.Free R B]
variable {C : Type x} [CommRing C] [Bialgebra R C] [Module.Finite R C] [Module.Free R C]

def mapLinear (f : A →ₐc[R] B) : CartierDual R B →ₗ[R] CartierDual R A :=
  (ofDual R A).toLinearMap ∘ₗ (f : A →ₗ[R] B).dualMap ∘ₗ (toDual R B).toLinearMap

@[simp] theorem mapLinear_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    mapLinear f φ a = φ (f a) := rfl

theorem dualDistrib_map_map (f : A →ₐc[R] B) (φ ψ : CartierDual R B) (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R B B (toDual R B φ ⊗ₜ[R] toDual R B ψ)
        (TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B) z) =
      TensorProduct.dualDistrib R A A
        (toDual R A (mapLinear f φ) ⊗ₜ[R] toDual R A (mapLinear f ψ)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mapLinear_mul (f : A →ₐc[R] B) (φ ψ : CartierDual R B) :
    mapLinear f (φ * ψ) = mapLinear f φ * mapLinear f ψ := by
  apply CartierDual.ext; intro a
  rw [mapLinear_apply, mul_apply, mul_apply, ← dualDistrib_map_map]
  congr 1
  exact (CoalgHomClass.map_comp_comul_apply f a).symm

theorem mapLinear_one (f : A →ₐc[R] B) : mapLinear f 1 = 1 := by
  apply CartierDual.ext; intro a
  rw [mapLinear_apply, one_apply, one_apply]
  exact CoalgHomClass.counit_comp_apply f a

def mapAlgHom (f : A →ₐc[R] B) : CartierDual R B →ₐ[R] CartierDual R A :=
  AlgHom.ofLinearMap (mapLinear f) (mapLinear_one f) (mapLinear_mul f)

@[simp] theorem mapAlgHom_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    mapAlgHom f φ a = φ (f a) := rfl

theorem dualDistrib_map_mapAlgHom (f : A →ₐc[R] B)
    (w : CartierDual R B ⊗[R] CartierDual R B) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap
          (TensorProduct.map (mapLinear f) (mapLinear f) w)) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R B B
        (TensorProduct.map (toDual R B).toLinearMap (toDual R B).toLinearMap w)
        (f a ⊗ₜ[R] f b) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul φ ψ => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem counit_comp_mapAlgHom (f : A →ₐc[R] B) :
    (Bialgebra.counitAlgHom R (CartierDual R A)).comp (mapAlgHom f) =
      Bialgebra.counitAlgHom R (CartierDual R B) := by
  apply AlgHom.ext; intro φ
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
  exact (counit_apply (mapAlgHom f φ)).trans ((congrArg φ (map_one f)).trans (counit_apply φ).symm)

theorem map_comp_comul_mapAlgHom (f : A →ₐc[R] B) :
    (Algebra.TensorProduct.map (mapAlgHom f) (mapAlgHom f)).comp
        (Bialgebra.comulAlgHom R (CartierDual R B)) =
      (Bialgebra.comulAlgHom R (CartierDual R A)).comp (mapAlgHom f) := by
  apply AlgHom.ext; intro φ
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    Bialgebra.comulAlgHom_apply]
  have hmap : (Algebra.TensorProduct.map (mapAlgHom f) (mapAlgHom f)).toLinearMap =
      TensorProduct.map (mapLinear f) (mapLinear f) := TensorProduct.ext' fun _ _ => rfl
  rw [← AlgHom.toLinearMap_apply, hmap]
  apply tmul_eq_of_pairing_eq
  intro a b
  have h1 := dualDistrib_map_mapAlgHom f (Coalgebra.comul (R := R) φ) a b
  have h2 := comul_pairing (R := R) (A := B) φ (f a) (f b)
  have h3 := comul_pairing (R := R) (A := A) (mapAlgHom f φ) a b
  exact (h1.trans (h2.trans (congrArg φ (map_mul f a b).symm))).trans h3.symm

noncomputable def map (f : A →ₐc[R] B) : CartierDual R B →ₐc[R] CartierDual R A :=
  BialgHom.ofAlgHom (mapAlgHom f) (counit_comp_mapAlgHom f) (map_comp_comul_mapAlgHom f)

@[simp] theorem map_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    map f φ a = φ (f a) := rfl

theorem toDual_map (f : A →ₐc[R] B) (φ : CartierDual R B) :
    toDual R A (map f φ) = (f : A →ₗ[R] B).dualMap (toDual R B φ) := rfl

theorem map_id : map (BialgHom.id R A) = BialgHom.id R (CartierDual R A) := by
  apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a; rfl

theorem map_comp (g : B →ₐc[R] C) (f : A →ₐc[R] B) :
    map (g.comp f) = (map f).comp (map g) := by
  apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a; rfl

noncomputable def congr (e : A ≃ₐc[R] B) : CartierDual R B ≃ₐc[R] CartierDual R A :=
  BialgEquiv.ofBialgHom (map (e : A →ₐc[R] B)) (map (e.symm : B →ₐc[R] A))
    (by apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a
        change φ (e.symm (e a)) = φ a
        rw [BialgEquiv.symm_apply_apply])
    (by apply BialgHom.ext; intro φ; apply CartierDual.ext; intro b
        change φ (e (e.symm b)) = φ b
        rw [BialgEquiv.apply_symm_apply])

@[simp] theorem congr_apply (e : A ≃ₐc[R] B) (φ : CartierDual R B) (a : A) :
    congr e φ a = φ (e a) := rfl

@[simp] theorem congr_symm_apply (e : A ≃ₐc[R] B) (φ : CartierDual R A) (b : B) :
    (congr e).symm φ b = φ (e.symm b) := rfl

end Map

end CartierDual
