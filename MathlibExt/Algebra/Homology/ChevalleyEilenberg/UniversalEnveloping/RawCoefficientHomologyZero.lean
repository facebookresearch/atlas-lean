/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RawCoefficientResolutionHeight
public import MathlibExt.Algebra.Homology.ShortComplex.MapHomologyOpcycles

/-!
# Degree-zero coefficient classes and enveloping tensors

Degree-zero Chevalley–Eilenberg homology with Lie coefficients identifies with the balanced
tensor of their right enveloping representation and the trivial enveloping module. The
empty-exterior class of m maps to `m ⊗ 1`.

This comparison commutes with coefficient and output universe lifts. For a free underlying Lie
module, the degree-zero homology-to-Tor comparison agrees with the canonical derived-zero
augmentation.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z a b c

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex coefficientComplexULift HomologicalComplex.homologyFunctor
  rawLieCoefficientLiftAt

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (M : LieModuleCat.{w} R L)

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The raw CE input transport carries the empty-exterior class to the empty-exterior class of the
lifted coefficient. -/
theorem rawCoefficientHomologyTransportAt_zero_class (m : M) :
    (rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0).hom
      (ULift.up ((coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)))) =
    (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).isoHomologyι₀.inv
      ((coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).pOpcycles 0
        (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R]
          (ULift.up m : (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)))) := by
  let K := coefficientComplex R L M
  let Q := coefficientComplexULift.{u, v, w, max u v v' w w' z} R L M
  let W := ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R
  letI : W.PreservesHomology := Functor.preservesHomologyOfExact W
  let eH := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 0 W).app K
  let eO := (K.sc 0).mapOpcyclesIso W
  let E := coefficientULiftComplexIso.{u, v, w, max u v v' w w' z} R L M
  let p : K.X 0 := exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m
  have hp : W.map (K.pOpcycles 0) ≫ eO.inv = Q.pOpcycles 0 := by
    apply (cancel_mono eO.hom).1
    have hCancel : (W.map (K.pOpcycles 0) ≫ eO.inv) ≫ eO.hom = W.map (K.pOpcycles 0) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => W.map (K.pOpcycles 0) ≫ q) eO.inv_hom_id).trans (Category.comp_id _))
    exact hCancel.trans (ShortComplex.pOpcycles_comp_mapOpcyclesIso_hom (K.sc 0) W).symm
  have hι : W.map K.isoHomologyι₀.inv ≫ eH.inv = eO.inv ≫ Q.isoHomologyι₀.inv := by
    apply (cancel_mono Q.isoHomologyι₀.hom).1
    have hCancel : (eO.inv ≫ Q.isoHomologyι₀.inv) ≫ Q.isoHomologyι₀.hom = eO.inv :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => eO.inv ≫ q) Q.isoHomologyι₀.inv_hom_id).trans (Category.comp_id _))
    refine Eq.trans ?_ hCancel.symm
    change W.map K.isoHomologyι₀.inv ≫ ((K.sc 0).mapHomologyIso W).inv ≫
      ((K.sc 0).map W).homologyι = eO.inv
    have hInv := ShortComplex.mapHomologyIso_inv_comp_homologyι (K.sc 0) W
    have hMap : W.map K.isoHomologyι₀.inv ≫ W.map K.isoHomologyι₀.hom = 𝟙 _ :=
      (W.map_comp _ _).symm.trans
        ((congrArg W.map K.isoHomologyι₀.inv_hom_id).trans (W.map_id _))
    exact (congrArg (fun q => W.map K.isoHomologyι₀.inv ≫ q) hInv).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ eO.inv) hMap).trans (Category.id_comp _)))
  have hClass : W.map (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) ≫ eH.inv =
      Q.pOpcycles 0 ≫ Q.isoHomologyι₀.inv := by
    exact (congrArg (fun q => q ≫ eH.inv) (W.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun q => W.map (K.pOpcycles 0) ≫ q) hι).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ Q.isoHomologyι₀.inv) hp))))
  have hLift := congrArg
    (fun f : W.obj (K.X 0) ⟶ Q.homology 0 => f.hom (ULift.up p)) hClass
  change eH.inv.hom (ULift.up (K.isoHomologyι₀.inv.hom ((K.pOpcycles 0).hom p))) =
    Q.isoHomologyι₀.inv.hom ((Q.pOpcycles 0).hom (ULift.up p)) at hLift
  have hEι := congrArg
    (fun f : Q.opcycles 0 ⟶ (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).homology 0 =>
      f.hom ((Q.pOpcycles 0).hom (ULift.up p)))
    (ChainComplex.isoHomologyι₀_inv_naturality E.hom)
  have hEp := congrArg
    (fun f : Q.X 0 ⟶ (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).opcycles 0 =>
      f.hom (ULift.up p))
    (HomologicalComplex.p_opcyclesMap E.hom 0)
  have hEx : (E.hom.f 0).hom (ULift.up p) =
      exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R]
        (ULift.up m : (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :=
    coefficientULiftDegreeEquiv_up_tmul R L M 0 _ m
  change (HomologicalComplex.homologyMap E.hom 0).hom
    (eH.inv.hom (ULift.up (K.isoHomologyι₀.inv.hom ((K.pOpcycles 0).hom p)))) = _
  rw [hLift]
  exact hEι.trans (congrArg
    (fun a : (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).opcycles 0 =>
      (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).isoHomologyι₀.inv.hom a)
    (hEp.trans
      (congrArg
      (fun a => ((coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).pOpcycles 0).hom a)
      hEx)))

/-- Coefficient down on the trivial-module tensor returns the raw right-representation balanced
quotient. -/
def rawCoefficientTrivialTensorEquiv :
    (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))).obj (envelopingTrivialObject R L) ≃ₗ[R]
      (ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
        (envelopingTrivialObject R L) :=
  by
    let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
    let N := LieModuleCat.RightUniversalEnveloping.representObj R L M
    let T := (ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)
    let e := LieModuleCat.RightUniversalEnveloping.coefficientULiftGroundEquiv.{u, v, w,
      max u v v' w w' z} R L M
    have h : ∀ (a : U)
        (m : (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N₁),
        e (MulOpposite.op a • m) = MulOpposite.op a • e m :=
      fun a m => (LieModuleCat.RightUniversalEnveloping.coefficientULiftEquiv.{u, v, w,
        max u v v' w w' z} R L M).map_smul (MulOpposite.op a) m
    exact TensorProduct.Balanced.congr (k := R) (R := U)
      (M := (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N₁)
      (M' := (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N) (N := T) (N' := T)
      e (LinearEquiv.refl R T) h (fun _ _ => rfl)

@[simp]
theorem rawCoefficientTrivialTensorEquiv_mk_up (m : M) (x : envelopingTrivialObject R L) :
    rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M
      (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          (ULift.up m) x) =
    TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
      ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m x := by
  let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
  let N := LieModuleCat.RightUniversalEnveloping.representObj R L M
  let T := (ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)
  let e := LieModuleCat.RightUniversalEnveloping.coefficientULiftGroundEquiv.{u, v, w,
    max u v v' w w' z} R L M
  have h : ∀ (a : U) (m : (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N₁),
      e (MulOpposite.op a • m) = MulOpposite.op a • e m :=
    fun a m => (LieModuleCat.RightUniversalEnveloping.coefficientULiftEquiv.{u, v, w,
      max u v v' w w' z} R L M).map_smul (MulOpposite.op a) m
  exact TensorProduct.Balanced.congr_mk e (LinearEquiv.refl R T) h (fun _ _ => rfl)
    (show (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj N₁ from ULift.up m)
    (show T from x)

/-- Coefficient down followed by up of the whole balanced output places that output in the
sufficient working universe. -/
def rawCoefficientTrivialTensorOutputLiftEquiv :
    (ModuleCat.BalancedTensor.functor R U
      (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))).obj (envelopingTrivialObject R L) ≃ₗ[R]
      (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
        ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
        (envelopingTrivialObject R L)) :=
  (rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M).trans
    (ULift.moduleEquiv : ULift.{max u v v' w w' z}
      ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
      (envelopingTrivialObject R L)) ≃ₗ[R]
      ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
      (envelopingTrivialObject R L))).symm

@[simp]
theorem rawCoefficientTrivialTensorOutputLiftEquiv_mk_up (m : M) (x : envelopingTrivialObject R L) :
    rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M
      (TensorProduct.Balanced.mk R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          (ULift.up m) x) =
    ULift.up (TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
      ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m x) := by
  exact congrArg ULift.up (rawCoefficientTrivialTensorEquiv_mk_up.{u, v, v', w, w', z} R L M m x)

/-- The canonical raw coefficient H₀/unit isomorphism, including output down to the lower-universe
balanced quotient carrier. -/
def rawCoefficientHomologyZeroTensorIsoAt :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology 0) ≅
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
      (envelopingTrivialObject R L)) :=
  rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0 ≪≫
    nativeCoefficientHomologyZeroTensorIso.{u, v, v', max w w' z} R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) ≪≫
      (rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M).toModuleIso

/-- Canonical H₀ comparison between the exact raw homology and the exact raw balanced quotient, as
an independent-universe linear equivalence. -/
def rawCoefficientHomologyZeroTensorEquivAt : (coefficientComplex R L M).homology 0 ≃ₗ[R]
  ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
  (envelopingTrivialObject R L)) :=
  (coefficientHomologyCarrierLiftEquiv.{u, v, w, max u v v' w w' z} R L M 0).trans
    ((rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).toLinearEquiv.trans
      (ULift.moduleEquiv : ULift.{max u v v' w w' z}
        ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
        (envelopingTrivialObject R L)) ≃ₗ[R]
        ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
        (envelopingTrivialObject R L))))

/-- The empty-exterior class keeps the raw coefficient and scalar unit after both carrier
transports. -/
theorem rawCoefficientHomologyZeroTensorIsoAt_class (m : M) :
    (rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).hom
      (ULift.up ((coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)))) =
      ULift.up (TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          m (ULift.up (1 : R))) := by
  change rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M
    ((nativeCoefficientHomologyZeroTensorIso.{u, v, v', max w w' z} R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).hom
      ((rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0).hom
        (ULift.up ((coefficientComplex R L M).isoHomologyι₀.inv
          ((coefficientComplex R L M).pOpcycles 0
            (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m)))))) = _
  rw [rawCoefficientHomologyTransportAt_zero_class, nativeCoefficientHomologyZeroTensorIso_class,
    rawCoefficientTrivialTensorOutputLiftEquiv_mk_up]

/-- The raw empty-exterior class keeps the raw coefficient and scalar unit after explicit input up
and output down. -/
theorem rawCoefficientHomologyZeroTensorEquivAt_class (m : M) :
    rawCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L M
      ((coefficientComplex R L M).isoHomologyι₀.inv
        ((coefficientComplex R L M).pOpcycles 0
          (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))) =
      TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
          m (ULift.up (1 : R)) := by
  change ((rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).hom
    (ULift.up ((coefficientComplex R L M).isoHomologyι₀.inv
      ((coefficientComplex R L M).pOpcycles 0
        (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))))).down = _
  rw [rawCoefficientHomologyZeroTensorIsoAt_class]

local instance rawCoefficientZeroTensor_additive {A : Type a} [Ring A] [Algebra R A]
    (N : ModuleCat.{b} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, a, b, c} R A N).Additive :=
  ModuleCat.BalancedTensor.additive R A N

/-- Full raw-carrier canonical H₀ agreement with derived zero, including trivial-input down and
raw coefficient-output down. -/
theorem rawCoefficientHomologyIsoTorAt_zero_original [Module.Free R L] :
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M 0).hom ≫
      (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
        ModuleCat.{max u v v' w w' z} R).fromLeftDerivedZero.app
        (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L) ≫
        (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))).toModuleIso.hom ≫
          (rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M).toModuleIso.hom =
      (rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).hom := by
  let q := (rawCoefficientTrivialTensorOutputLiftEquiv.{u, v, v', w, w', z} R L M).toModuleIso.hom
  have h := rawCoefficientHomologyIsoTorAt_zero_canonical.{u, v, v', w, w', z} R L M
  have hOut : (rawCoefficientHomologyZeroTensorIsoAt.{u, v, v', w, w', z} R L M).hom =
      (rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0).hom ≫
        (nativeCoefficientHomologyZeroTensorIso.{u, v, v', max w w' z} R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).hom ≫ q := rfl
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ q) h).trans hOut.symm)

/-- Canonical H₀ agreement on the exact raw input and output carriers, with the derived-zero map
between the explicit transports. -/
theorem rawCoefficientHomologyEquivTorAt_zero_original [Module.Free R L]
    (a : (coefficientComplex R L M).homology 0) :
    rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M
      (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        (((ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R).fromLeftDerivedZero.app
          (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L)).hom
          (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M 0 a))) =
    rawCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L M a := by
  have h := congrArg (fun f => f.hom (ULift.up a))
    (rawCoefficientHomologyIsoTorAt_zero_original.{u, v, v', w, w', z} R L M)
  have hDown := congrArg
    (fun b : ULift.{max u v v' w w' z}
    ((ModuleCat.BalancedTensor.functor R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj
    (envelopingTrivialObject R L)) => b.down) h
  change rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M
      (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L
        (LieModuleCat.RightUniversalEnveloping.representObj R L
        (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M))
        (((ModuleCat.BalancedTensor.functor R U
          (LieModuleCat.RightUniversalEnveloping.representObj R L
          (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) : ModuleCat.{max u v v' w w' z} U ⥤
          ModuleCat.{max u v v' w w' z} R).fromLeftDerivedZero.app
          (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L)).hom
          ((rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M 0).hom (ULift.up a)))) =
    rawCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L M a at hDown
  simpa only [rawCoefficientHomologyEquivTorAt_apply] using hDown

end ChevalleyEilenberg
