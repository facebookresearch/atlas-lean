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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RightTensor
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.BarComparison
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientHomologyZero
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Induction
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ZeroClass

/-!
# Right-coefficient homology and the trivial-module tensor

For a right enveloping module, quotienting by the Lie-action relations identifies degree-zero
coefficient homology with its balanced tensor against the trivial enveloping module. The
quotient class of m maps to `m ⊗ 1`; the inverse multiplies the scalar coordinate by the
coinvariant class.

For a free underlying Lie module, the degree-zero homology-to-Tor comparison agrees with this
tensor identification.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] HomologicalComplex.homologyFunctor coefficientComplex

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

variable (N : ModuleCat.{w} (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ)

local notation "M" => rightCoefficients R L N
local notation "Q" => M ⧸ ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆

/-- Right Lie-generator action values lie in the coefficient action-relation submodule. -/
theorem rightCoefficient_generator_mem_relations (x : L) (m : N) :
    op (UniversalEnvelopingAlgebra.ι R x) • m ∈ ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule) := by
  have h : ⁅x, (show M from m)⁆ ∈ ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule) := by
    rw [coefficientActionRelations_eq_range]
    exact ⟨x ⊗ₜ[R] (show M from m), by
      simp only [LieModuleHom.coe_toLinearMap, LieModule.toModuleHom_apply]⟩
  simpa only [rightCoefficients_lie, neg_neg] using
    ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).neg_mem h

/-- Every right enveloping algebra action is its augmentation modulo the Lie action relations, by
scalar/generator/product/sum induction. -/
theorem rightCoefficient_action_sub_augmentation_mem (u : U) (m : N) :
    op u • m - UniversalEnvelopingAlgebra.augmentation R L u • m ∈
      ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule) := by
  have h : ∀ m : N, op u • m - UniversalEnvelopingAlgebra.augmentation R L u • m ∈
    ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule) := by
    induction u using UniversalEnvelopingAlgebra.induction R L with
    | algebraMap r =>
        intro m
        rw [(UniversalEnvelopingAlgebra.augmentation R L).commutes]
        change op (algebraMap R U r) • m - r • m ∈ ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule)
        rw [← rightCoefficients_smul R L N r m, sub_self]
        exact ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).zero_mem
    | ι x =>
        intro m
        rw [UniversalEnvelopingAlgebra.augmentation_ι, zero_smul, sub_zero]
        exact rightCoefficient_generator_mem_relations R L N x m
    | mul u v hu hv =>
        intro m
        have h := ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).add_mem (hv (op u • m))
          (((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).smul_mem
            (UniversalEnvelopingAlgebra.augmentation R L v) (hu m))
        have hEq : op (u * v) • m - UniversalEnvelopingAlgebra.augmentation R L (u * v) • m =
            (op v • (op u • m) - UniversalEnvelopingAlgebra.augmentation R L v • (op u • m)) +
              UniversalEnvelopingAlgebra.augmentation R L v •
                (op u • m - UniversalEnvelopingAlgebra.augmentation R L u • m) := by
          rw [MulOpposite.op_mul, mul_smul, map_mul, smul_sub,
            ← mul_smul, mul_comm (UniversalEnvelopingAlgebra.augmentation R L u)
              (UniversalEnvelopingAlgebra.augmentation R L v)]
          simp only [smul_sub, mul_smul]
          abel
        exact hEq ▸ h
    | add u v hu hv =>
        intro m
        rw [MulOpposite.op_add, add_smul, map_add, add_smul, add_sub_add_comm]
        exact ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).add_mem (hu m) (hv m)
  exact h m

/-- The right action on a coinvariant class is scalar multiplication by the enveloping algebra
augmentation. -/
theorem rightCoefficient_quotient_action (u : U) (m : N) :
    ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ (op u • m) =
      UniversalEnvelopingAlgebra.augmentation R L u •
      ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m := by
  apply sub_eq_zero.mp
  rw [← map_smul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule)).2
    (rightCoefficient_action_sub_augmentation_mem R L N u m)

/-- The scalar coordinate of the trivial enveloping algebra module. -/
def envelopingTrivialScalarCoordinates :
  ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) ≃ₗ[R] R :=
  (envelopingTrivialGroundEquiv R L).trans
    (ULift.moduleEquiv : ULift.{max u v} R ≃ₗ[R] R)

@[simp]
theorem envelopingTrivialScalarCoordinates_apply
  (a : ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :
    envelopingTrivialScalarCoordinates R L a = a.down := rfl

/-- The coefficient/coinvariant pairing for the trivial-module tensor. -/
def rightCoinvariantsPairing : N →ₗ[R]
  ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) →ₗ[R] Q where
  toFun m := (envelopingTrivialScalarCoordinates R L).toLinearMap.smulRight
    (((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m)
  map_add' m n := by
    ext a
    simp only [LinearMap.smulRight_apply, map_add, smul_add, LinearMap.add_apply]
  map_smul' r m := by
    ext a
    change a.down • ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ (r • m) = r •
      (a.down • ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m)
    rw [map_smul, smul_comm]

@[simp]
theorem rightCoinvariantsPairing_apply (m : N)
  (a : ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :
    rightCoinvariantsPairing R L N m a = a.down • ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ
      m := rfl

/-- The pairing respects the enveloping algebra balancing relation. -/
theorem rightCoinvariantsPairing_balanced (u : U) (m : N)
  (a : ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :
    rightCoinvariantsPairing R L N (op u • m) a = rightCoinvariantsPairing R L N m (u • a) := by
  rw [rightCoinvariantsPairing_apply, rightCoinvariantsPairing_apply,
    rightCoefficient_quotient_action]
  change a.down •
    (UniversalEnvelopingAlgebra.augmentation R L u •
    ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m) =
    (UniversalEnvelopingAlgebra.augmentation R L u * a.down) •
      ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m
  rw [← mul_smul, mul_comm]

/-- The balanced tensor map to the coefficient coinvariants. -/
def rightTensorToCoinvariants : (TensorProduct.Balanced R U N
    ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) →ₗ[R] Q :=
  TensorProduct.Balanced.lift (rightCoinvariantsPairing R L N)
    (rightCoinvariantsPairing_balanced R L N)

theorem rightTensorToCoinvariants_mk (m : N)
  (a : ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :
    rightTensorToCoinvariants R L N
      (TensorProduct.Balanced.mk R U N
      ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m a) =
      a.down • ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m := rfl

/-- Insert the scalar unit in the trivial enveloping algebra coefficient. -/
def rightTensorInsertUnit : N →ₗ[R] (TensorProduct.Balanced R U N
    ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :=
  (TensorProduct.Balanced.mk R U N
    ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))).flip (ULift.up (1 : R))

@[simp]
theorem rightTensorInsertUnit_apply (m : N) :
    rightTensorInsertUnit R L N m =
      TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m (ULift.up (1 : R)) := rfl

private theorem rightTensorInsertUnit_generator (x : L) (m : N) :
    rightTensorInsertUnit R L N (op (UniversalEnvelopingAlgebra.ι R x) • m) = 0 := by
  let T := (ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)
  let one : T := ULift.up (1 : R)
  have hBalance := TensorProduct.Balanced.balance R U N T
    (UniversalEnvelopingAlgebra.ι R x) m one
  have hZero : UniversalEnvelopingAlgebra.ι R x • one = (0 : T) := by
    apply ULift.ext
    change UniversalEnvelopingAlgebra.augmentation R L (UniversalEnvelopingAlgebra.ι R x) * 1 = 0
    rw [UniversalEnvelopingAlgebra.augmentation_ι, zero_mul]
  exact (rightTensorInsertUnit_apply R L N _).trans
    (hBalance.trans ((congrArg (TensorProduct.Balanced.mk R U N T m) hZero).trans
      (TensorProduct.Balanced.mk R U N T m).map_zero))

/-- The unit insertion annihilates the Lie action relations. -/
theorem rightTensorInsertUnit_relations : ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule) ≤
  LinearMap.ker (rightTensorInsertUnit R L N) := by
  rw [coefficientActionRelations_eq_range]
  rintro z ⟨t, rfl⟩
  change rightTensorInsertUnit R L N ((LieModule.toModuleHom R L M).toLinearMap t) = 0
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht', add_zero]
  | tmul x m =>
      simp only [LieModuleHom.coe_toLinearMap, LieModule.toModuleHom_apply,
        rightCoefficients_lie, map_neg, rightTensorInsertUnit_generator, neg_zero]

/-- The unit insertion descends to the coinvariant quotient. -/
def rightCoinvariantsToTensor : Q →ₗ[R] (TensorProduct.Balanced R U N
    ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :=
  ((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).liftQ (rightTensorInsertUnit R L N)
    (rightTensorInsertUnit_relations R L N)

theorem rightCoinvariantsToTensor_mk (m : N) :
    rightCoinvariantsToTensor R L N (((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m) =
      TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m (ULift.up (1 : R)) := rfl

theorem rightTensorToCoinvariants_comp_inverse :
    (rightTensorToCoinvariants R L N).comp (rightCoinvariantsToTensor R L N) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ m =>
      exact (congrArg (rightTensorToCoinvariants R L N)
        (rightCoinvariantsToTensor_mk R L N m)).trans
          ((rightTensorToCoinvariants_mk R L N m (ULift.up 1)).trans
            (one_smul R (((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m)))

theorem rightCoinvariantsToTensor_comp_inverse :
    (rightCoinvariantsToTensor R L N).comp (rightTensorToCoinvariants R L N) = LinearMap.id := by
  apply TensorProduct.Balanced.hom_ext
  intro m a
  let T := (ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)
  let one : T := ULift.up (1 : R)
  let F := rightCoinvariantsToTensor R L N
  let H := TensorProduct.Balanced.mk R U N T m
  let scalar : R := a.down
  have hScalar : scalar • one = a := by
    apply (envelopingTrivialScalarCoordinates R L).injective
    rw [map_smul, envelopingTrivialScalarCoordinates_apply,
      envelopingTrivialScalarCoordinates_apply]
    exact mul_one scalar
  have hClass := rightTensorToCoinvariants_mk R L N m a
  have hUnit := rightCoinvariantsToTensor_mk R L N m
  exact (congrArg F hClass).trans
    ((F.map_smul scalar _).trans ((congrArg (fun y => scalar • y) hUnit).trans
      ((H.map_smul scalar one).symm.trans (congrArg H hScalar))))

/-- Coinvariant/tensor coordinates with the computed inverse. -/
def rightTensorCoinvariantsEquiv : (TensorProduct.Balanced R U N
    ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) ≃ₗ[R] Q :=
  LinearEquiv.ofLinearMap (rightTensorToCoinvariants R L N) (rightCoinvariantsToTensor R L N)
    (rightTensorToCoinvariants_comp_inverse R L N) (rightCoinvariantsToTensor_comp_inverse R L N)

theorem rightTensorCoinvariantsEquiv_symm_mk (m : N) :
    (rightTensorCoinvariantsEquiv R L N).symm (((⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆).toSubmodule).mkQ m) =
      TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m (ULift.up (1 : R)) := rfl

/-- The coefficient H₀ comparison followed by the coinvariant/unit-tensor coordinates. No freeness
is required for this H₀ result. -/
def rightCoefficientHomologyZeroTensorIso :
    (rightEnvelopingCoefficientComplex R L N).homology 0 ≅ ModuleCat.of R (TensorProduct.Balanced R U N
    ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :=
  ((coefficientHomologyZeroLinearEquiv R L M).trans
    (rightTensorCoinvariantsEquiv R L N).symm).toModuleIso

/-- The canonical empty exterior word maps to its unit tensor class. -/
theorem rightCoefficientHomologyZeroTensorIso_class (m : N) :
    (rightCoefficientHomologyZeroTensorIso R L N).hom
      ((rightEnvelopingCoefficientComplex R L N).isoHomologyι₀.inv
        ((rightEnvelopingCoefficientComplex R L N).pOpcycles 0
          (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] (show M from m)))) =
      TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m (ULift.up (1 : R)) := by
  change (rightTensorCoinvariantsEquiv R L N).symm
    (coefficientHomologyZeroLinearEquiv R L M
      ((rightEnvelopingCoefficientComplex R L N).isoHomologyι₀.inv
        ((rightEnvelopingCoefficientComplex R L N).pOpcycles 0
          (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] (show M from m))))) = _
  exact (congrArg (rightTensorCoinvariantsEquiv R L N).symm
    (coefficientHomologyZeroLinearEquiv_class R L M m)).trans
      (rightTensorCoinvariantsEquiv_symm_mk R L N m)

section DerivedZero

variable [Module.Free R L]

local instance rightHomologyZero_tensor_additive :
    (ModuleCat.BalancedTensor.functor R U N :
      ModuleCat.{max u v} U ⥤ ModuleCat.{max u v w} R).Additive :=
  ModuleCat.BalancedTensor.additive R U N

/-- The derived augmentation comparison takes the empty-word class to the balanced unit tensor. -/
theorem rightCoefficientDerivedZero_unit_class (m : N) :
    ((ModuleCat.BalancedTensor.functor R U N).fromLeftDerivedZero.app
      (envelopingTrivialObject R L)).hom
      ((rightCoefficientHomologyIsoTor R L N 0).hom
        ((rightEnvelopingCoefficientComplex R L N).isoHomologyι₀.inv
          ((rightEnvelopingCoefficientComplex R L N).pOpcycles 0
            (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] (show M from m))))) =
      TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m (ULift.up (1 : R)) := by
  let K := rightEnvelopingCoefficientComplex R L N
  let J := rightTensorEnvelopingComplex R L N
  let e := rightTensorCoefficientIso R L N
  let P := envelopingProjectiveResolution R L
  let F : ModuleCat.{max u v} U ⥤ ModuleCat.{max u v w} R :=
    ModuleCat.BalancedTensor.functor R U N
  let cK : K.X 0 ⟶ K.homology 0 := K.pOpcycles 0 ≫ K.isoHomologyι₀.inv
  have h : cK ≫ (rightCoefficientHomologyIsoTor R L N 0).hom ≫
      F.fromLeftDerivedZero.app (envelopingTrivialObject R L) =
        e.inv.f 0 ≫ F.map (P.π.f 0) := by
    exact ProjectiveResolution.zeroClass_fromLeftDerivedZero_of_iso P F K e.symm
  let z : K.X 0 := exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] (show M from m)
  have hval := congrArg (fun f : K.X 0 ⟶ F.obj (envelopingTrivialObject R L) => f.hom z) h
  let X := (envelopingComplex R L).X 0
  let Y := envelopingTrivialObject R L
  letI : Module R X := Module.compHom X (algebraMap R U)
  letI : Module R Y := Module.compHom Y (algebraMap R U)
  let aug : X ⟶ Y := P.π.f 0
  let p : X := exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] (1 : regularCoefficients R L)
  let unit : Y := ULift.up (1 : R)
  have hAug : aug.hom p = unit := by
    change envelopingAugmentationComponent R L p = unit
    exact (envelopingAugmentationComponent_apply R L p).trans
      (congrArg ULift.up
        ((congrArg (UniversalEnvelopingAlgebra.augmentation R L)
          (envelopingZeroEquiv_tmul R L (exteriorPower.ιMulti R 0 Fin.elim0) 1)).trans
            (by rw [exteriorPower.zeroEquiv_ιMulti, one_smul, map_one])))
  have hTensor := ModuleCat.BalancedTensor.map_mk R U N aug m p
  have hUnit : (F.map aug).hom (TensorProduct.Balanced.mk R U N X m p) =
      TensorProduct.Balanced.mk R U N Y m unit :=
    hTensor.trans (congrArg (TensorProduct.Balanced.mk R U N Y m) hAug)
  have hInverse := rightTensorCoordinates_symm_tmul R L N 0
    m (exteriorPower.ιMulti R 0 Fin.elim0)
  have hInput : (e.inv.f 0).hom z = TensorProduct.Balanced.mk R U N X m p := hInverse
  have hOutput := (congrArg (F.map aug).hom hInput).trans hUnit
  exact hval.trans hOutput

/-- The Tor computation agrees with the canonical H₀ coinvariant map, through the derived
augmentation map. -/
theorem rightCoefficientHomologyIsoTor_zero_canonical :
    (rightCoefficientHomologyIsoTor R L N 0).hom ≫
      (ModuleCat.BalancedTensor.functor R U N).fromLeftDerivedZero.app
        (envelopingTrivialObject R L) =
      (rightCoefficientHomologyZeroTensorIso R L N).hom := by
  apply ModuleCat.hom_ext
  ext a
  obtain ⟨m, hm⟩ := LieSubmodule.Quotient.surjective_mk'
    ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆
      (coefficientHomologyZeroLinearEquiv R L M a)
  have ha : a = (rightEnvelopingCoefficientComplex R L N).isoHomologyι₀.inv
      ((rightEnvelopingCoefficientComplex R L N).pOpcycles 0
        (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] m)) := by
    apply (coefficientHomologyZeroLinearEquiv R L M).injective
    rw [coefficientHomologyZeroLinearEquiv_class]
    exact hm.symm
  let left := ((rightCoefficientHomologyIsoTor R L N 0).hom ≫
    (ModuleCat.BalancedTensor.functor R U N).fromLeftDerivedZero.app
      (envelopingTrivialObject R L)).hom
  let right := (rightCoefficientHomologyZeroTensorIso R L N).hom.hom
  exact (congrArg left ha).trans
    ((rightCoefficientDerivedZero_unit_class R L N m).trans
      ((rightCoefficientHomologyZeroTensorIso_class R L N m).symm.trans
        (congrArg right ha.symm)))

/-- The derived-zero map is an isomorphism at this trivial enveloping algebra module, from the two
H₀ coordinates. -/
instance rightEnvelopingTorZero_isIso :
    IsIso ((ModuleCat.BalancedTensor.functor R U N).fromLeftDerivedZero.app
      (envelopingTrivialObject R L)) := by
  let e := rightCoefficientHomologyIsoTor R L N 0
  let d := rightCoefficientHomologyZeroTensorIso R L N
  let h : rightEnvelopingTor R L N 0 ⟶
      ModuleCat.of R (TensorProduct.Balanced R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :=
    e.inv ≫ d.hom
  have hMap : (ModuleCat.BalancedTensor.functor R U N).fromLeftDerivedZero.app
      (envelopingTrivialObject R L) = h := by
    apply (cancel_epi e.hom).1
    exact (rightCoefficientHomologyIsoTor_zero_canonical R L N).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ d.hom) e.hom_inv_id).trans (Category.id_comp _))).symm
  haveI : IsIso h := by
    exact (inferInstance : IsIso (e.symm ≪≫ d).hom)
  exact hMap.symm ▸ (inferInstance : IsIso h)

/-- The canonical degree-zero Tor/tensor isomorphism at the trivial enveloping algebra module. Its
forward map is the derived augmentation map. -/
def rightEnvelopingTorZeroIso : rightEnvelopingTor R L N 0 ≅ ModuleCat.of R (TensorProduct.Balanced R U N
    ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))) :=
  (rightCoefficientHomologyIsoTor R L N 0).symm ≪≫ rightCoefficientHomologyZeroTensorIso R L N

/-- The constructed degree-zero coordinates have exactly the canonical derived-augmentation map as
their forward map. -/
theorem rightEnvelopingTorZeroIso_hom :
    (rightEnvelopingTorZeroIso R L N).hom =
      (ModuleCat.BalancedTensor.functor R U N).fromLeftDerivedZero.app
        (envelopingTrivialObject R L) := by
  let e := rightCoefficientHomologyIsoTor R L N 0
  let d := rightCoefficientHomologyZeroTensorIso R L N
  apply (cancel_epi e.hom).1
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ d.hom) e.hom_inv_id).trans (Category.id_comp _))).trans
      (rightCoefficientHomologyIsoTor_zero_canonical R L N).symm

end DerivedZero

end ChevalleyEilenberg
