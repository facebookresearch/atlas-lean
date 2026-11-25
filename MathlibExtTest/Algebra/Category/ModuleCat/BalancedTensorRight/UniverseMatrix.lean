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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.UniverseLongExact
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.NormNum

/-!
# Actual independent-carrier enriched tensor clients

The abstract interface keeps all ring/carrier/lift worlds independent. The
concrete quotient uses a noncommutative integral matrix balancing ring, its
genuine regular right input, and an integral outer action. Values are measured
by the actual balanced multiplication map, not a supplied comparison.
This client is covered by the recorded scoped Native checks. It makes no
nonzero positive-Tor assertion.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct

namespace IndependentCarrierWorlds

universe r s a b z t
variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

/-- An actual Tor output can be constructed without a smaller-source or outer-ring size premise. -/
def actualTorOutput (n : ℕ) (X : ModuleCat.{a} Rᵐᵒᵖ) :
    ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  ModuleCat.BalancedTensorRight.torObjAt.{z, r, s, a, b} R S B n X

/-- The actual original short exact sequence produces the native Gamma-valued window. -/
def actualWindow (n : ℕ) (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ))
    (hQ : Q.ShortExact) : ComposableArrows (ModuleCat.{max r a b z} Sᵐᵒᵖ) 5 :=
  ModuleCat.BalancedTensorRight.torLongSequenceAt.{z, r, s, a, b} R S B n Q hQ

/-- Its exactness uses the actual native horseshoe, with no coefficient-projectivity premise. -/
theorem actualWindow_exact (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (actualWindow.{r, s, a, b, z} R S B n Q hQ).Exact :=
  ModuleCat.BalancedTensorRight.torLongSequenceAt_exact R S B n Q hQ

end IndependentCarrierWorlds

namespace IndependentCarrierMatrixFacade

abbrev R := Matrix (Fin 2) (Fin 2) ℤ

/-- The original integral outer action uses the native opposite-ring morphism. -/
def integerUnop : ℤᵐᵒᵖ →+* ℤ :=
  (RingHom.id ℤ).fromOpposite (fun x y => show Commute x y from mul_comm x y)

local instance coefficientRightInteger : Module ℤᵐᵒᵖ R := Module.compHom R integerUnop
local instance coefficientRightIntegerSMul : SMul ℤᵐᵒᵖ R := coefficientRightInteger.toSMul
local instance coefficientActions :
    @SMulCommClass R ℤᵐᵒᵖ R (inferInstance : Module R R).toSMul
      coefficientRightInteger.toSMul := by
  refine ⟨?_⟩
  intro r s b
  change r * (integerUnop s • b) = integerUnop s • (r * b)
  exact (LinearMap.mulLeft ℤ r).toAddMonoidHom.map_zsmul (integerUnop s) b

abbrev X : ModuleCat.{1} Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ (ULift.{1} Rᵐᵒᵖ)
abbrev original := ModuleCat.BalancedTensorRight.originalTensorObj R ℤ R X
abbrev working := ModuleCat.BalancedTensorRight.tensorObjAt.{2, 0, 0, 1, 0} R ℤ R X

/-- Lower the actual right input through the native opposite linear equivalence. -/
def inputDown : X →ₗ[ℤ] R :=
  (MulOpposite.opLinearEquiv ℤ : R ≃ₗ[ℤ] Rᵐᵒᵖ).symm.toLinearMap.comp
    (ULift.moduleEquiv : ULift.{1} Rᵐᵒᵖ ≃ₗ[ℤ] Rᵐᵒᵖ).toLinearMap

/-- The actual bilinear product descends through the original noncommutative balance. -/
def originalValue : original.carrier →ₗ[ℤ] R :=
  TensorProduct.Balanced.lift
    ((LinearMap.mul ℤ R).comp inputDown)
    (fun r q b => by
      change (q.down.unop * r) * b = q.down.unop * (r * b)
      exact mul_assoc _ _ _)

/-- The original quotient probe retains the ordered matrix product. -/
theorem originalValue_mk (q : X) (b : R) :
    originalValue (ModuleCat.BalancedTensorRight.originalTensorMk R ℤ R X q b) =
      q.down.unop * b := by
  exact TensorProduct.Balanced.lift_mk _ _ q b

/-- The working probe is the actual native carrier comparison followed by that original product. -/
def workingValue : working.carrier →ₗ[ℤ] R :=
  originalValue.comp
    (ModuleCat.BalancedTensorRight.tensorUnliftAt.{2, 0, 0, 1, 0} R ℤ R X).toAddMonoidHom.toIntLinearMap

/-- Down on both actual lifted inputs preserves the same ordered product. -/
theorem workingValue_mk (q : X) (b : R) :
    workingValue (TensorProduct.Balanced.mk ℤ R (ULift.{2} X) (ULift.{2} R)
      (ULift.up q) (ULift.up b)) = q.down.unop * b := by
  change originalValue
    (ModuleCat.BalancedTensorRight.tensorUnliftAt.{2, 0, 0, 1, 0} R ℤ R X
      (TensorProduct.Balanced.mk ℤ R (ULift.{2} X) (ULift.{2} R)
        (ULift.up q) (ULift.up b))) = _
  have h := ModuleCat.BalancedTensorRight.tensorUnliftAt_mk.{2, 0, 0, 1, 0}
    R ℤ R X (ULift.up q) (ULift.up b)
  exact (congrArg originalValue h).trans (originalValue_mk q b)

abbrev e01 : R := fun i j => if i = 0 ∧ j = 1 then 1 else 0
abbrev e10 : R := fun i j => if i = 1 ∧ j = 0 then 1 else 0
abbrev pure01_10 : working :=
  TensorProduct.Balanced.mk ℤ R (ULift.{2} X) (ULift.{2} R)
    (ULift.up (ULift.up (op e01))) (ULift.up e10)

/-- A surviving actual balanced word detects the noncommutative matrix order. -/
theorem ordered_value_one : workingValue pure01_10 0 0 = 1 := by
  rw [workingValue_mk]
  norm_num [e01, e10, Matrix.mul_apply, Matrix.ofNat_apply, Fin.sum_univ_two]

/-- Reversing those same original factors gives a different matrix coordinate. -/
theorem reversed_value_zero :
    workingValue (TensorProduct.Balanced.mk ℤ R (ULift.{2} X) (ULift.{2} R)
      (ULift.up (ULift.up (op e10))) (ULift.up e01)) 0 0 = 0 := by
  rw [workingValue_mk]
  norm_num [e01, e10, Matrix.mul_apply, Matrix.ofNat_apply, Fin.sum_univ_two]

/-- The actual outer right-integer action reaches three on the nonzero original class. -/
theorem outer_value_three : workingValue ((op (3 : ℤ)) • pure01_10) 0 0 = 3 := by
  change workingValue (TensorProduct.Balanced.rightAction ℤ R ℤ
    (ULift.{2} X) (ULift.{2} R) (op 3) pure01_10) 0 0 = 3
  rw [TensorProduct.Balanced.rightAction_mk, workingValue_mk]
  change ((3 : ℤ) • e10) 1 0 = 3
  norm_num [Matrix.smul_apply, e10]

/-- Integer tripling is an actual bimodule coefficient map over the noncommutative ring. -/
def tripleCoefficient : R →ₗ[R] R := (3 : ℕ) • (LinearMap.id : R →ₗ[R] R)

/-- The original integral outer action is retained by this legitimate additive coefficient map. -/
theorem tripleCoefficient_outer (s : ℤᵐᵒᵖ) (r : R) :
    tripleCoefficient (s • r) = s • tripleCoefficient r := by
  change tripleCoefficient (integerUnop s • r) = integerUnop s • tripleCoefficient r
  exact tripleCoefficient.toAddMonoidHom.map_zsmul (integerUnop s) r

/-- The actual facade coefficient transformation reaches3 on the same surviving matrix class. -/
theorem coefficient_value_three :
    workingValue
      (((ModuleCat.BalancedTensorRight.tensorCoefficientTransformationAt.{2, 0, 0, 1, 0}
        R ℤ R R tripleCoefficient tripleCoefficient_outer).app X).hom pure01_10) 0 0 = 3 := by
  rw [ModuleCat.BalancedTensorRight.tensorCoefficientTransformationAt_mk, workingValue_mk]
  norm_num [tripleCoefficient, e01, e10, Matrix.mul_apply, Matrix.ofNat_apply, Fin.sum_univ_two]

/-- The actual noncommutative word survives the facade's computed whole-output height comparison. -/
theorem height_value_one :
    workingValue
      (((ModuleCat.BalancedTensorRight.tensorHeightFacadeIsoAt.{2, 1, 0, 0, 1, 0}
        R ℤ R).hom.app X).hom
        (ULift.up (TensorProduct.Balanced.mk ℤ R (ULift.{1} X) (ULift.{1} R)
          (ULift.up (ULift.up (op e01))) (ULift.up e10)))) 0 0 = 1 := by
  rw [ModuleCat.BalancedTensorRight.tensorHeightFacadeIsoAt_hom_mk, workingValue_mk]
  norm_num [e01, e10, Matrix.mul_apply, Matrix.ofNat_apply, Fin.sum_univ_two]

/-- This real noncommutative input also instantiates native Gamma-derived Tor. -/
def actualTor : ModuleCat.{2} ℤᵐᵒᵖ :=
  ModuleCat.BalancedTensorRight.torObjAt.{2, 0, 0, 1, 0} R ℤ R 1 X

end IndependentCarrierMatrixFacade
