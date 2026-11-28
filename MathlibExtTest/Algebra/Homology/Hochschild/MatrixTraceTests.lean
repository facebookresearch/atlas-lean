/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Algebra.Homology.Hochschild.Matrix.Trace
import MathlibExt.Algebra.Homology.Hochschild.Matrix.BlockTrace
import MathlibExt.LinearAlgebra.Matrix.ZeroExtension.Trace
import Mathlib.Tactic

/-!
# Closed matrix cycles and the signed coefficient boundary

Scalar matrix units detect the order of the generalized trace. Matrix-valued
coefficients detect the right-minus-left degree-one boundary in a noncommutative
algebra. The corner section uses an index carrier above the scalar-ring universe.
-/

noncomputable section
open CategoryTheory
open scoped TensorProduct BigOperators
namespace MatrixTraceTests
open ModuleCat.Algebra.Hochschild.Matrix

private abbrev I2 := Fin 2
private abbrev I3 := Fin 3
private abbrev A := Matrix I2 I2 ℤ
private abbrev unit2 (i j : I2) : A := Matrix.single i j 1
private abbrev unit3 (i j : I3) : Matrix I3 I3 ℤ := Matrix.single i j 1
private abbrev loopTail : Fin 2 → Matrix I3 I3 ℤ := ![unit3 1 2, unit3 2 0]
private abbrev reversedTail : Fin 2 → Matrix I3 I3 ℤ := ![unit3 2 0, unit3 1 2]

private theorem const_fin_one {B : Type*} (x : B) :
    (fun _ : Fin 1 => x) = ![x] := by
  funext i
  fin_cases i
  rfl

example :
    matrixTensorEquiv ℤ I2 (Matrix.single 0 1 (3 : ℤ) ⊗ₜ[ℤ] (2 : ℤ)) 0 1 = 6 := by
  rw [matrixTensorEquiv_tmul]
  rfl

example :
    generalizedTrace ℤ I3 2 (unit3 0 1 ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ loopTail) =
      (1 : ℤ) ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (fun _ : Fin 2 => (1 : ℤ)) := by
  have h := generalizedTrace_scaled ℤ I3 2 (unit3 0 1) loopTail
    (1 : ℤ) (fun _ : Fin 2 => (1 : ℤ))
  simpa [unit3, loopTail, Matrix.map, Matrix.of, Matrix.single, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, List.ofFn_succ, Matrix.single_apply, smul_eq_mul] using h

example :
    generalizedTrace ℤ I3 2 (unit3 0 1 ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ reversedTail) = 0 := by
  have h := generalizedTrace_scaled ℤ I3 2 (unit3 0 1) reversedTail
    (1 : ℤ) (fun _ : Fin 2 => (1 : ℤ))
  simpa [unit3, reversedTail, Matrix.map, Matrix.of, Matrix.single, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, List.ofFn_succ, Matrix.single_apply, smul_eq_mul] using h

private abbrev outerCoefficient : Matrix I2 I2 A := Matrix.single 0 1 (unit2 0 1)
private abbrev outerAlgebra : Matrix I2 I2 A := Matrix.single 1 0 (unit2 1 0)

private theorem matchedTrace :
    generalizedTrace ℤ I2 1
        (outerCoefficient ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ ![outerAlgebra]) =
      unit2 0 1 ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ ![unit2 1 0] := by
  have h := generalizedTrace_scaled ℤ I2 1 (Matrix.single 0 1 (1 : ℤ))
    ![Matrix.single 1 0 (1 : ℤ)] (unit2 0 1) ![unit2 1 0]
  simpa [outerCoefficient, outerAlgebra, Matrix.map, Matrix.of, Matrix.single,
    const_fin_one, Matrix.trace, Matrix.mul_apply,
    Matrix.single_apply, Fin.sum_univ_succ, List.ofFn_succ] using h

example :
    generalizedTrace ℤ I2 1
        (outerCoefficient ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ ![outerAlgebra]) =
      unit2 0 1 ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ ![unit2 1 0] := matchedTrace

example :
    generalizedTrace ℤ I2 1
      (Matrix.single 0 1 (2 : ℤ) ⊗ₜ[ℤ]
        PiTensorProduct.tprod ℤ ![Matrix.single 0 1 (3 : ℤ)]) = 0 := by
  have h := generalizedTrace_scaled ℤ I2 1 (Matrix.single 0 1 (1 : ℤ))
    ![Matrix.single 0 1 (1 : ℤ)] (2 : ℤ) ![(3 : ℤ)]
  simpa [Matrix.map, Matrix.of, Matrix.single, const_fin_one, Matrix.trace, Matrix.mul_apply,
    Matrix.single_apply, Fin.sum_univ_succ, List.ofFn_succ] using h

private def zeroCoordinate :
    A ⊗[ℤ] TensorPower ℤ 0 A →ₗ[ℤ] A :=
  (TensorProduct.rid ℤ A).toLinearMap.comp
    (TensorProduct.map LinearMap.id (TensorPower.zeroEquiv ℤ A).toLinearMap)

-- Pin the regular coefficient actions before opening the matrix-actor scope.
local instance : Module A A := Semiring.toModule
local instance : Module Aᵐᵒᵖ A := Semiring.toOppositeModule
local instance : SMulCommClass A Aᵐᵒᵖ A :=
  Semigroup.opposite_smulCommClass' (α := A)
open scoped ModuleCat.Algebra.Hochschild.Matrix.Coefficients

-- Use the actual coefficient modules of the public matrix trace interface.
local instance : Module (Matrix I2 I2 A) (Matrix I2 I2 A) :=
  Coefficients.leftModule A A I2
local instance : Module (Matrix I2 I2 A)ᵐᵒᵖ (Matrix I2 I2 A) :=
  Coefficients.rightModule A A I2
local instance : SMulCommClass (Matrix I2 I2 A) (Matrix I2 I2 A)ᵐᵒᵖ (Matrix I2 I2 A) :=
  Coefficients.commute A A I2

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

example :
    zeroCoordinate (generalizedTrace ℤ I2 0
      ((ModuleCat.Algebra.Hochschild.boundary ℤ (Matrix I2 I2 A)
        (Matrix I2 I2 A) 0).hom
          (outerCoefficient ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ ![outerAlgebra]))) =
      unit2 0 0 - unit2 1 1 := by
  have h := LinearMap.congr_fun (trace_boundary_comm ℤ A A I2 0)
    (outerCoefficient ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ ![outerAlgebra])
  change zeroCoordinate (_) = _
  rw [h, matchedTrace, ModuleCat.Algebra.Hochschild.boundary_one_tprod]
  simp [zeroCoordinate, LinearMap.comp_apply, TensorProduct.map_tmul,
    TensorPower.zeroEquiv, PiTensorProduct.isEmptyEquiv_apply_tprod,
    unit2, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ,
    smul_eq_mul]

example :
    (cornerChainMap ℤ A A (ULift.{1} I2) (ULift.up 0)) ≫
      traceChainMap ℤ A A (ULift.{1} I2) =
        𝟙 (ModuleCat.Algebra.Hochschild.chainComplex ℤ A (ULift.{1} A)) :=
  cornerChainMap_comp_trace ℤ A A (ULift.{1} I2) (ULift.up 0)

example :
    generalizedTrace ℤ I2 2
      (Matrix.singleLinearMap ℤ 0 0 (4 : ℤ) ⊗ₜ[ℤ]
        PiTensorProduct.tprod ℤ
          (fun j : Fin 2 => Matrix.singleLinearMap ℤ 0 0 (![(5 : ℤ), 6] j))) =
      (4 : ℤ) ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ ![(5 : ℤ), 6] :=
  generalizedTrace_corner_tprod ℤ I2 0 2 4 ![(5 : ℤ), 6]

example :
    (generalizedTrace ℤ (Fin 0) 2 :
      Matrix (Fin 0) (Fin 0) ℤ ⊗[ℤ] TensorPower ℤ 2 (Matrix (Fin 0) (Fin 0) ℤ)
        →ₗ[ℤ] ℤ ⊗[ℤ] TensorPower ℤ 2 ℤ) = 0 :=
  generalizedTrace_of_isEmpty ℤ (Fin 0) 2

example :
    generalizedTrace ℤ (PUnit ⊕ I2) 1
      ((Matrix.fromBlocks (0 : Matrix PUnit PUnit ℤ) 0 0
          (Matrix.single 0 1 (2 : ℤ))) ⊗ₜ[ℤ]
        PiTensorProduct.tprod ℤ ![Matrix.fromBlocks
          (0 : Matrix PUnit PUnit ℤ) 0 0 (Matrix.single 1 0 (3 : ℤ))]) =
      (2 : ℤ) ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ ![(3 : ℤ)] := by
  have hb := generalizedTrace_fromBlocks ℤ I2 1
    (Matrix.single 0 1 (2 : ℤ))
    (fun _ : Fin 1 => Matrix.single 1 0 (3 : ℤ))
  have h := generalizedTrace_scaled ℤ I2 1 (Matrix.single 0 1 (1 : ℤ))
    (fun _ : Fin 1 => Matrix.single 1 0 (1 : ℤ)) (2 : ℤ) (fun _ : Fin 1 => (3 : ℤ))
  have ht :
      generalizedTrace ℤ I2 1
        (Matrix.single 0 1 (2 : ℤ) ⊗ₜ[ℤ]
          PiTensorProduct.tprod ℤ (fun _ : Fin 1 => Matrix.single 1 0 (3 : ℤ))) =
        (2 : ℤ) ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (fun _ : Fin 1 => (3 : ℤ)) := by
    simpa [Matrix.map, Matrix.of, Matrix.single, Matrix.trace, Matrix.mul_apply,
      Matrix.single_apply, Fin.sum_univ_succ, List.ofFn_succ] using h
  simpa only [const_fin_one] using hb.trans ht


example : Matrix.trace (Matrix.zeroExtend (show 1 ≤ 3 by decide)
    (Matrix.single 0 0 (7 : ℤ) : Matrix (Fin 1) (Fin 1) ℤ)) = 7 := by
  rw [Matrix.zeroExtend_trace]
  simp [Matrix.trace, Matrix.single_apply]

example : Matrix.trace (Matrix.zeroExtend (show 0 ≤ 2 by decide)
    (0 : Matrix (Fin 0) (Fin 0) ℤ)) = 0 := by
  rw [Matrix.zeroExtend_trace]
  simp

end MatrixTraceTests
