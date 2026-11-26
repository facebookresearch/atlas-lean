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

import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Pi

/-!
# General linear groups over a product of noncommutative semirings

Let `R = M₂(ℕ)`. Its matrix units do not commute. Two explicit block permutation matrices
over `R` also have different products in the two orders. Entrywise coefficient evaluation
identifies the general linear group over `Fin 2 → R` with the product of the two general
linear groups over `R`; the inverse recombines each matrix entry pointwise. Empty coefficient
and matrix indices give the corresponding trivial groups without a nonzero-ring assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix.GeneralLinearGroup

namespace PiSemiringSmoke

private abbrev R := Matrix (Fin 2) (Fin 2) ℕ
private abbrev G := Matrix.GeneralLinearGroup (Fin 2) R

private def matrixUnit (i j : Fin 2) : R :=
  fun p q => if p = i ∧ q = j then 1 else 0

private def flipMatrix : Matrix (Fin 2) (Fin 2) R :=
  fun p q => matrixUnit q p

private def swapMatrix : Matrix (Fin 2) (Fin 2) R :=
  fun p q => if p = q then 0 else 1

private def flip : G where
  val := flipMatrix
  inv := flipMatrix
  val_inv := by decide
  inv_val := by decide

private def swap : G where
  val := swapMatrix
  inv := swapMatrix
  val_inv := by decide
  inv_val := by decide

private theorem flip_swap_ne_swap_flip : flip * swap ≠ swap * flip := by
  decide

private abbrev coefficients : Fin 2 → Type := fun _ => R
private def family : ∀ i : Fin 2, Matrix.GeneralLinearGroup (Fin 2) (coefficients i) :=
  fun i => if i = 0 then flip else swap

private def reversedFamily : ∀ i : Fin 2, Matrix.GeneralLinearGroup (Fin 2) (coefficients i) :=
  fun i => if i = 0 then swap else flip

private def combined : Matrix.GeneralLinearGroup (Fin 2) (Fin 2 → R) :=
  (piSemiringEquiv coefficients (Fin 2)).symm family

private def reversed : Matrix.GeneralLinearGroup (Fin 2) (Fin 2 → R) :=
  (piSemiringEquiv coefficients (Fin 2)).symm reversedFamily

private theorem evaluate_combined (i : Fin 2) :
    piSemiringEquiv coefficients (Fin 2) combined i = family i := by
  exact congrFun ((piSemiringEquiv coefficients (Fin 2)).apply_symm_apply family) i

private theorem evaluate_reversed (i : Fin 2) :
    piSemiringEquiv coefficients (Fin 2) reversed i = reversedFamily i := by
  exact congrFun ((piSemiringEquiv coefficients (Fin 2)).apply_symm_apply reversedFamily) i

private theorem evaluate_product :
    piSemiringEquiv coefficients (Fin 2) (combined * reversed) 0 = flip * swap ∧
      piSemiringEquiv coefficients (Fin 2) (combined * reversed) 1 = swap * flip := by
  constructor
  · calc
      piSemiringEquiv coefficients (Fin 2) (combined * reversed) 0 =
          piSemiringEquiv coefficients (Fin 2) combined 0 *
            piSemiringEquiv coefficients (Fin 2) reversed 0 :=
        congrFun (map_mul (piSemiringEquiv coefficients (Fin 2)) combined reversed) 0
      _ = flip * swap := by
        rw [evaluate_combined, evaluate_reversed]
        rfl
  · calc
      piSemiringEquiv coefficients (Fin 2) (combined * reversed) 1 =
          piSemiringEquiv coefficients (Fin 2) combined 1 *
            piSemiringEquiv coefficients (Fin 2) reversed 1 :=
        congrFun (map_mul (piSemiringEquiv coefficients (Fin 2)) combined reversed) 1
      _ = swap * flip := by
        rw [evaluate_combined, evaluate_reversed]
        rfl

example : matrixUnit 0 1 * matrixUnit 1 0 ≠ matrixUnit 1 0 * matrixUnit 0 1 := by
  decide

example : piSemiringEquiv coefficients (Fin 2) combined 0 = flip ∧
    piSemiringEquiv coefficients (Fin 2) combined 1 = swap := by
  constructor
  · simpa [family] using evaluate_combined 0
  · simpa [family] using evaluate_combined 1

example (i : Fin 2) : mapRingHom (Pi.evalRingHom coefficients i) combined = family i := by
  rw [← piSemiringEquiv_apply coefficients (Fin 2) combined i]
  exact evaluate_combined i

example (i p q : Fin 2) :
    ((combined : Matrix (Fin 2) (Fin 2) (Fin 2 → R)) p q) i =
      if i = 0 then matrixUnit q p else if p = q then 0 else 1 := by
  change ((↑((piSemiringEquiv coefficients (Fin 2)).symm family) :
    Matrix (Fin 2) (Fin 2) (∀ i, coefficients i)) p q) i = _
  rw [coe_piSemiringEquiv_symm_apply coefficients (Fin 2) family p q i]
  by_cases hi : i = 0
  · simp [family, hi, flip, flipMatrix]
  · simp [family, hi, swap, swapMatrix]

example :
    piSemiringEquiv coefficients (Fin 2) (combined * reversed) 0 = flip * swap ∧
      piSemiringEquiv coefficients (Fin 2) (combined * reversed) 1 = swap * flip ∧
      piSemiringEquiv coefficients (Fin 2) (combined * reversed) 0 ≠
        piSemiringEquiv coefficients (Fin 2) (combined * reversed) 1 := by
  refine ⟨evaluate_product.1, evaluate_product.2, ?_⟩
  rw [evaluate_product.1, evaluate_product.2]
  exact flip_swap_ne_swap_flip

private abbrev emptyCoefficients : Fin 0 → Type := fun _ => R
private def emptyFamily : ∀ i : Fin 0,
    Matrix.GeneralLinearGroup (Fin 2) (emptyCoefficients i) := fun i => Fin.elim0 i

example : (piSemiringEquiv emptyCoefficients (Fin 2)).symm emptyFamily =
    (1 : Matrix.GeneralLinearGroup (Fin 2) (∀ i, emptyCoefficients i)) := by
  apply (piSemiringEquiv emptyCoefficients (Fin 2)).injective
  funext i
  exact Fin.elim0 i

example (A : ∀ i : Fin 2, Matrix.GeneralLinearGroup (Fin 0) (coefficients i)) :
    (piSemiringEquiv coefficients (Fin 0)).symm A =
      (1 : Matrix.GeneralLinearGroup (Fin 0) (∀ i, coefficients i)) := by
  apply Units.ext
  funext p
  exact Fin.elim0 p

end PiSemiringSmoke
