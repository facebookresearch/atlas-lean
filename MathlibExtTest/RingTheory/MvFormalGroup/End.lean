/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.End
public import MathlibExtTest.RingTheory.MvFormalGroup.Basic
public import MathlibExtTest.RingTheory.MvFormalGroup.Hom

import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for endomorphisms of multivariate formal group laws

The semiring structure on `MvFormalGroup.End F` and `MvFormalGroup.linearPartHom`, tested on the
endomorphisms `linEnd A` of the additive formal group law given by square matrices.
-/

@[expose] public section

noncomputable section

namespace MvFormalGroupEndTest

open MvPowerSeries MvFormalGroup MvFormalGroupHomTest MvFormalGroupBasicTest

variable {g : ℕ} {R : Type*} [CommRing R]

/-- The endomorphisms of a commutative formal group law form a semiring. -/
example (F : MvFormalGroup g R) [F.IsComm] : Semiring (End F) := inferInstance

/-- The endomorphism of the additive formal group law given by a square matrix. -/
abbrev linEnd (A : Matrix (Fin g) (Fin g) R) : End (addMv g R) := linHom A

/-- Multiplication in `End` is composition `φ * ψ = φ ∘ ψ`: it multiplies the matrices in this
order. -/
theorem linEnd_mul (A B : Matrix (Fin g) (Fin g) R) : linEnd A * linEnd B = linEnd (A * B) :=
  comp_linHom A B

theorem linEnd_add (A B : Matrix (Fin g) (Fin g) R) : linEnd A + linEnd B = linEnd (A + B) :=
  linHom_add A B

theorem linEnd_one : (1 : End (addMv g R)) = linEnd 1 :=
  id_eq_linHom

/-- In `End (addMv g R)`, the natural number `n` is `n` times the identity matrix. -/
theorem natCast_eq_linEnd (n : ℕ) :
    (n : End (addMv g R)) = linEnd (n : Matrix (Fin g) (Fin g) R) := by
  apply Hom.ext
  funext i
  rw [End.toPowerSeries_natCast, nthSeries_addMv, toPowerSeries_linHom]
  simp [Matrix.natCast_apply, Nat.cast_smul_eq_nsmul]

/-- The semiring operations of `End` match those of matrices on a polynomial expression. -/
example (A B : Matrix (Fin g) (Fin g) R) :
    linEnd A * (linEnd B + 2) = linEnd (A * (B + 2)) := by
  rw [show (2 : End (addMv g R)) = ((2 : ℕ) : End (addMv g R)) by norm_cast,
    natCast_eq_linEnd, linEnd_add, linEnd_mul]
  norm_cast

/-- `linearPartHom` sends `linEnd A` to `A`. -/
theorem linearPartHom_linEnd (A : Matrix (Fin g) (Fin g) R) :
    linearPartHom (addMv g R) (linEnd A) = A :=
  linearPart_linHom A

example (A B : Matrix (Fin g) (Fin g) R) :
    linearPartHom (addMv g R) (linEnd A * linEnd B + 3) = A * B + 3 := by
  rw [map_add, map_mul, map_ofNat, linearPartHom_linEnd, linearPartHom_linEnd]

/-- `End (addMv 2 ℤ)` is not commutative: the order of the factors matters. -/
example : linEnd (R := ℤ) !![1, 1; 0, 1] * linEnd !![1, 0; 1, 1] ≠
    linEnd !![1, 0; 1, 1] * linEnd !![1, 1; 0, 1] := by
  intro hc
  have h := congrArg (linearPartHom (addMv 2 ℤ)) hc
  simp only [map_mul, linearPartHom_linEnd] at h
  have := congrFun (congrFun h 0) 0
  simp at this

end MvFormalGroupEndTest

end
