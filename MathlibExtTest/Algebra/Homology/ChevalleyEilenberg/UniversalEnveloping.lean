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

import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Actual enveloping CE differential with noncommuting integer matrix coefficients

The native universal property evaluates U(M₂(Z)) in M₂(Z). On u=iota(E12)
and x=E21 the actual coefficient-first first differential evaluates to E11,
with positive sign. Reversing the product yields E22, and negating it yields
-E11. These witnesses use neither PBW nor an assumed enveloping embedding.
-/

noncomputable section

open CategoryTheory ChevalleyEilenberg
open scoped TensorProduct Matrix

namespace ChevalleyEilenberg.EnvelopingTests

private abbrev L := Matrix (Fin 2) (Fin 2) ℤ

local instance : LieRing L := LieRing.ofAssociativeRing

private abbrev U := UniversalEnvelopingAlgebra ℤ L

private def e12 : L := !![0, 1; 0, 0]
private def e21 : L := !![0, 0; 1, 0]

/-- This is the native representation, not a supplied injectivity or PBW witness. -/
private def evaluate : U →ₐ[ℤ] L :=
  UniversalEnvelopingAlgebra.lift ℤ (LieHom.id : L →ₗ⁅ℤ⁆ L)

private theorem evaluate_ι (x : L) :
    evaluate (UniversalEnvelopingAlgebra.ι ℤ x) = x :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℤ (LieHom.id : L →ₗ⁅ℤ⁆ L) x

private def actualBoundary : (envelopingComplex ℤ L).X 0 :=
  ((envelopingComplex ℤ L).d 1 0).hom
    (exteriorPower.ιMulti ℤ 1 (fun _ => e21) ⊗ₜ[ℤ]
      (UniversalEnvelopingAlgebra.ι ℤ e12 : regularCoefficients ℤ L))

private theorem actualBoundary_evaluated :
    evaluate (envelopingZeroEquiv ℤ L actualBoundary) = e12 * e21 := by
  rw [actualBoundary, envelopingComplex_d_one, envelopingZeroEquiv_tmul,
    exteriorPower.zeroEquiv_ιMulti]
  change evaluate ((1 : ℤ) •
    (UniversalEnvelopingAlgebra.ι ℤ e12 * UniversalEnvelopingAlgebra.ι ℤ e21 : U)) = e12 * e21
  rw [one_smul, map_mul, evaluate_ι, evaluate_ι]

/-- Positive right multiplication has coordinate (0,0)=1. -/
private theorem actualBoundary_right_order_coordinate :
    evaluate (envelopingZeroEquiv ℤ L actualBoundary) 0 0 = 1 := by
  rw [actualBoundary_evaluated]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, e12, e21]

/-- The other diagonal coordinate is zero, distinguishing the reversed product. -/
private theorem actualBoundary_other_diagonal_coordinate :
    evaluate (envelopingZeroEquiv ℤ L actualBoundary) 1 1 = 0 := by
  rw [actualBoundary_evaluated]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, e12, e21]

private theorem reversed_product_coordinate : (e21 * e12) 0 0 = 0 := by
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, e12, e21]

/-- The genuine differential output differs from reversed multiplication. -/
private theorem actualBoundary_not_reversed :
    evaluate (envelopingZeroEquiv ℤ L actualBoundary) ≠ e21 * e12 := by
  intro h
  have hc := congrArg (fun a : L => a 0 0) h
  rw [actualBoundary_right_order_coordinate, reversed_product_coordinate] at hc
  exact Int.one_ne_zero hc

/-- The same nonzero coordinate detects a wrong global sign. -/
private theorem actualBoundary_positive_sign :
    evaluate (envelopingZeroEquiv ℤ L actualBoundary) ≠ -(e12 * e21) := by
  intro h
  have hc := congrArg (fun a : L => a 0 0) h
  rw [actualBoundary_right_order_coordinate] at hc
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, e12, e21] at hc

private theorem actualBoundary_nonzero : actualBoundary ≠ 0 := by
  intro h
  have hc := congrArg (fun p : (envelopingComplex ℤ L).X 0 =>
    evaluate (envelopingZeroEquiv ℤ L p) 0 0) h
  rw [actualBoundary_right_order_coordinate, map_zero, map_zero] at hc
  exact Int.one_ne_zero hc

/-- Projectivity is earned for the native matrix CE terms; no resolution exactness is input. -/
private theorem actual_terms_projective (n : ℕ) :
    CategoryTheory.Projective ((envelopingComplex ℤ L).X n) := by
  infer_instance

end ChevalleyEilenberg.EnvelopingTests
