/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

@[expose] public section

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

-- `exactSource` consumers with the original binders.
example (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n * v.deg :=
  Divisor.degree_single v n

example {D : Divisor K F} :
    D ∈ Divisor.degZero (K := K) (F := F) ↔ Divisor.degree D = 0 :=
  Divisor.mem_degZero

example {D : Divisor K F} :
    D ∈ Divisor.principal (K := K) (F := F) ↔ Divisor.IsPrincipal D :=
  Divisor.mem_principal

example (D : Divisor.degZero (K := K) (F := F)) : Pic0 K F :=
  Pic0.mk D

example : Function.Surjective (Pic0.mk (K := K) (F := F)) :=
  Pic0.mk_surjective

-- Boundary: the zero divisor has degree zero, and a single place of
-- positive degree contributes nontrivially when its degree is nonzero.
example : (0 : Divisor K F) ∈ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero]
  simp

example (v : Place K F) (hv : v.deg ≠ 0) :
    Finsupp.single v 1 ∉ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero, Divisor.degree_single]
  simp [hv]

end AlgebraicCurve
