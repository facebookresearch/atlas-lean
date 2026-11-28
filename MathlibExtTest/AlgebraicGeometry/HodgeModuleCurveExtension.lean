/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension

@[expose] public section

/-!
# Tests for the formal curve model of a unipotent variation

With trivial monodromy the truncated logarithm vanishes, so the residue
matrix is zero and the formal connection is ordinary Laurent differentiation.
The Deligne lattice lies in the minimal module, which is stable under the
connection.
-/

noncomputable section

open MathlibExt.Geometry.RationalHodgeStructures MathlibExt.Geometry.LimitingHodgeStructures
open MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension

namespace MathlibExtTest.AlgebraicGeometry.HodgeModuleCurveExtension

variable {V : ModuleCat.{0} ℚ} (C : RationalComplexification V) {r : ℕ}
  (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) {w : ℤ}
  (H : PolarizedPeriodVariation C e w) (b : ℕ)

/-- Trivial monodromy has zero truncated logarithm. -/
theorem truncatedComplexLog_eq_zero (hT : H.complexDeck.toLinearMap = 1) :
    truncatedComplexLog C e H b = 0 := by
  unfold truncatedComplexLog
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  split_ifs with hi
  · rfl
  · rw [hT, sub_self, zero_pow hi, smul_zero]

example (hT : H.complexDeck.toLinearMap = 1) : residueMatrix C e H b = 0 := by
  ext i j
  simp [residueMatrix, truncatedComplexLog_eq_zero C e H b hT]

/-- With trivial monodromy the connection is Laurent differentiation. -/
example (hT : H.complexDeck.toLinearMap = 1) (v : Fin r → LocalMeromorphicSeries) (i : Fin r) :
    formalConnection C e H b v i = LaurentSeries.derivative ℂ (v i) := by
  have h0 : residueMatrix C e H b = 0 := by
    ext i j
    simp [residueMatrix, truncatedComplexLog_eq_zero C e H b hT]
  simp [formalConnection, h0]

example : deligneLattice r ≤ minimalModule C e H b := lattice_le_minimal C e H b

example (v : Fin r → LocalMeromorphicSeries) (hv : v ∈ minimalModule C e H b) :
    formalConnection C e H b v ∈ minimalModule C e H b :=
  connection_mem_minimal C e H b hv

/-- Specialization of the Deligne lattice is the constant coefficient. -/
example (v : (deligneLattice r).restrictScalars ℂ) :
    specialization C e v = constantCoefficient C e v.1 :=
  rfl

end MathlibExtTest.AlgebraicGeometry.HodgeModuleCurveExtension
