/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Elasticity.StressStrain

/-!
# Effective-stress sign conversion

## i. Overview

Terzaghi effective stress at Biot coefficient one with scalar
pore pressure `u` (positive in compression, carried by the
fluid): the compression-positive formula is `σc - u • 1` and
the tension-positive formula is `σt + u • 1`. The
compression/tension conversion of `StressStrain` is negation,
so the two effective-stress formulas convert into each other,
and the physical traction of the effective stress is the
total traction plus `u • v`. The coefficient is the literal
one; the identity itself holds for every coefficient.

## ii. Key results

- `EarthScience.effectiveStressCompressionPositive` and
  `effectiveStressTensionPositive`: the two formulas.
- `EarthScience.effectiveStress_conversion` and
  `effectiveStress_roundTrip`: conversion between them.
- `EarthScience.effectiveStress_traction`: traction form.

## iii. Table of contents

- A. Effective-stress formulas and conversion

## iv. References

- `PhyslibExt.CondensedMatter.Elasticity.StressStrain` for
  the compression-positive conversion and traction maps.
- K. Terzaghi, *Theoretical Soil Mechanics*, Wiley, 1943:
  the effective-stress decomposition.
-/

@[expose] public section

open Matrix
open Elasticity

namespace EarthScience

/-! ## A. Effective-stress formulas and conversion -/

/-- Compression-positive effective stress at Biot coefficient
one: `σc - u • 1`. -/
def effectiveStressCompressionPositive {n : ℕ}
    (σc : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  σc - u • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Tension-positive effective stress at Biot coefficient one:
`σt + u • 1`. -/
def effectiveStressTensionPositive {n : ℕ}
    (σt : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  σt + u • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Converting the compression-positive effective stress gives
the tension-positive effective stress of the converted total
stress. -/
lemma effectiveStress_conversion {n : ℕ}
    (σc : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    compressionPositiveStress
        (effectiveStressCompressionPositive σc u)
      = effectiveStressTensionPositive
          (compressionPositiveStress σc) u := by
  simp only [compressionPositiveStress, effectiveStressCompressionPositive,
    effectiveStressTensionPositive, neg_sub]
  abel

/-- Starting from the tension-positive total stress `σ`, the
compression-positive effective stress is `compressionPositiveStress σ - u • 1`,
and converting it back gives `σ + u • 1`. -/
lemma effectiveStress_roundTrip {n : ℕ}
    (σ : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    compressionPositiveStress
        (effectiveStressCompressionPositive
          (compressionPositiveStress σ) u)
      = effectiveStressTensionPositive σ u := by
  simp only [compressionPositiveStress, effectiveStressCompressionPositive,
    effectiveStressTensionPositive, neg_sub]
  abel

/-- The physical traction of the compression-positive
effective stress equals the tension-positive total traction
plus `u • v`. -/
lemma effectiveStress_traction {n : ℕ}
    (σ : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) (v : Fin n → ℝ) :
    compressionPositiveTraction
        (effectiveStressCompressionPositive
          (compressionPositiveStress σ) u) v
      = traction σ v + u • v := by
  simp only [compressionPositiveTraction, traction,
    effectiveStressCompressionPositive, compressionPositiveStress,
    Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, neg_sub]
  abel

/-- At zero pore pressure both effective stresses reduce to
the total stress in their own convention. -/
lemma effectiveStress_zero_pore_pressure {n : ℕ}
    (σ : Matrix (Fin n) (Fin n) ℝ) :
    effectiveStressCompressionPositive σ 0 = σ
      ∧ effectiveStressTensionPositive σ 0 = σ := by
  simp [effectiveStressCompressionPositive, effectiveStressTensionPositive]

end EarthScience
