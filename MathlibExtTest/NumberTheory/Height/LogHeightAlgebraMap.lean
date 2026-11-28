/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.LogHeightAlgebraMap

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

@[expose] public section

universe u v w

/-- Source-shaped consumer with the original binders. -/
private theorem exactSource {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {ι : Type*} [Finite ι] (x : ι → K) :
    Height.logHeight (fun i => algebraMap K L (x i))
      = (Module.finrank K L : ℝ) * Height.logHeight x :=
  Height.logHeight_algebraMap x

/-- Higher-universe consumer. -/
example {K : Type (u+1)} [Field K] [NumberField K] {L : Type (v+1)} [Field L]
    [NumberField L] [Algebra K L] {ι : Type w} [Finite ι] (x : ι → K) :
    Height.logHeight (fun i => algebraMap K L (x i))
      = (Module.finrank K L : ℝ) * Height.logHeight x :=
  Height.logHeight_algebraMap x

/-- Boundary: for the identity extension the factor is `1`, so the height is
unchanged. -/
example (x : Fin 2 → ℚ) :
    Height.logHeight (fun i => algebraMap ℚ ℚ (x i)) = Height.logHeight x := by
  rw [Height.logHeight_algebraMap]
  simp

/-- Degree-two boundary: over the fourth cyclotomic field, a quadratic
extension, the logarithmic height doubles. -/
example (x : Fin 2 → ℚ) :
    Height.logHeight (fun i => algebraMap ℚ (CyclotomicField 4 ℚ) (x i))
      = 2 * Height.logHeight x := by
  rw [Height.logHeight_algebraMap]
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have hfin : Module.finrank ℚ (CyclotomicField 4 ℚ) = 2 := by
    rw [IsCyclotomicExtension.finrank (CyclotomicField 4 ℚ)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 4))]
    decide
  rw [hfin]
  norm_num
