/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact rational certificate for the published Golay sign reflection of ξ. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiData
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
/-- The actual source Golay codeword labelled 0x400. -/
def co1ReflectionCode : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients 1024), ⟨_, rfl⟩⟩

/-- Its diagonal signs as rational entries. -/
def co1ReflectionScalarQ (i : Fin 24) : ℚ :=
  if (0x11111e : ℕ).testBit i.val then -1 else 1

/-- The rational sign matrix used for the fixed source reflection certificate. -/
def co1ReflectionMatrixQ : Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.diagonal co1ReflectionScalarQ

set_option maxHeartbeats 4000000 in
-- Kernel reduction checks the fixed encoder across all physical coordinates.
/-- The source label is checked against all 24 physical bits of the published encoder. -/
theorem co1ReflectionCode_bits : ∀ i : Fin 24,
    co1ReflectionCode.val i = if (0x11111e : ℕ).testBit i.val then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Exact rational matrix multiplication is reduced by the kernel.
/-- Kernel-checked reflection of the fixed rational ξ matrix. -/
theorem co1Reflection_xi_certificate :
    co1ReflectionMatrixQ * co1XiMatrixQ * co1ReflectionMatrixQ =
      co1XiMatrixQ * co1XiMatrixQ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
