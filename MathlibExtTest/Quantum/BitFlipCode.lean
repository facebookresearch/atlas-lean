/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.BitFlipCode

@[expose] public section

open MathlibExt.Quantum.BitFlipCode

/-- The codewords are the labels `000` and `111`. -/
example : (encodeQ 0).val = 0 ∧ (encodeQ 1).val = 7 := by decide

/-- Flipping bit `2` of `111` gives `011`. -/
example : (flipAt 2 (encodeQ 1)).val = 3 := by decide

/-- A flip in the middle bit of `111` is corrected to `111`. -/
example : recoverBasis (flipAt 1 (encodeQ 1)) = encodeQ 1 :=
  recover_flip_encode 1 1

/-- Two flips are not corrected: `000` with bits `0` and `1` flipped decodes to `111`. -/
example : recoverBasis (flipAt 0 (flipAt 1 (encodeQ 0))) = encodeQ 1 := by decide

end
