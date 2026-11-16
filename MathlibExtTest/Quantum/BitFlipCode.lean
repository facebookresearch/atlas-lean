/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.BitFlipCode

@[expose] public section

/-- A flip in the middle bit of `111` is corrected to `111`. -/
example : recoverBasis (flipAt 1 (encodeQ 1)) = encodeQ 1 :=
  recover_flip_encode 1 1

end
