/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Combinatorics.BinaryChvatalSankoff

/-! # Tests for the binary Chvátal–Sankoff constant -/

namespace CSLibExtTest.Combinatorics.BinaryChvatalSankoff

open MathlibExt.Combinatorics.BinaryChvatalSankoffWanted

-- All four ordered pairs in the length-one sample space.
example : lcsLength (n := 1) (fun _ => false) (fun _ => false) = 1 := by decide +kernel
example : lcsLength (n := 1) (fun _ => true) (fun _ => true) = 1 := by decide +kernel
example : lcsLength (n := 1) (fun _ => false) (fun _ => true) = 0 := by decide +kernel
example : lcsLength (n := 1) (fun _ => true) (fun _ => false) = 0 := by decide +kernel

-- Normalization is defined at zero, but the positive bound is for the limit.
example : normalizedExpectedLCS 0 = 0 := by simp [normalizedExpectedLCS]

example : 0 < binaryChvatalSankoffConstant :=
  chvatalSankoffStrictPositive_wanted

end CSLibExtTest.Combinatorics.BinaryChvatalSankoff
