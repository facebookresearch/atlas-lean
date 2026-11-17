/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.OverwriteSampleRegister

@[expose] public section

open Cslib.Semantics.Peripheral.OverwriteSampleRegister

namespace CSLibExtTest.Foundations.Semantics.Peripheral.OverwriteSampleRegister

/-- Reading the empty register once returns `none` and stays empty. -/
example (r : Option (ℕ × ℕ)) (s : Slot ℕ) :
    (registerLTS ℕ).MTr none [.read r] s ↔ r = none ∧ s = none :=
  registerLTS_mtr_read_empty_iff r s

end CSLibExtTest.Foundations.Semantics.Peripheral.OverwriteSampleRegister
