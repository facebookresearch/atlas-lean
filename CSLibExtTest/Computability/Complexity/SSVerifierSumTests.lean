/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.SSVerifierSum

open Cslib.Complexity.Karp Cslib.Complexity.SSVerifierSum
open Cslib.Complexity.SatVerifier MetaMathlibExt.TM2Program Turing

-- Empty input reaches the zero halt after exactly three steps.
example : Run SSVerify.prog 3
    ⟨some .next, false, SSVerify.st [] [] [] [] []⟩
    ⟨some .yes, Flag.tag false, SSVerify.st [] [] [] [] []⟩ := by
  rfl

-- Two equal item occurrences are both selected, not deduplicated.
example : ∃ v w, RunLe SSVerify.prog 273
    ⟨some .next, false, SSVerify.st
      (([2, 2].flatMap fun a => MetaMathlibExt.BitstringEncoding.delimit
        (Computability.encodeNat a)).map .bit)
      [Sym.bit true, Sym.bit true] [] [] []⟩
    ⟨some .no, v, SSVerify.st [] w [] []
      [Sym.bit true, Sym.bit false, Sym.bit false]⟩ := by
  exact sum_component_run [2, 2] [true, true] false

-- Missing witness bits are false; an oversized all-true mask is allowed.
example : SSVerify.pick [2, 7] [true] = [2] := by decide
example : SSVerify.pick [0, 0, 3] (List.replicate 5 true) = [0, 0, 3] :=
  pick_all _ _ (by decide)

-- Canonical zero has no payload bits, unlike a malformed false payload.
example : Computability.encodeNat (SSVerify.pick [0, 0] [true, true]).sum =
    [] := by decide
example : Computability.decodeNat [false] = 2 := by decide
example : Computability.decodeNat [true, false] = 5 := by decide
