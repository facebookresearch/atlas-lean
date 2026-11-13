/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.Hadamard
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-- Boundary check: the weight of the codeword of `(1, 0)` over
`Fin 2 → ZMod 2` is `2 ^ (2 - 1) = 2`. -/
example : (Finset.univ.filter
      (fun r => dot (![1, 0] : Fin 2 → ZMod 2) r = 1)).card = 2 ^ (2 - 1) :=
  hadWeight (![1, 0] : Fin 2 → ZMod 2) (by decide)
