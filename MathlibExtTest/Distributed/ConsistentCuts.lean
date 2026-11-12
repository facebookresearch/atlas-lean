/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.ConsistentCuts
public import Mathlib.Order.Fin.Basic

@[expose] public section

/-- Boundary check: on the chain `Fin 3`, the principal cut of
`1` contains `0` and `1` but not `2`. -/
example : (0 : Fin 3) ∈ Set.Iic (1 : Fin 3) ∧
    (1 : Fin 3) ∈ Set.Iic (1 : Fin 3) ∧
    (2 : Fin 3) ∉ Set.Iic (1 : Fin 3) := by decide
