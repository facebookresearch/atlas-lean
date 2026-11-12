/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.CircuitComposition

@[expose] public section

/-- Computation: an AND of the two inputs evaluates as expected. -/
example : Circuit.eval (fun i : Fin 2 => i = 0)
    (Circuit.and (Circuit.input 0) (Circuit.input 1)) = false := rfl

/-- Computation: NOT of a constant. -/
example : Circuit.eval (fun _ : Fin 0 => true)
    (Circuit.not (Circuit.const true)) = false := rfl

/-- The depth and size of a one-gate circuit. -/
example : (Circuit.and (Circuit.input (0 : Fin 2))
    (Circuit.const true)).depth = 1 ∧
    (Circuit.and (Circuit.input (0 : Fin 2))
    (Circuit.const true)).size = 1 := ⟨rfl, rfl⟩
