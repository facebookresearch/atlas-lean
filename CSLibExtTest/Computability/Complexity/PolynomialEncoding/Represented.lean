/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.CodecMachine
import CSLibExt.Computability.Complexity.PolynomialEncoding.RowDedup
import CSLibExt.Computability.Complexity.PolynomialEncoding.Tuples

open Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.PolynomialEncoding.Comprehension
open MetaMathlibExt.BitstringEncoding

-- Bounded enumeration includes shorter tuples and allows the same choice in both positions.
example : tuples [false, true] 2 =
    [[], [false], [false, false], [false, true], [true], [true, false], [true, true]] := by
  decide

-- The outer frame is complete in both cases. A truncated inner frame invalidates its whole list.
example : CodecMachine.nat.list.list.valid (delimit (delimit [])) = true ∧
    CodecMachine.nat.list.list.valid (delimit (delimit [] ++ [true])) = false := by
  decide

-- The polynomial-time row operation retains the last occurrence of each payload.
example : ∃ run, MetaMathlibExt.ComplexityTheory.IsPolyTime run ∧
    run (frames id [[true], [false], [true]]) = frames id [[false], [true]] := by
  obtain ⟨run, hpoly, hrows⟩ := Represented.dedup (rows := id) Function.injective_id
    (Represented.input (frames (α := List Bool) id))
  exact ⟨run, hpoly, hrows [[true], [false], [true]]⟩
