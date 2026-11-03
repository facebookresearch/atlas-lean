/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionDouble
public import MathlibExt.Computability.BinaryNatEncoding

/-! # Streaming doubling: executable and machine-proof consumers -/

open MetaMathlibExt.Complexity.NPComplete.Partition
open MetaMathlibExt.BitstringEncoding Computability

example : DoubleStream.transform .start [] = [] := rfl
example : DoubleStream.transform .start [false] = [false] := rfl
example : DoubleStream.transform .start [true] = [true, false, true] := rfl

example : DoubleStream.transform .start (bitEncode ([0, 1, 1, 7] : List ℕ)) =
    bitEncode ([0, 2, 2, 14] : List ℕ) := by decide

example : DoubleStream.transform .start (bitEncode ([1024, 1024] : List ℕ)) =
    bitEncode ([2048, 2048] : List ℕ) := by decide

example : MetaMathlibExt.ComplexityTheory.IsPolyTime
    (DoubleStream.transform .start) := DoubleStream.isPolyTime_transform

example (x : List Bool) :
    ∃ v S', MetaMathlibExt.TM2Program.RunLe DoubleStream.prog
      (4 * x.length + 2)
      ⟨some (.scan .start), false, Function.update (fun _ => []) .X x⟩
      ⟨some .done, v, S'⟩ ∧ S' .O = DoubleStream.transform .start x :=
  DoubleStream.run x
