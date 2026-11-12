/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionHardnessCore

/-! # Proof and execution consumers of the padding component -/

open MetaMathlibExt.Complexity.NPComplete.Partition
open MetaMathlibExt.TM2Program Cslib.Complexity.Karp
open MetaMathlibExt.BitstringEncoding Turing

example (as : List ℕ) (t : ℕ) :
    ∃ v S, RunLe HardnessCore.prog (20 * ((encodeSS as t).length + 1) ^ 2)
      ⟨some .target, false, Function.update (fun _ => []) .X (encodeSS as t)⟩
      ⟨some .done, v, S⟩ ∧ S .O = bitEncode (fromSubsetSum as t) :=
  HardnessCore.run as t

private def execute : Nat → TM2.Cfg HardnessCore.Γ HardnessCore.Lab Bool →
    Option (List Bool)
  | 0, _ => none
  | n + 1, c =>
    if c.l = some .done then some (c.stk .O)
    else (TM2.step HardnessCore.prog c).bind (execute n)

example : execute 100 ⟨some .target, false,
    Function.update (fun _ => []) .X (encodeSS [] 0)⟩ =
    some (bitEncode ([0, 0] : List ℕ)) := by decide

example : execute 100 ⟨some .target, false,
    Function.update (fun _ => []) .X (encodeSS [] 1)⟩ =
    some (bitEncode ([0, 2] : List ℕ)) := by decide

example : execute 200 ⟨some .target, false,
    Function.update (fun _ => []) .X (encodeSS [0, 2, 2] 2)⟩ =
    some (bitEncode ([4, 4, 0, 2, 2] : List ℕ)) := by decide

example : execute 200 ⟨some .target, false,
    Function.update (fun _ => []) .X (encodeSS [1, 2] 4)⟩ =
    some (bitEncode ([3, 8, 1, 2] : List ℕ)) := by decide
