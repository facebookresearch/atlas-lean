/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Bitwise

/-! Closed balanced data trees avoid substituting an address throughout a
large finite table. Every leaf remains an ordinary natural-number literal. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A balanced binary carrier for exact packed finite arithmetic data. -/
inductive GeneratedAxisGlobalMaskTree where
  /-- An exact packed natural-number payload. -/
  | leaf : ℕ → GeneratedAxisGlobalMaskTree
  /-- Two exact child tables. -/
  | node : GeneratedAxisGlobalMaskTree → GeneratedAxisGlobalMaskTree →
      GeneratedAxisGlobalMaskTree

/-- Select a leaf using the high address bits in an explicitly supplied tree depth. -/
def generatedAxisGlobalMaskTreeValue : GeneratedAxisGlobalMaskTree → ℕ → ℕ → ℕ
  | .leaf v, _, _ => v
  | .node l r, d, b =>
      if b.testBit (d - 1) then generatedAxisGlobalMaskTreeValue r (d - 1) b
      else generatedAxisGlobalMaskTreeValue l (d - 1) b

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
