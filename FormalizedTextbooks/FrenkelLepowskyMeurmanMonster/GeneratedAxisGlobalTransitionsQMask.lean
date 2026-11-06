/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! Positive genuine extraspecial lifts of finite binary coordinate masks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- This is an element of the original Q extension, with its original positive central phase. -/
def generatedAxisGlobalQMask (m : ℕ) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (n := 24) m), 1⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
