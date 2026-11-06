/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Every exact original-source A5 matrix and encoding check is verified. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Check00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Check01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Check02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Check03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Check04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Check05

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every finite actual-source A5 check block passes its exact kernel certificate. -/
theorem y322Orthogonal3A5CheckBlock (block : Fin 6) (i : Fin 128) :
    y322Orthogonal3A5CheckAt (block.val * 128 + i.val) := by
  fin_cases block
  · exact y322Orthogonal3A5Check00 i
  · exact y322Orthogonal3A5Check01 i
  · exact y322Orthogonal3A5Check02 i
  · exact y322Orthogonal3A5Check03 i
  · exact y322Orthogonal3A5Check04 i
  · exact y322Orthogonal3A5Check05 i

/-- All 720 actual-source A5 candidates have exact generator, matrix, and encoding checks. -/
theorem y322Orthogonal3A5_checked (i : Fin 720) : y322Orthogonal3A5CheckAt i.val := by
  let block : Fin 6 := ⟨i.val / 128, by omega⟩
  let offset : Fin 128 := ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩
  have h := y322Orthogonal3A5CheckBlock block offset
  have he : block.val * 128 + offset.val = i.val := by
    dsimp [block, offset]
    omega
  simpa only [he] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Only literal adjacent integer inequalities are checked, avoiding quadratic pair enumeration.
/-- The literal sorted source matrix codes are strictly increasing. -/
theorem y322Orthogonal3A5SortedCode_mono : StrictMono y322Orthogonal3A5SortedCode := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- The literal inverse position is checked on all 720 source candidates.
/-- The exact sorting position table has its declared left inverse. -/
theorem y322Orthogonal3A5SortPosition_inverse (i : Fin 720) :
    y322Orthogonal3A5InverseSortPosition (y322Orthogonal3A5SortPosition i) = i := by
  revert i
  decide +kernel

/-- The sorted literal encoding distinguishes all 720 actual source image matrices. -/
theorem y322Orthogonal3A5Code_injective : Function.Injective
    (fun i => y322Orthogonal3A5SortedCode (y322Orthogonal3A5SortPosition i)) :=
  y322SortedFiniteCode_injective _ _ _ y322Orthogonal3A5SortedCode_mono
    y322Orthogonal3A5SortPosition_inverse

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
