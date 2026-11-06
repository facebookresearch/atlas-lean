/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite original-source A5 word and matrix encoding checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteCodes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact finite original-source word instructions for the 720 candidate A5 elements. -/
def y322Orthogonal3A5Raw (i : Fin 720) : Y322RawWordInstruction :=
  if i.val = 0 then .one
  else .appendGenerator (y322Orthogonal3A5Parent i).val (y322Orthogonal3A5Generator i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every actual source word reference is strictly earlier; no matrix equality is assumed here.
/-- All literal source A5 candidate word instructions have genuine chronological bounds. -/
theorem y322Orthogonal3A5Raw_allowed (i : Fin 720) : (y322Orthogonal3A5Raw i).Allowed i.val := by
  revert i
  decide +kernel

/-- The exact original-source acyclic A5 candidate word program. -/
def y322Orthogonal3A5Program : Y322WordProgram 720 :=
  y322RawWordProgram y322Orthogonal3A5Raw y322Orthogonal3A5Raw_allowed

/-- Check source labels, actual matrix products, and the exact sorted matrix encoding. -/
def y322Orthogonal3A5CheckAt (index : ℕ) : Prop :=
  if h : index < 720 then
    let i : Fin 720 := ⟨index, h⟩
    (if index = 0 then y322Orthogonal3A5Matrix i = 1 else
      y322Orthogonal3A5Matrix i = y322Orthogonal3A5Matrix (y322Orthogonal3A5Parent i) *
        y322Orthogonal3Reflection (y322Orthogonal3A5Generator i)) ∧
      (y322Orthogonal3A5Generator i).val < 5 ∧
      y322Orthogonal3MatrixCode (y322Orthogonal3A5Matrix i) =
        y322Orthogonal3A5SortedCode (y322Orthogonal3A5SortPosition i)
  else True

/-- Literal source A5 products and their exact integer encodings have decidable finite checks. -/
instance y322Orthogonal3A5CheckAtDecidable (index : ℕ) :
    Decidable (y322Orthogonal3A5CheckAt index) := by
  unfold y322Orthogonal3A5CheckAt
  split
  · infer_instance
  · infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
