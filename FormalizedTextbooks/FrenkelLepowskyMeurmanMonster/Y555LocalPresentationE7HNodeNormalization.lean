/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact normalization of the actual acyclic E7 transporter ancestor word program. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7HNodeBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordProgramCertificates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The canonical positive source word selected by an ancestor's checked normalization. -/
def y322E7HNodeWord (i : Fin 4413) : List (Fin 8) :=
  y322E7HNormOutput (y322E7HNodeNormalization i)

/-- Exact literal input matching for an actual ancestor instruction, with padding separated. -/
def y322E7HNodeNormalizationInputAt (index : ℕ) : Prop :=
  if h : index < 4413 then
    y322InstructionPositiveWord
      (fun a => y322E7HNodeWord (y322ProgramPrior ⟨index, h⟩ a))
      (y322E7HNodeProgram ⟨index, h⟩) =
        y322E7HNormInput (y322E7HNodeNormalization ⟨index, h⟩)
  else True

/-- Literal input matching for each finite ancestor normalization is decidable. -/
instance y322E7HNodeNormalizationInputAtDecidable (index : ℕ) :
    Decidable (y322E7HNodeNormalizationInputAt index) := by
  unfold y322E7HNodeNormalizationInputAt
  split <;> infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel compares every actual instruction's positive word with its literal move input.
/-- All finite normalization inputs match their exact earlier-source-word instructions. -/
theorem y322E7HNodeNormalizationInputBlock (block : Fin 5) (i : Fin 1024) :
    y322E7HNodeNormalizationInputAt (block.val * 1024 + i.val) := by
  fin_cases block <;> revert i <;> decide +kernel

/-- Each actual ancestor's input is precisely its checked earlier-word instruction. -/
theorem y322E7HNodeNormalizationInput (i : Fin 4413) :
    y322InstructionPositiveWord (fun a => y322E7HNodeWord (y322ProgramPrior i a))
      (y322E7HNodeProgram i) = y322E7HNormInput (y322E7HNodeNormalization i) := by
  let block : Fin 5 := ⟨i.val / 1024, by omega⟩
  let offset : Fin 1024 := ⟨i.val % 1024, Nat.mod_lt _ (by decide)⟩
  have h := y322E7HNodeNormalizationInputBlock block offset
  have he : block.val * 1024 + offset.val = i.val := by
    dsimp [block, offset]
    omega
  rw [he] at h
  simpa only [y322E7HNodeNormalizationInputAt, dite_eq_left i.isLt] using h

/-- Every actual ancestor word equals its canonical source word in the original C322 group. -/
theorem y322E7HNodeProgram_value (i : Fin 4413) :
    y322LocalProgramValue y322E7HNodeProgram i = y322PositiveWord (y322E7HNodeWord i) := by
  apply y322WordProgramValue_of_coxeter_certificates
    y322E7HNodeProgram y322E7HNodeWord
    (fun i => y322E7HNormMoves (y322E7HNodeNormalization i))
  intro i
  rw [y322E7HNodeNormalizationInput]
  exact y322E7HNormReplay (y322E7HNodeNormalization i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
