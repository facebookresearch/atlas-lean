/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal embedding of normalized ancestor instructions into the actual chronological program. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7HNodeBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordProgramEmbeddings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawInstructionEquality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact source-instruction comparison under the literal chronological ancestor embedding. -/
def y322E7HNodeEmbeddingInputAt (index : ℕ) : Prop :=
  if h : index < 4413 then
    y322TransportProgram (y322E7HNodeEmbedding ⟨index, h⟩) =
      y322InstructionEmbed y322E7HNodeEmbedding y322E7HNodeEmbedding_strictMono ⟨index, h⟩
        (y322E7HNodeProgram ⟨index, h⟩)
  else True

/-- Literal equality of the embedded acyclic instructions is decidable. -/
instance y322E7HNodeEmbeddingInputAtDecidable (index : ℕ) :
    Decidable (y322E7HNodeEmbeddingInputAt index) := by
  unfold y322E7HNodeEmbeddingInputAt
  split <;> infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Every instruction and its actual target reference are compared literally in the kernel.
/-- Each ancestor instruction is the precise corresponding chronological source instruction. -/
theorem y322E7HNodeEmbeddingInputBlock (block : Fin 5) (i : Fin 1024) :
    y322E7HNodeEmbeddingInputAt (block.val * 1024 + i.val) := by
  fin_cases block <;> revert i <;> decide +kernel

/-- Literal target instructions agree with the acyclic embedded ancestor instructions. -/
theorem y322E7HNodeEmbeddingInput (i : Fin 4413) :
    y322TransportProgram (y322E7HNodeEmbedding i) =
      y322InstructionEmbed y322E7HNodeEmbedding y322E7HNodeEmbedding_strictMono i
        (y322E7HNodeProgram i) := by
  let block : Fin 5 := ⟨i.val / 1024, by omega⟩
  let offset : Fin 1024 := ⟨i.val % 1024, Nat.mod_lt _ (by decide)⟩
  have h := y322E7HNodeEmbeddingInputBlock block offset
  have he : block.val * 1024 + offset.val = i.val := by
    dsimp [block, offset]
    omega
  rw [he] at h
  simpa only [y322E7HNodeEmbeddingInputAt, dite_eq_left i.isLt] using h

/-- Actual local word values agree in the ancestor program and the chronological source program. -/
theorem y322E7HNodeTransport_value (i : Fin 4413) :
    y322LocalProgramValue y322TransportProgram (y322E7HNodeEmbedding i) =
      y322LocalProgramValue y322E7HNodeProgram i :=
  y322LocalProgramValue_embedding _ _ _ y322E7HNodeEmbedding_strictMono
    y322E7HNodeEmbeddingInput i

/-- The final normalized ancestor is exactly chronological transporter H38539. -/
theorem y322E7HNodeEmbedding_last : y322E7HNodeEmbedding 4412 = 38539 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
