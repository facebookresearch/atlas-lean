/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact word-value preservation under acyclic instruction-table embeddings. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Embed an earlier instruction reference through a strictly increasing word-table embedding. -/
def y322ProgramEmbeddingPrior {size larger : ℕ} (embedding : Fin size → Fin larger)
    (he : StrictMono embedding) (i : Fin size) (a : Fin i.val) : Fin (embedding i).val :=
  ⟨(embedding (y322ProgramPrior i a)).val, he a.isLt⟩

/-- Rename the strictly earlier references of one source instruction through a table embedding. -/
def y322InstructionEmbed {size larger : ℕ} (embedding : Fin size → Fin larger)
    (he : StrictMono embedding) (i : Fin size) :
    Y322WordInstruction i.val → Y322WordInstruction (embedding i).val
  | .one => .one
  | .generator v => .generator v
  | .multiply a b =>
      .multiply (y322ProgramEmbeddingPrior embedding he i a)
        (y322ProgramEmbeddingPrior embedding he i b)
  | .inverse a => .inverse (y322ProgramEmbeddingPrior embedding he i a)
  | .appendGenerator a v => .appendGenerator (y322ProgramEmbeddingPrior embedding he i a) v

/-- Renaming an earlier reference gives exactly the embedding of that earlier instruction. -/
theorem y322ProgramEmbeddingPrior_value {size larger : ℕ} (embedding : Fin size → Fin larger)
    (he : StrictMono embedding) (i : Fin size) (a : Fin i.val) :
    y322ProgramPrior (embedding i) (y322ProgramEmbeddingPrior embedding he i a) =
      embedding (y322ProgramPrior i a) := rfl

/-- A literal instruction embedding preserves every actual source-generator word value. -/
theorem y322WordProgramValue_embedding {G : Type*} [Group G] {size larger : ℕ}
    (program : Y322WordProgram size) (target : Y322WordProgram larger)
    (generators : Fin 8 → G) (embedding : Fin size → Fin larger) (he : StrictMono embedding)
    (h : ∀ i, target (embedding i) = y322InstructionEmbed embedding he i (program i))
    (i : Fin size) :
    y322WordProgramValue target generators (embedding i) =
      y322WordProgramValue program generators i := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    rw [y322WordProgramValue_eq, y322WordProgramValue_eq, h i]
    cases program i with
    | one => rfl
    | generator v => rfl
    | multiply a b =>
      simp only [y322InstructionEmbed, y322InstructionValue, y322ProgramEmbeddingPrior_value,
        ih (y322ProgramPrior i a) a.isLt, ih (y322ProgramPrior i b) b.isLt]
    | inverse a =>
      simp only [y322InstructionEmbed, y322InstructionValue, y322ProgramEmbeddingPrior_value,
        ih (y322ProgramPrior i a) a.isLt]
    | appendGenerator a v =>
      simp only [y322InstructionEmbed, y322InstructionValue, y322ProgramEmbeddingPrior_value,
        ih (y322ProgramPrior i a) a.isLt]

/-- Literal subprogram embeddings preserve word values in the genuine source C322 group. -/
theorem y322LocalProgramValue_embedding {size larger : ℕ}
    (program : Y322WordProgram size) (target : Y322WordProgram larger)
    (embedding : Fin size → Fin larger) (he : StrictMono embedding)
    (h : ∀ i, target (embedding i) = y322InstructionEmbed embedding he i (program i))
    (i : Fin size) :
    y322LocalProgramValue target (embedding i) = y322LocalProgramValue program i :=
  y322WordProgramValue_embedding program target _ embedding he h i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
