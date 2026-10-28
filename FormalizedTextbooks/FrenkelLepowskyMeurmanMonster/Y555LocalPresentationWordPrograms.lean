/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Acyclic generator-word programs for compressed local presentation certificates.
Every program is evaluated using the actual supplied source generators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationSignedWords

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A word instruction whose references are strictly earlier than its own position. -/
inductive Y322WordInstruction (earlier : ℕ)
  | one
  | generator (v : Fin 8)
  | multiply (left right : Fin earlier)
  | inverse (word : Fin earlier)
  | appendGenerator (word : Fin earlier) (v : Fin 8)

/-- A finite source-generator word program with no cyclic or undefined references. -/
abbrev Y322WordProgram (size : ℕ) := (i : Fin size) → Y322WordInstruction i.val

/-- Reinterpret an earlier instruction index as an index of the whole program. -/
def y322ProgramPrior {size : ℕ} (i : Fin size) (a : Fin i.val) : Fin size :=
  ⟨a.val, a.isLt.trans i.isLt⟩

/-- Evaluate one instruction using the supplied generator values and earlier word values. -/
def y322InstructionValue {G : Type*} [Group G] {earlier : ℕ}
    (generators : Fin 8 → G) (prior : Fin earlier → G) : Y322WordInstruction earlier → G
  | .one => 1
  | .generator v => generators v
  | .multiply a b => prior a * prior b
  | .inverse a => (prior a)⁻¹
  | .appendGenerator a v => prior a * generators v

/-- Exact evaluation of an acyclic word program in a group, without expanding its word trees. -/
noncomputable def y322WordProgramValue {G : Type*} [Group G] {size : ℕ}
    (program : Y322WordProgram size) (generators : Fin 8 → G) : Fin size → G :=
  (measure (fun i : Fin size => i.val)).wf.fix fun i prior =>
    y322InstructionValue generators
      (fun a => prior (y322ProgramPrior i a) a.isLt) (program i)

/-- The actual word value obeys precisely its acyclic instruction. -/
theorem y322WordProgramValue_eq {G : Type*} [Group G] {size : ℕ}
    (program : Y322WordProgram size) (generators : Fin 8 → G) (i : Fin size) :
    y322WordProgramValue program generators i =
      y322InstructionValue generators
        (fun a => y322WordProgramValue program generators (y322ProgramPrior i a)) (program i) := by
  conv_lhs => rw [y322WordProgramValue, WellFounded.fix_eq]
  rfl

/-- Group homomorphisms preserve the exact value of every acyclic source word program. -/
theorem y322WordProgramValue_map {G H : Type*} [Group G] [Group H] {size : ℕ}
    (program : Y322WordProgram size) (generators : Fin 8 → G) (f : G →* H) (i : Fin size) :
    f (y322WordProgramValue program generators i) =
      y322WordProgramValue program (fun v => f (generators v)) i := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    rw [y322WordProgramValue_eq, y322WordProgramValue_eq]
    cases program i with
    | one => exact map_one f
    | generator v => rfl
    | multiply a b =>
      simp only [y322InstructionValue, map_mul,
        ih (y322ProgramPrior i a) a.isLt, ih (y322ProgramPrior i b) b.isLt]
    | inverse a =>
      simp only [y322InstructionValue, map_inv, ih (y322ProgramPrior i a) a.isLt]
    | appendGenerator a v =>
      simp only [y322InstructionValue, map_mul, ih (y322ProgramPrior i a) a.isLt]

/-- Concrete program values in the independently defined source local presentation. -/
noncomputable def y322LocalProgramValue {size : ℕ} (program : Y322WordProgram size) :
    Fin size → Y322Presentation :=
  y322WordProgramValue program (fun v => (PresentedGroup.of v : Y322Presentation))

/-- Every concrete local program value equals its exact earlier-generator instruction. -/
theorem y322LocalProgramValue_eq {size : ℕ} (program : Y322WordProgram size) (i : Fin size) :
    y322LocalProgramValue program i =
      y322InstructionValue (fun v => (PresentedGroup.of v : Y322Presentation))
        (fun a => y322LocalProgramValue program (y322ProgramPrior i a)) (program i) :=
  y322WordProgramValue_eq program (fun v => (PresentedGroup.of v : Y322Presentation)) i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
