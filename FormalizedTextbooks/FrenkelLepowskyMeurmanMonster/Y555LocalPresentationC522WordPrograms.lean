/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Acyclic source-word programs for the C522 terminal certificate, with arbitrary finite arity. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A word instruction whose references are strictly earlier than its own position. -/
inductive Y522WordInstruction (alphabet earlier : ℕ)
  | one
  | generator (v : Fin alphabet)
  | multiply (left right : Fin earlier)
  | inverse (word : Fin earlier)
  | appendGenerator (word : Fin earlier) (v : Fin alphabet)

/-- A finite source-generator word program with no cyclic or undefined references. -/
abbrev Y522WordProgram (alphabet size : ℕ) := (i : Fin size) → Y522WordInstruction alphabet i.val

/-- Reinterpret an earlier instruction index as an index of the whole program. -/
def y522ProgramPrior {size : ℕ} (i : Fin size) (a : Fin i.val) : Fin size :=
  ⟨a.val, a.isLt.trans i.isLt⟩

/-- Evaluate one instruction using the supplied generator values and earlier word values. -/
def y522InstructionValue {G : Type*} [Group G] {alphabet earlier : ℕ}
    (generators : Fin alphabet → G) (prior : Fin earlier → G) :
    Y522WordInstruction alphabet earlier → G
  | .one => 1
  | .generator v => generators v
  | .multiply a b => prior a * prior b
  | .inverse a => (prior a)⁻¹
  | .appendGenerator a v => prior a * generators v

/-- Exact evaluation of an acyclic word program in a group, without expanding its word trees. -/
noncomputable def y522WordProgramValue {G : Type*} [Group G] {alphabet size : ℕ}
    (program : Y522WordProgram alphabet size) (generators : Fin alphabet → G) : Fin size → G :=
  (measure (fun i : Fin size => i.val)).wf.fix fun i prior =>
    y522InstructionValue generators
      (fun a => prior (y522ProgramPrior i a) a.isLt) (program i)

/-- The actual word value obeys precisely its acyclic instruction. -/
theorem y522WordProgramValue_eq {G : Type*} [Group G] {alphabet size : ℕ}
    (program : Y522WordProgram alphabet size) (generators : Fin alphabet → G) (i : Fin size) :
    y522WordProgramValue program generators i =
      y522InstructionValue generators
        (fun a => y522WordProgramValue program generators (y522ProgramPrior i a)) (program i) := by
  conv_lhs => rw [y522WordProgramValue, WellFounded.fix_eq]
  rfl

/-- Group homomorphisms preserve the exact value of every acyclic source word program. -/
theorem y522WordProgramValue_map {G H : Type*} [Group G] [Group H] {alphabet size : ℕ}
    (program : Y522WordProgram alphabet size) (generators : Fin alphabet → G)
    (f : G →* H) (i : Fin size) :
    f (y522WordProgramValue program generators i) =
      y522WordProgramValue program (fun v => f (generators v)) i := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    rw [y522WordProgramValue_eq, y522WordProgramValue_eq]
    cases program i with
    | one => exact map_one f
    | generator v => rfl
    | multiply a b =>
      simp only [y522InstructionValue, map_mul,
        ih (y522ProgramPrior i a) a.isLt, ih (y522ProgramPrior i b) b.isLt]
    | inverse a =>
      simp only [y522InstructionValue, map_inv, ih (y522ProgramPrior i a) a.isLt]
    | appendGenerator a v =>
      simp only [y522InstructionValue, map_mul, ih (y522ProgramPrior i a) a.isLt]

/-- A homomorphism fixing all supplied source generators fixes every actual acyclic word. -/
theorem y522WordProgramValue_fixed {G : Type*} [Group G] {alphabet size : ℕ}
    (program : Y522WordProgram alphabet size) (generators : Fin alphabet → G)
    (f : G →* G) (hg : ∀ v, f (generators v) = generators v) (i : Fin size) :
    f (y522WordProgramValue program generators i) =
      y522WordProgramValue program generators i := by
  rw [y522WordProgramValue_map]
  have he : (fun v => f (generators v)) = generators := funext hg
  rw [he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
