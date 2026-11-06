/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit bound checking for finite compressed source-word instruction tables. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A raw source word instruction before its earlier-reference bounds are checked. -/
inductive Y322RawWordInstruction
  | one
  | generator (v : Fin 8)
  | multiply (left right : ℕ)
  | inverse (word : ℕ)
  | appendGenerator (word : ℕ) (v : Fin 8)
  deriving DecidableEq

/-- Every raw reference must be strictly earlier than its own instruction. -/
def Y322RawWordInstruction.Allowed (earlier : ℕ) : Y322RawWordInstruction → Prop
  | .one => True
  | .generator _ => True
  | .multiply a b => a < earlier ∧ b < earlier
  | .inverse a => a < earlier
  | .appendGenerator a _ => a < earlier

/-- Checking a raw instruction's earlier-reference bounds is decidable. -/
instance y322RawInstructionAllowedDecidable (earlier : ℕ) (raw : Y322RawWordInstruction) :
    Decidable (raw.Allowed earlier) := by
  cases raw <;> unfold Y322RawWordInstruction.Allowed <;> infer_instance

/-- A checked raw instruction becomes an exact acyclic source-word instruction. -/
def y322RawInstructionDecode (earlier : ℕ) (raw : Y322RawWordInstruction)
    (h : raw.Allowed earlier) : Y322WordInstruction earlier :=
  match raw with
  | .one => .one
  | .generator v => .generator v
  | .multiply a b => .multiply ⟨a, h.1⟩ ⟨b, h.2⟩
  | .inverse a => .inverse ⟨a, h⟩
  | .appendGenerator a v => .appendGenerator ⟨a, h⟩ v

/-- Recover exactly the raw instruction of a checked acyclic source instruction. -/
def y322InstructionRaw {earlier : ℕ} : Y322WordInstruction earlier → Y322RawWordInstruction
  | .one => .one
  | .generator v => .generator v
  | .multiply a b => .multiply a.val b.val
  | .inverse a => .inverse a.val
  | .appendGenerator a v => .appendGenerator a.val v

/-- Bound checking preserves every literal raw instruction and reference exactly. -/
theorem y322RawInstructionDecode_raw (earlier : ℕ) (raw : Y322RawWordInstruction)
    (h : raw.Allowed earlier) :
    y322InstructionRaw (y322RawInstructionDecode earlier raw h) = raw := by
  cases raw <;> rfl

/-- A fully bound-checked raw word table gives an actual acyclic word program. -/
def y322RawWordProgram {size : ℕ} (raw : Fin size → Y322RawWordInstruction)
    (h : ∀ i, (raw i).Allowed i.val) : Y322WordProgram size :=
  fun i => y322RawInstructionDecode i.val (raw i) (h i)

/-- Every instruction of the checked raw table retains precisely its original literal data. -/
theorem y322RawWordProgram_raw {size : ℕ} (raw : Fin size → Y322RawWordInstruction)
    (h : ∀ i, (raw i).Allowed i.val) (i : Fin size) :
    y322InstructionRaw (y322RawWordProgram raw h i) = raw i :=
  y322RawInstructionDecode_raw i.val (raw i) (h i)

/-- Decode a natural-number record of a source instruction with a fixed reference radix. -/
def y322PackedWordInstruction (radix packed : ℕ) : Y322RawWordInstruction :=
  let payload := packed / 5
  match packed % 5 with
  | 0 => .one
  | 1 => .generator ⟨payload % 8, Nat.mod_lt _ (by decide)⟩
  | 2 => .multiply (payload % radix) (payload / radix)
  | 3 => .inverse payload
  | _ => .appendGenerator (payload % radix) ⟨(payload / radix) % 8, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
