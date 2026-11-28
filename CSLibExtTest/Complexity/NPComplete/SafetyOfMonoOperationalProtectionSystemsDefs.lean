/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SafetyOfMonoOperationalProtectionSystemsDefs

namespace MetaMathlibExt.Complexity.NPComplete.SafetyOfMonoOperationalProtectionSystems

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SafetyOfMonoOperationalProtectionSystemsInstance) :
    safetyOfMonoOperationalProtectionSystemsDec (bitEncode i) = true ↔
      WellFormed i ∧ SafetyOfMonoOperationalProtectionSystemsFeasible i := by
  simp [safetyOfMonoOperationalProtectionSystemsDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : safetyOfMonoOperationalProtectionSystemsDec [true] = false := by
  have h : bitDecode (α := SafetyOfMonoOperationalProtectionSystemsInstance) [true] = none := rfl
  simp [safetyOfMonoOperationalProtectionSystemsDec, h]

/-- The single command "if right `1` is in `(X₀, X₀)`, enter right `0` into `(X₀, X₀)`". -/
private abbrev guarded : Command := (1, [(1, 0, 0)], (true, 0, 0, 0))

/-- Two rights, one subject (which is also the only object), the command `guarded`, the leaked
right `0`, and the given initial matrix. -/
private abbrev inst (init : List (ℕ × ℕ × ℕ)) : SafetyOfMonoOperationalProtectionSystemsInstance :=
  (2, 1, 1, init, [guarded], 0)

/-- With right `1` initially in cell `(0, 0)`, the command `guarded` runs at once and enters the
missing right `0`: a leak. -/
example : safetyOfMonoOperationalProtectionSystemsDec (bitEncode (inst [(0, 0, 1)])) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, initialMatrix (inst [(0, 0, 1)]),
    Relation.ReflTransGen.refl, guarded, fun _ => 0, ⟨by simp, by simp, ?_, by simp⟩, rfl, rfl, ?_⟩
  · simp [initialMatrix]
  · simp [initialMatrix]

/-- From the empty matrix, the guard of the only command never holds, so no command ever runs and
right `0` cannot leak. -/
example : safetyOfMonoOperationalProtectionSystemsDec (bitEncode (inst [])) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, P, hreach, c, x, ⟨hc, -, hcond, -⟩, -⟩ := (accepts_encoding _).1 h
  have hempty : ∀ Q, Relation.ReflTransGen (Step (inst [])) (initialMatrix (inst [])) Q →
      Q = ∅ := by
    intro Q hQ
    induction hQ with
    | refl => ext t; simp [initialMatrix]
    | tail _ hstep ih =>
      obtain ⟨c', x', ⟨hc', -, hcond', -⟩, -⟩ := hstep
      simp only [List.mem_singleton] at hc'
      subst hc'
      have := hcond' (1, 0, 0) (by simp)
      simp [ih] at this
  simp only [List.mem_singleton] at hc
  subst hc
  have := hcond (1, 0, 0) (by simp)
  simp [hempty P hreach] at this

/-- A leaked right outside the `2` rights makes the instance malformed. -/
example : safetyOfMonoOperationalProtectionSystemsDec
    (bitEncode ((2, 1, 1, [(0, 0, 1)], [guarded], 2) :
      SafetyOfMonoOperationalProtectionSystemsInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.2.2.2 (by decide)

end MetaMathlibExt.Complexity.NPComplete.SafetyOfMonoOperationalProtectionSystems
