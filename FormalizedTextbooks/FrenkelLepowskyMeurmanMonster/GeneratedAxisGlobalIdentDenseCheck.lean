/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOctadFastDense

/-! # Splitting dense short transport checks

Dense short lists (tens of thousands of terms) are checked in segments, each in its own kernel
check: `shortCheckF_append` joins segment checks, `octChunkTerms_append` splits packed target
chunk lists along the same segments. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Fast transport checks of segments give the check of the concatenation. -/
theorem shortCheckF_append (d : QMaskP) : ∀ (A C : List (ℕ × ℤ)), shortCheckF d A C = true →
    ∀ (B E : List (ℕ × ℤ)), shortCheckF d B E = true → shortCheckF d (A ++ B) (C ++ E) = true
  | [], [], _, _, _, h => h
  | [], _ :: _, h, _, _, _ => by simp [shortCheckF] at h
  | _ :: _, [], h, _, _, _ => by simp [shortCheckF] at h
  | a :: A, c :: C, h, B, E, hB => by
    simp only [shortCheckF, Bool.and_eq_true] at h
    simp only [List.cons_append, shortCheckF, Bool.and_eq_true]
    exact ⟨h.1, shortCheckF_append d A C h.2 B E hB⟩

/-- The terms of concatenated chunk lists. -/
theorem octChunkTerms_append : ∀ (A B : List (ℕ × ℕ × ℕ)),
    OctadDense.octChunkTerms (A ++ B) = OctadDense.octChunkTerms A ++ OctadDense.octChunkTerms B
  | [], _ => rfl
  | a :: A, B => by
    simp only [List.cons_append, OctadDense.octChunkTerms, octChunkTerms_append A B,
      List.append_assoc]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
