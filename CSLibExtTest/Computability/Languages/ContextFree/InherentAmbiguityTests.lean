/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Languages.ContextFree.InherentAmbiguity

/-!
# Client tests for the canonical inherently ambiguous language

Literal words exercise each equality branch, their overlap, and zero exponents.
Letter counts and the order of the blocks independently reject two nonmembers.
-/

namespace Cslib.Language.InherentAmbiguityTests

/-- Zero exponents include the empty word. -/
example : [] ∈ inherentlyAmbiguousLang := ⟨0, 0, 0, Or.inl rfl, rfl⟩

/-- Equal numbers of `0` and `1` suffice when the `2`-count differs. -/
example : [0, 1, 2, 2] ∈ inherentlyAmbiguousLang := ⟨1, 1, 2, Or.inl rfl, rfl⟩

/-- Equal numbers of `1` and `2` suffice when the `0`-count differs. -/
example : [0, 0, 1, 2] ∈ inherentlyAmbiguousLang := ⟨2, 1, 1, Or.inr rfl, rfl⟩

/-- A nonempty word can satisfy both equality branches. -/
example : [0, 1, 2] ∈ inherentlyAmbiguousLang := ⟨1, 1, 1, Or.inl rfl, rfl⟩

/-- Counts `1, 2, 3` satisfy neither equality branch. -/
example : [0, 1, 1, 2, 2, 2] ∉ inherentlyAmbiguousLang := by
  rintro ⟨i, j, k, hijk, hword⟩
  have hi : i = 1 := by
    simpa [List.count_replicate] using (congrArg (List.count (0 : Fin 3)) hword).symm
  have hj : j = 2 := by
    simpa [List.count_replicate] using (congrArg (List.count (1 : Fin 3)) hword).symm
  have hk : k = 3 := by
    simpa [List.count_replicate] using (congrArg (List.count (2 : Fin 3)) hword).symm
  rcases hijk with h | h <;> omega

/-- Equal letter counts do not admit a word whose blocks are out of order. -/
example : [1, 0, 2] ∉ inherentlyAmbiguousLang := by
  rintro ⟨i, j, k, _, hword⟩
  have hi : i = 1 := by
    simpa [List.count_replicate] using (congrArg (List.count (0 : Fin 3)) hword).symm
  have hj : j = 1 := by
    simpa [List.count_replicate] using (congrArg (List.count (1 : Fin 3)) hword).symm
  have hk : k = 1 := by
    simpa [List.count_replicate] using (congrArg (List.count (2 : Fin 3)) hword).symm
  subst i
  subst j
  subst k
  simp at hword

/-- The union characterization is available to an importing client. -/
example : inherentlyAmbiguousLang =
    eqPowLang (0 : Fin 3) 1 * KStar.kstar ({[(2 : Fin 3)]} : Language (Fin 3)) +
      (KStar.kstar ({[(0 : Fin 3)]} : Language (Fin 3)) * eqPowLang (1 : Fin 3) 2) :=
  inherentlyAmbiguousLang_eq

/-- The context-free theorem is available through the same public import. -/
example : inherentlyAmbiguousLang.IsContextFree := inherentlyAmbiguousLang_isContextFree

end Cslib.Language.InherentAmbiguityTests
