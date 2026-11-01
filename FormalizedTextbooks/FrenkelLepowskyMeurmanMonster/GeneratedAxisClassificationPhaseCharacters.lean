/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaPhase

/-! Two distinct nontrivial binary characters remain independent on a kernel. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- A surjective binary character remains surjective on the kernel of a
second surjective character if the two characters are distinct. -/
theorem generatedAxis_binary_characters_kernel {A : Type*} [Group A]
    (χ ψ : A →* Multiplicative (ZMod 2))
    (hχ : Function.Surjective χ) (hψ : Function.Surjective ψ) (hne : ψ ≠ χ) :
    ∃ a : A, χ a = 1 ∧ ψ a = ofAdd 1 := by
  have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  by_contra! hn
  have hk (a : A) (ha : toAdd (χ a) = 0) : toAdd (ψ a) = 0 := by
    rcases hbit (toAdd (ψ a)) with h | h
    · exact h
    · exact False.elim (hn a (toAdd.injective ha) (toAdd.injective h))
  obtain ⟨u, hu⟩ := hχ (ofAdd 1)
  have hc (a : A) (ha : toAdd (χ a) = 1) : toAdd (χ (a * u)) = 0 := by
    rw [map_mul, hu]
    change toAdd (χ a) + 1 = 0
    rw [ha]
    decide
  rcases hbit (toAdd (ψ u)) with hpu | hpu
  · obtain ⟨a, ha⟩ := hψ (ofAdd 1)
    rcases hbit (toAdd (χ a)) with h | h
    · have hz := hk a h
      rw [ha] at hz
      exact (by decide : (1 : ZMod 2) ≠ 0) hz
    · have hz := hk (a * u) (hc a h)
      rw [map_mul, ha] at hz
      change 1 + toAdd (ψ u) = 0 at hz
      rw [hpu, add_zero] at hz
      exact (by decide : (1 : ZMod 2) ≠ 0) hz
  · apply hne
    ext a
    apply toAdd.injective
    rcases hbit (toAdd (χ a)) with h | h
    · exact (hk a h).trans h.symm
    · have hz := hk (a * u) (hc a h)
      rw [map_mul] at hz
      change toAdd (ψ a) + toAdd (ψ u) = 0 at hz
      rw [hpu] at hz
      have hself : (1 : ZMod 2) + 1 = 0 := by decide
      exact (add_right_cancel (hz.trans hself.symm)).trans h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
