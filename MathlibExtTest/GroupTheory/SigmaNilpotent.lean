/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SigmaNilpotent
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.SetTheory.Cardinal.Finite

open MathlibExt.GroupTheory.KourovkaNotebookShared

-- The trivial group admits the empty direct product for any family of blocks.
example {I : Type} (σ : I → Set ℕ) : IsSigmaNilpotent σ PUnit.{1} := by
  exact ⟨0, Fin.elim0, fun k ↦ k.elim0, Subsingleton.elim _ _, fun k ↦ k.elim0⟩

-- A group of σ-primary order is σ-nilpotent, with the whole group as its only factor.
private theorem isSigmaNilpotent_of_isSigmaPrimary {I : Type} {σ : I → Set ℕ} {G : Type*}
    [Group G] (h : IsSigmaPrimary σ (Nat.card G)) : IsSigmaNilpotent σ G := by
  refine ⟨1, fun _ ↦ ⊤, fun _ ↦ ⟨inferInstance, by simpa using h⟩, by simp, fun k ↦ ?_⟩
  have hk : ({k}ᶜ : Set (Fin 1)) = ∅ := by
    ext j
    simp [Subsingleton.elim j k]
  simp [hk]

private def singletons (p : Nat.Primes) : Set ℕ := {p.val}

-- The cyclic group of order 8 is σ-nilpotent for the partition of the primes into singletons.
example : IsSigmaNilpotent singletons (Multiplicative (ZMod 8)) := by
  refine isSigmaNilpotent_of_isSigmaPrimary ⟨⟨2, Nat.prime_two⟩, fun p hp h ↦ ?_⟩
  rw [show Nat.card (Multiplicative (ZMod 8)) = 2 ^ 3 from Nat.card_zmod 8] at h
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
