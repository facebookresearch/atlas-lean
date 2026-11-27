/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

open MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted

-- Empty prime support still contains the trivial group.
example : (primeSupportClass ∅).mem Unit :=
  (isFormation_primeSupportClass ∅).2.1

-- The cyclic group of order three separates the two comparable vertices of the pentagon.
example : (primeSupportClass {2, 3}).mem (Multiplicative (ZMod 3)) ∧
    ¬ (primeSupportClass {2}).mem (Multiplicative (ZMod 3)) := by
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := Nat.card_zmod 3
  constructor
  · refine ⟨inferInstance, fun q hq hd ↦ ?_⟩
    have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hcard ▸ hd)
    simp [this]
  · intro h
    have : 3 ∈ ({2} : Set ℕ) := h.2 3 Nat.prime_three (by rw [hcard])
    simp at this

-- Even the largest formation excludes infinite groups.
example : ¬ (primeSupportClass Set.univ).mem (Multiplicative ℤ) := by
  intro h
  have : Finite (Multiplicative ℤ) := h.1
  exact not_finite (Multiplicative ℤ)
