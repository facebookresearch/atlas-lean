/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.MetaAutomaticTwoAffine

open MetaMathlibExt

private def samplePair (n : ℕ) : Bool × Bool :=
  (metaAutomaticTwo n, metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat))

-- All four transitions at the initial state, including the digit-zero loop.
example : [samplePair 0, samplePair 1, samplePair 2, samplePair 3] =
    [(false, false), (true, false), (true, true), (false, true)] := by
  have hzero : samplePair 0 = (false, false) := by decide +kernel
  have h := (metaAutomaticTwo_affine (s := samplePair) (hs := fun _ => rfl)).1 0
  simp only [Nat.mul_zero, Nat.zero_add] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  conv at h0 =>
    rhs
    rw [hzero]
  simp only [hzero] at h1 h2 h3
  rw [h0, h1, h2, h3]
  decide

-- The index 11 has MSB-first digits [2, 3]; reversing them changes the output (index 14).
example : metaAutomaticTwo 11 = true ∧ metaAutomaticTwo 14 = false := by decide +kernel

example : [samplePair 44, samplePair 45, samplePair 46, samplePair 47] =
    [(true, false), (false, false), (false, true), (true, true)] := by
  have hbase : samplePair 11 = (true, true) := by decide +kernel
  obtain ⟨h0, h1, h2, h3⟩ := (metaAutomaticTwo_affine (s := samplePair) (hs := fun _ => rfl)).1 11
  rw [hbase] at h0 h1 h2 h3
  change [samplePair (4 * 11), samplePair (4 * 11 + 1), samplePair (4 * 11 + 2),
    samplePair (4 * 11 + 3)] = _
  rw [h0, h1, h2, h3]
  decide