/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.AvoidZZ1Z

open MathlibExt.NumberTheory.OeisConjecturesWanted

-- The first recurrence step over a one-letter alphabet has no bad extensions.
example : avoidZZ1Z 1 3 = 1 := by
  obtain ⟨h₀, h₁, h₂, hrec⟩ := avoidZZ1Z_spec 1 (by decide)
  have h : (avoidZZ1Z 1 3 : ℤ) = 1 * avoidZZ1Z 1 2 - avoidZZ1Z 1 1 + avoidZZ1Z 1 0 :=
    hrec 3 (by decide)
  rw [h₀, h₁, h₂] at h
  omega

-- At length five, the forbidden pattern can overlap itself in a two-letter alphabet.
example : avoidZZ1Z 2 5 = 21 := by
  have h₂ : avoidZZ1Z 2 2 = 4 := by decide +kernel
  have h₃ : avoidZZ1Z 2 3 = 7 := by decide +kernel
  have h₄ : avoidZZ1Z 2 4 = 12 := by decide +kernel
  have h : (avoidZZ1Z 2 5 : ℤ) = 2 * avoidZZ1Z 2 4 - avoidZZ1Z 2 3 + avoidZZ1Z 2 2 :=
    (avoidZZ1Z_spec 2 (by decide)).2.2.2 5 (by decide)
  rw [h₂, h₃, h₄] at h
  omega
