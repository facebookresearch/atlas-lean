/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonSubsetCount

open MathlibExt.Combinatorics.SidonSubsetCountErdosProblem861Wanted

-- The empty interval has one Sidon subset and maximum size zero.
example : (sidonSubsetsUpTo 0).card = 1 ∧ maxSidonSize 0 = 0 := by
  classical
  have hfamily : sidonSubsetsUpTo 0 = {∅} := by
    ext s
    simp [sidonSubsetsUpTo, Set.IsSidon]
    rintro rfl
    simp
  simp [maxSidonSize, hfamily]

-- Every positive interval includes its right endpoint as a singleton Sidon subset.
example {N : ℕ} (hN : 0 < N) : ({N} : Finset ℕ) ∈ sidonSubsetsUpTo N := by
  classical
  simp [sidonSubsetsUpTo, Set.IsSidon]
  omega

-- Repeated summands matter: 1 + 3 = 2 + 2.
example : ({1, 2, 3} : Finset ℕ) ∉ sidonSubsetsUpTo 3 := by
  classical
  intro h
  have hs := (Finset.mem_filter.mp h).2
  rcases hs 1 (by decide) 3 (by decide) 2 (by decide) 2 (by decide) rfl with h | h <;> omega
