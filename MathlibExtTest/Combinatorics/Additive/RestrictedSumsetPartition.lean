/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/GreensOpenProblems/25.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Adapted portion: the existential source-faithfulness statement.
-/

module

public import MathlibExt.Combinatorics.Additive.RestrictedSumsetPartition

@[expose] public section

/-!
# Tests for `MathlibExt.Combinatorics.Additive.RestrictedSumsetPartition`
-/

namespace MathlibExtTest.Combinatorics.Additive.RestrictedSumsetPartition

open Filter Asymptotics Green25

-- The restricted sumset of `{1, 2, 3}` is `{3, 4, 5}`.
example : Finset.restrictedSumset ({1, 2, 3} : Finset ℕ) = {3, 4, 5} := by decide

-- The binary restricted sumset agrees with the `h`-fold one at `h = 2`.
example (S : Finset ℕ) :
    S.restrictedSumset = MetaMathlibExt.restrictedSumset 2 S :=
  Finset.restrictedSumset_eq_metaMathlibExt_two S

-- The proved statement implies the Formal Conjectures shape of `Green25.green_25.upper`,
-- whose last conjunct is the weaker `¬ ∀ᶠ N, Property25 ..`.
example :
    ∃ k : ℕ → ℕ,
      (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
      (fun N => (k N : ℝ)) =o[atTop] bestUpper ∧
      ¬ ∀ᶠ N in atTop, Property25 (k N) N := by
  obtain ⟨k, hk, ho, hbad⟩ := green_25.upper
  refine ⟨k, hk, ho, fun hgood => ?_⟩
  obtain ⟨N, hN⟩ := (hbad.and hgood).exists
  exact hN.1 hN.2

end MathlibExtTest.Combinatorics.Additive.RestrictedSumsetPartition
