/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.MoritaGammaExistsUnique

/-!
# Tests for the Morita gamma compatibility module

The old import path still provides the existence and uniqueness of Morita's `p`-adic gamma
function, including the deprecated odd-prime statement.
-/

@[expose] public section

open MetaMathlibExt

set_option linter.deprecated false in
example : ∃! Γ : C(ℤ_[3], ℤ_[3]), IsMoritaPadicGamma 3 Γ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact existsUnique_moritaPadicGamma 3 (by norm_num)

example (p : ℕ) [Fact p.Prime] : ∃! Γ : C(ℤ_[p], ℤ_[p]), IsMoritaPadicGamma p Γ :=
  existsUnique_isMoritaPadicGamma p
