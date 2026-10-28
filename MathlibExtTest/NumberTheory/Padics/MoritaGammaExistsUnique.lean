/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.MoritaGammaExistsUnique

/-!
# Tests for the existence and uniqueness of Morita's `p`-adic gamma function
-/

@[expose] public section

open MetaMathlibExt

example : ∃! Γ : C(ℤ_[3], ℤ_[3]), IsMoritaPadicGamma 3 Γ :=
  existsUnique_moritaPadicGamma 3 (by decide)

/-- The extension is pinned down at the naturals. -/
example (Γ : C(ℤ_[3], ℤ_[3])) (hΓ : IsMoritaPadicGamma 3 Γ) :
    Γ ((3 : ℕ) : ℤ_[3]) = moritaGammaNat 3 3 :=
  hΓ.natCast_eq (by decide)
