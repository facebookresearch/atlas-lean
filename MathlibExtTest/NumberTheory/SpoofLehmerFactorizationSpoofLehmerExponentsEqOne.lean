/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SpoofLehmerFactorizationSpoofLehmerExponentsEqOne
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.SpoofLehmerFactorizationSpoofLehmerExponentsEqOne

open MetaMathlibExt

-- The nontrivial `2`-Lehmer factorization `3 · 3` has all exponents `1`.
example : ∀ p ∈ ({(3, 1), (3, 1)} : Multiset (ℕ × ℕ)), p.2 = 1 :=
  spoofLehmer_exponents_eq_one _ 2 isSpoofLehmer_three_three (by
    intro h
    have h3 := h (3, 1) (by simp)
    norm_num at h3)

end MathlibExtTest.NumberTheory.SpoofLehmerFactorizationSpoofLehmerExponentsEqOne
