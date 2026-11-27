/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EvenPseudoprimeResidueSixteen

/-! # Tests for even pseudoprimes modulo sixteen -/

open MathlibExt.NumberTheory MetaMathlibExt

-- Lehmer's example attains residue 14.
example : IsEvenPseudoprime 161038 ∧ 161038 % 16 = 14 := by
  have hN : IsEvenPseudoprime 161038 := ⟨by decide, by decide, by decide +kernel⟩
  exact ⟨hN, (evenPseudoprime_mod_sixteen (hN := hN)).resolve_left (by decide)⟩

-- The third even pseudoprime attains residue 2.
example : IsEvenPseudoprime 2568226 ∧ 2568226 % 16 = 2 := by
  have hN : IsEvenPseudoprime 2568226 := ⟨by decide, by decide, by decide +kernel⟩
  exact ⟨hN, (evenPseudoprime_mod_sixteen hN).resolve_right (by decide)⟩
