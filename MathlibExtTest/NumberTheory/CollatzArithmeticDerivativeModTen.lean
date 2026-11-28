/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CollatzArithmeticDerivativeModTen

namespace MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeModTen

open MetaMathlibExt

-- Each semiprime's two factor residues add to ten.
example {p q r s : ℕ} (h : IsCompatibleSemiprimePair p q r s) :
    p % 10 + q % 10 = 10 ∧ r % 10 + s % 10 = 10 := by
  obtain ⟨hpq, hrs⟩ := h.mod_ten
  exact ⟨by omega, by omega⟩

-- The first pair in Bradshaw's Table 1 realizes opposite residue orders.
example : (71 % 10 = 1 ∧ 1609 % 10 = 9) ∧ (349 % 10 = 9 ∧ 491 % 10 = 1) := by
  obtain ⟨hpq, hrs⟩ := isCompatibleSemiprimePair_71_1609.mod_ten
  exact ⟨hpq.resolve_right (by decide), hrs.resolve_left (by decide)⟩

end MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeModTen
