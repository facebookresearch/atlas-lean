/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SDiophantineSystemFour

namespace MetaMathlibExt

/-- The triple (1, 2, 4) realizes the required powers 3, 5 and 9.
It cannot be extended by a fourth entry with the other three factorizations. -/
example {d : ℕ} (hd : 4 < d) :
    ¬∃ x y z w : ℕ, 2 * d + 1 = 5 ^ x ∧ d + 1 = 5 ^ y * 3 ^ z ∧ 4 * d + 1 = 3 ^ w := by
  rintro ⟨x, y, z, w, hbd, had, hcd⟩
  exact not_exists_sDiophantine_system_four (p := 5) (q := 3) (a := 1) (b := 2) (c := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hd ⟨1, 0, 2, 1, x, y, z, w, rfl, rfl, rfl, hbd, by simpa using had, hcd⟩

#print axioms not_exists_sDiophantine_system_four

end MetaMathlibExt
