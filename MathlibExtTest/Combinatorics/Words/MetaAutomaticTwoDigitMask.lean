/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.MetaAutomaticTwoDigitMask

namespace MetaMathlibExt

private def testMask (n : ℕ) : ℕ :=
  ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 3 ≠ 2), n / 2 ^ i % 2 * 2 ^ i

example : metaAutomaticTwo 0 = false := by
  rw [(metaAutomaticTwo_eq_thueMorse_mask testMask (fun _ => rfl) 0).1]
  decide

-- 23 = 10111₂. The bit of weight 4 is dropped, and 19 has odd binary parity.
example : metaAutomaticTwo 23 = true := by
  rw [(metaAutomaticTwo_eq_thueMorse_mask testMask (fun _ => rfl) 23).1,
    show testMask 23 = 19 by decide]
  decide

-- 45 = 231₄. The digit at position 1 keeps its high bit; position 2 keeps only its low bit.
example : testMask 45 = 9 := by
  rw [(metaAutomaticTwo_eq_thueMorse_mask testMask (fun _ => rfl) 45).2]
  decide

end MetaMathlibExt
