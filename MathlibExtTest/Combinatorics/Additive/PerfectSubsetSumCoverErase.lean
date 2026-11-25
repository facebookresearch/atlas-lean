/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCoverErase

namespace MetaMathlibExt

open PerfectSubsetSumCover

/-- Erasing `1` from the perfect cover `{1, 2}` leaves the even residues covered. -/
example :
    let c := coverCount (fun x : ({1, 2} : Finset (ZMod 4)).erase 1 => (x : ZMod 4))
    2 * (Finset.univ.filter fun g => c g = 1).card = 4 ∧ c 2 = 1 ∧ c 1 = 0 := by
  intro c
  have h := perfectCover_erase_coverCount (n := 2) (by decide)
    isPerfectCover_zmod_four.1 (z := 1) (by simp)
  have hshift := h.2 0 (by decide) 1 (by decide)
  change 1 ≤ c 2 ∧ c 1 = 0 at hshift
  exact ⟨h.1.2, Nat.le_antisymm (h.1.1 2) hshift.1, hshift.2⟩

end MetaMathlibExt
