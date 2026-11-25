/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.OrderOfElement
import MathlibExt.GroupTheory.InvolutionFreeQuotientKourovka18Problem94

namespace MathlibExt.GroupTheory.InvolutionFreeQuotientKourovka18Problem94Wanted

-- Recover the existential statement using Mathlib's order of an element.
example : ∃ (G : Type) (_ : Group G), (∀ g : G, orderOf g ≠ 2) ∧
    ∃ a : G, (¬ ∃ x : G, x ^ 2 = a) ∧ ∃ n : ℕ, Odd n ∧
      ∃ y : G ⧸ Subgroup.normalClosure {a ^ n}, orderOf y = 2 := by
  by_contra h
  apply involutionFreeQuotientByNonSquarePower_refuted
  intro G inst hG a ha n hn y hy
  by_contra hne
  refine h ⟨G, inst, ?_, a, ha, n, hn, y, orderOf_eq_prime hy hne⟩
  intro g hg
  obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.mp hg
  exact hne (hG g hsq)

end MathlibExt.GroupTheory.InvolutionFreeQuotientKourovka18Problem94Wanted
