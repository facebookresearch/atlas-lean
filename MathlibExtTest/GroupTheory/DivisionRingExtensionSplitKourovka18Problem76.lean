/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DivisionRingExtensionSplitKourovka18Problem76

namespace MathlibExt.GroupTheory.DivisionRingExtensionSplitKourovka18Problem76Wanted

-- Apply the refutation to the fully expanded splitting assertion.
example
    (h : ∀ (A : Type) [DivisionRing A] (G : Subgroup Aˣ) (E : Type) [Group E]
      (i : Multiplicative A →* E) (π : E →* G), Function.Injective i → Function.Surjective π →
      i.range = π.ker →
      (∀ (e : E) (a : A), e * i (Multiplicative.ofAdd a) * e⁻¹ =
        i (Multiplicative.ofAdd (((π e : Aˣ) : A) * a))) →
      ∃ s : G →* E, ∀ g : G, π (s g) = g) : False :=
  divisionRingMultiplicationExtensionsSplit_refuted h

end MathlibExt.GroupTheory.DivisionRingExtensionSplitKourovka18Problem76Wanted
