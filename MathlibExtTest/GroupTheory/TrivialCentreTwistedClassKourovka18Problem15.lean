/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TrivialCentreTwistedClassKourovka18Problem15

open MathlibExt.GroupTheory.TrivialCentreTwistedClassKourovka18Problem15Wanted

-- The inner automorphism induced by the identity gives a singleton twisted class.
example (G : Type) [Group G] : twistedUnitClass (MulAut.conj (1 : G)) = {1} := by
  ext g
  simp [twistedUnitClass]

-- Apply the refutation with the conjecture and its twisted class fully unfolded.
example : ¬ ∀ (G : Type) [Group G], Nontrivial G → Subgroup.center G = ⊥ →
    ∃ a : G, ¬ ∃ H : Subgroup G, (H : Set G) =
      Set.range (fun g : G ↦ g⁻¹ * (MulAut.conj a) g) :=
  trivialCentreHasInnerTwistedClassNotSubgroup_refuted
