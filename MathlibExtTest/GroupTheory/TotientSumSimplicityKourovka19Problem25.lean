/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TotientSumSimplicityKourovka19Problem25

open MathlibExt.GroupTheory.TotientSumSimplicityKourovka19Problem25Wanted

-- Extract witnesses with both numerical equalities and the two simplicity conditions.
example : ∃ (G H : Type) (_ : Group G) (_ : Group H) (_ : Fintype G) (_ : Fintype H),
    Fintype.card G = Fintype.card H ∧
    (∑ g : G, Nat.totient (orderOf g)) = (∑ h : H, Nat.totient (orderOf h)) ∧
    IsSimpleGroup G ∧ ¬ IsSimpleGroup H := by
  classical
  by_contra h
  apply sameOrderTotientSumSimple_refuted
  intro G H _ _ _ _ hcard hsum hsimple
  by_contra hH
  exact h ⟨G, H, _, _, _, _, hcard, hsum, hsimple, hH⟩
