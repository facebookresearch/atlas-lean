/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalCoefficient

/-!

# Reduction of the formal identity to repeated edges

The formal Kac-Ward identity holds once every coefficient of the formal root with a repeated
variable vanishes.

## i. Overview

An exponent is not squarefree exactly when some variable has exponent at least `2`. Since the formal
root and the decorated spin polynomial agree on squarefree monomials, and the polynomial has only
squarefree monomials, the formal Kac-Ward identity follows from the vanishing of the root's
coefficients at exponents with a repeated variable.

## ii. Key results

- `ons_not_isSquarefreeExponent_iff` : non-squarefree means a repeated variable
- `ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes` : the reduction

## iii. Table of contents

- A. The reduction

## iv. References

- None; the material is standard.

-/

@[expose] public section

namespace StatMech.Onsager

open Finset StatMech.Ising

/-! ## A. The reduction -/

lemma ons_not_isSquarefreeExponent_iff
    {E : Type*} (m : E →₀ ℕ) :
    ¬ ons_IsSquarefreeExponent m ↔ ∃ edge, 2 ≤ m edge := by
  constructor
  · intro hm
    by_contra hnone
    apply hm
    intro edge
    by_contra hle
    apply hnone
    exact ⟨edge, by omega⟩
  · rintro ⟨edge, hedge⟩ hm
    have := hm edge
    omega

lemma ons_decoratedFormalKacWardIdentity_of_nonsquarefree_vanishes
    (L : ℕ) [Fact (2 < L)]
    (hvanish : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ),
      ¬ ons_IsSquarefreeExponent m →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
    ons_decoratedFormalKacWardIdentity L :=
  ons_decoratedFormalKacWardIdentity_of_nonsquarefree_zero L hvanish

lemma ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes
    (L : ℕ) [Fact (2 < L)]
    (hvanish : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ)
      (edge : ons_DecEdge L), 2 ≤ m edge →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
    ons_decoratedFormalKacWardIdentity L := by
  apply ons_decoratedFormalKacWardIdentity_of_nonsquarefree_vanishes L
  intro a b m hm
  obtain ⟨edge, hedge⟩ := (ons_not_isSquarefreeExponent_iff m).mp hm
  exact hvanish a b m edge hedge

end StatMech.Onsager
