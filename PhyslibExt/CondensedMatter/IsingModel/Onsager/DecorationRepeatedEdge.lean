/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalSquarefree
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalToSpin
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.FreeEnergyOfSpinKacWard

/-!

# The formal identity from vanishing of repeated-edge coefficients

If the coefficients of the formal Kac-Ward root vanish at every exponent repeating a decorated edge,
Onsager's formula follows.

## i. Overview

`ons_DecFormalRepeatedEdgeVanishes` states that on every torus, for every spin structure, the
coefficient of the formal Kac-Ward root at any exponent using a decorated edge at least twice is
zero. It implies the formal Kac-Ward identity, then the spin Kac-Ward identities, and finally the
convergence of the torus pressure to Onsager's pressure for every `β ≥ 0`.

## ii. Key results

- `ons_DecFormalRepeatedEdgeVanishes` : vanishing of repeated-edge coefficients
- `ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes` : it implies the formal identity
- `ons_free_energy_of_repeatedEdgeVanishes` : it implies Onsager's formula

## iii. Table of contents

- A. Repeated-edge vanishing and its consequences

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- L. Onsager, *Crystal statistics. I. A two-dimensional model with an order-disorder transition*,
  Phys. Rev. 65 (1944) 117-149

-/

@[expose] public section

namespace StatMech.Onsager

/-! ## A. Repeated-edge vanishing and its consequences -/

/-- On every `L × L` torus with `L > 2` and for every spin structure, the coefficient of the formal
Kac-Ward root at any exponent that uses some decorated edge at least twice is zero. -/
def ons_DecFormalRepeatedEdgeVanishes : Prop :=
  ∀ (L : ℕ) (hL : 2 < L),
    letI : Fact (2 < L) := ⟨hL⟩
    ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ)
      (edge : ons_DecEdge L), 2 ≤ m edge →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0

lemma ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes) :
    ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_decoratedFormalKacWardIdentity L := by
  intro L hL
  let : Fact (2 < L) := ⟨hL⟩
  exact ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes
    L (hvanish L hL)

lemma ons_spinKacWardIdentities_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  apply ons_spinKacWardIdentities_of_decoratedFormal
  exact ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes hvanish

lemma ons_free_energy_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop (nhds (ons_pressure beta)) := by
  apply ons_free_energy_of_spinKacWard_all
    (fun gamma ↦ ons_spinKacWardIdentities_of_repeatedEdgeVanishes
      hvanish gamma)
  exact hbeta

end StatMech.Onsager
