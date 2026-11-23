/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationWalkSign
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationTurnTransfer

/-!

# Signed weights of decorated cycles

The first-return weight of a rooted decorated cycle is minus its spin character times its edge
weights.

## i. Overview

Combining the turning sign of a decorated cycle (`-1` for zero homology, `1` otherwise) with the
boundary phases, the twisted edge-weighted Kac-Ward first-return weight of a rooted decorated cycle
is `-χ_{a,b}(class) ∏ w_e`. The minus sign is the one that makes `∏ (1 - λ)` reproduce the
character-weighted even-subgraph sum.

## ii. Key results

- `ons_decCycleFirstReturn_weight_eq_neg_spinCharacter` : the first-return loop weight of a
  decorated cycle
- `ons_firstReturnWeight_decCycle_eq_neg_spinCharacter` : the same as a first-return weight

## iii. Table of contents

- A. Signed cycle weights

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217
- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337

-/

@[expose] public section

namespace StatMech.Onsager

open BigOperators

/-! ## A. Signed cycle weights -/

lemma ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) :
    ons_edgeWeight
        (ons_KWmatWeightedPhase L weight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_decCycleFirstReturn q) =
      -(ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) *
        ∏ edge ∈ ons_walkOriginalEdges q, weight edge := by
  exact ons_decCycleFirstReturn_weight_eq_spinCharacter q hq hsnd
    weight a b
    (ons_decCycle_turnProduct_eq_neg_spinCharacter L q hq hsnd)

lemma ons_firstReturnWeight_decCycle_eq_neg_spinCharacter
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) :
    ons_firstReturnWeight
        (ons_KWmatWeightedPhase L weight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        d (ons_dartRev L d) (ons_decCycleFirstReturn q) =
      -(ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) *
        ∏ edge ∈ ons_walkOriginalEdges q, weight edge := by
  rw [ons_firstReturnWeight_decCycle q hq hsnd]
  exact ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
    q hq hsnd weight a b

end StatMech.Onsager
