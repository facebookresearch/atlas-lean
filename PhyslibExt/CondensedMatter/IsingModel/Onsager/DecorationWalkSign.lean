/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationWalkHomology
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedHomology

/-!

# Kac-Ward weights of decorated cycles

The first-return weight of a rooted decorated cycle equals its spin character times the product of
its edge weights.

## i. Overview

The first-return loop of a rooted decorated cycle is a first-return segment of the twisted
edge-weighted Kac-Ward matrix, and its weight is the loop weight of the corresponding closed dart
walk. With the turning sign supplied, this weight is the spin character of the homology class of the
cycle times the product of the weights of its torus edges, which is exactly the weight of the cycle
in the character-weighted even-subgraph sum.

## ii. Key results

- `ons_firstReturnWeight_decCycle` : the first-return weight of a decorated cycle
- `ons_decCycleFirstReturn_weight_eq_spinCharacter` : it equals the spin character times the edge
  weights

## iii. Table of contents

- A. Weights of decorated cycles

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217
- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337

-/

@[expose] public section

namespace StatMech.Onsager

open BigOperators

/-! ## A. Weights of decorated cycles -/

lemma ons_loopWeight_eq_edgeWeight_neZero
    {E : Type*} [Fintype E] [DecidableEq E]
    (Lambda : Matrix E E ℂ) {n : ℕ} [NeZero n] (v : Fin n → E) :
    ons_loopWeight Lambda v =
      ons_edgeWeight Lambda (List.ofFn v ++ [v 0]) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact ons_loopWeight_eq_edgeWeight Lambda v

lemma ons_decCycleFirstReturn_edgeWeight_eq_loopWeight
    {L : ℕ} [NeZero L] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (Lambda : Matrix (ons_Dart L) (ons_Dart L) ℂ) :
    ons_edgeWeight Lambda (ons_decCycleFirstReturn q) =
      ons_loopWeight Lambda (ons_decCycleDartLoop q) := by
  rw [ons_loopWeight_eq_edgeWeight_neZero]
  rw [ons_decCycleDartList_ofFn, ons_decCycleDartLoop_zero]
  rw [ons_decCycleDartList_eq]
  rfl

lemma ons_firstReturnWeight_decCycle
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (Lambda : Matrix (ons_Dart L) (ons_Dart L) ℂ) :
    ons_firstReturnWeight Lambda d (ons_dartRev L d)
        (ons_decCycleFirstReturn q) =
      ons_edgeWeight Lambda (ons_decCycleFirstReturn q) := by
  unfold ons_firstReturnWeight
  rw [ite_eq_left (ons_decCycleFirstReturn_valid q hq hsnd)]

lemma ons_decCycleFirstReturn_unitWeight
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (omega : ℂ) (a b : Fin 2) :
    ons_edgeWeight
        (ons_KWmatWeightedPhase L (fun _ => 1) omega
          (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_decCycleFirstReturn q) =
      ons_spinLinearCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) *
        ∏ k, ons_turnW omega
          (ons_decCycleDartLoop q (k + 1)).2
          (ons_decCycleDartLoop q k).2 := by
  rw [ons_decCycleFirstReturn_edgeWeight_eq_loopWeight]
  rw [ons_loopWeight_KWmatWeightedPhase,
    ons_loopWeight_KWmatWeighted_eq (fun _ => 1) omega
      (ons_decCycleDartLoop q)
      (ons_decCycleDartLoop_valid q hq hsnd),
    ons_decCycle_spinPhase_product_eq_homology q hq hsnd a b]
  simp

lemma ons_decCycleFirstReturn_weight_eq_spinCharacter
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2)
    (hturn : (∏ k, ons_turnW ons_turnRoot
        (ons_decCycleDartLoop q (k + 1)).2
        (ons_decCycleDartLoop q k).2) =
      -(ons_spinCharacter 0 0
        (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ)) :
    ons_edgeWeight
        (ons_KWmatWeightedPhase L weight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_decCycleFirstReturn q) =
      -(ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) *
        ∏ edge ∈ ons_walkOriginalEdges q, weight edge := by
  rw [ons_decCycleFirstReturn_weight_factor q hq hsnd,
    ons_decCycleFirstReturn_unitWeight q hq hsnd ons_turnRoot a b,
    hturn]
  have hchar := ons_spinLinear_mul_quadratic a b
    (ons_evenHomology L (ons_walkOriginalEdges q))
  rw [← hchar]
  ring

end StatMech.Onsager
