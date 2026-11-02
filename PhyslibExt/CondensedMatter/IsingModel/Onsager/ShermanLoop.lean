/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.TracePowWalk

/-!

# Cyclic loop weights

The weight of a cyclic sequence of directed edges and its invariance under rotation.

## i. Overview

A cyclic sequence `v : Fin n → E` of states carries the weight `∏ₖ Λ (v k) (v (k + 1))`, indices
taken modulo `n`. Rotating the sequence by one step does not change this product, so the weight is a
function of the closed loop rather than of its starting point. Combined with the walk expansion of
`tr (Λ ^ n)` this is the starting point of Sherman's proof of the Feynman identity, where rotation
classes of closed walks are grouped into loops.

## ii. Key results

- `ons_loopWeight` : the cyclic product of matrix entries along a sequence
- `ons_trace_pow_eq_loopWeight_sum` : `tr (Λ ^ n)` is the sum of all loop weights of length `n`
- `ons_loopWeight_cyclicShift_iterate` : loop weights are invariant under rotation

## iii. Table of contents

- A. Loop weights and rotations

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217
- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators

/-! ## A. Loop weights and rotations -/

/-- The weight `∏ₖ Λ (v k) (v (k + 1))` of a cyclic sequence `v : Fin n → E`, indices taken modulo
`n`. -/
noncomputable def ons_loopWeight {E : Type*} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (v : Fin n → E) : ℂ := ∏ k : Fin n, Λ (v k) (v (k + 1))

/-- Rotation of a cyclic sequence by one step: `(ons_cyclicShift v) k = v (k + 1)`. -/
def ons_cyclicShift {E : Type*} {n : ℕ} [NeZero n] (v : Fin n → E) : Fin n → E :=
  fun k => v (k + 1)

lemma ons_loopWeight_cyclicShift {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (v : Fin n → E) :
    ons_loopWeight Λ (ons_cyclicShift v) = ons_loopWeight Λ v := by
  unfold ons_loopWeight ons_cyclicShift
  exact Equiv.prod_comp (Equiv.addRight (1 : Fin n)) (fun k => Λ (v k) (v (k + 1)))

lemma ons_trace_pow_eq_loopWeight_sum {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    (n : ℕ) [NeZero n] (hn : 0 < n) :
    (Λ ^ n).trace = ∑ v : Fin n → E, ons_loopWeight Λ v := by
  unfold ons_loopWeight
  exact ons_trace_pow_eq_walk_sum Λ n hn

lemma ons_loopWeight_cyclicShift_iterate {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (v : Fin n → E) (j : ℕ) :
    ons_loopWeight Λ (ons_cyclicShift^[j] v) = ons_loopWeight Λ v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ons_loopWeight_cyclicShift, ih]

end StatMech.Onsager
