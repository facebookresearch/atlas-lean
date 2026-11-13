/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Roots

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] public section

open Polynomial

/-- One-variable Boolean sum-check: the verifier accepts the
prover's polynomial `q` for the claim "the sum of `p` over
`{0, 1}` is `H`" at challenge `r` when `q`'s own Boolean sum
matches `H` and `q` agrees with the oracle `p` at `r`. -/
def accept1 (p q : F[X]) (H r : F) : Prop :=
  q.eval 0 + q.eval 1 = H ∧ q.eval r = p.eval r

/-- Completeness: the honest prover is always accepted. -/
theorem sumcheck1_complete (p : F[X]) (H : F)
    (hH : p.eval 0 + p.eval 1 = H) (r : F) :
    accept1 p p H r := by
  unfold accept1
  exact ⟨hH, rfl⟩

/-- Soundness: a prover polynomial different from `p`, both of
degree at most `d`, can agree with `p` at no more than `d`
challenges. -/
theorem sumcheck1_sound (p q : F[X]) (d : ℕ)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hne : q ≠ p) :
    (Finset.univ.filter (fun r => q.eval r = p.eval r)).card
      ≤ d := by
  have hsub : q - p ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (q - p).natDegree ≤ d :=
    le_trans (natDegree_sub_le q p) (max_le hq hp)
  have hsub2 : (Finset.univ.filter (fun r => q.eval r = p.eval r)).card
      ≤ (q - p).natDegree := by
    apply card_le_degree_of_subset_roots
    intro a ha
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [mem_roots hsub, IsRoot.def]
    rw [eval_sub, sub_eq_zero]
    exact ha
  exact le_trans hsub2 hdeg
