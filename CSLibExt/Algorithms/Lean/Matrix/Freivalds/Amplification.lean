/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Probability
public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Repeat
import Mathlib.Tactic

/-!
# Freivalds amplification by uniform complete histories

MIT 6.046J Spring 2015 Lecture 6, printed page 2, supplies the binary trial.
All matrices and arithmetic here are over `ZMod 2` by intentional GF(2) specialization (see
`Freivalds.Basic`); the lecture itself only takes the seed vector binary over a general
coefficient domain.
Independent repetition is the campaign extension. The ideal law is uniform
on the complete supplied history and is mapped through the actual repeated executor.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

open scoped ENNReal

@[expose] public section

namespace Cslib.Algorithms.Lean.Matrix

/-- **Output distribution of repeated Freivalds trials.** For natural numbers $n, k$ and
$n \times n$ matrices $A, B, C$ over $\mathbb{F}_2$, this is the probability distribution on
$\{\mathrm{true}, \mathrm{false}\}$ of the result returned by the repeated Freivalds executor on
$A, B, C$ when its history of $k$ seeds is drawn uniformly from $(\mathbb{F}_2^n)^k$. -/
noncomputable def freivaldsRepeatLaw {n : Nat} (k : Nat)
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin k → Fin n → ZMod 2)).map fun history =>
    (freivaldsRepeat A B C history).ret

/-- **Uniform mass of a Freivalds seed history.** For all natural numbers $n$ and $k$, under the
uniform distribution on histories of $k$ seeds, that is, on $(\mathbb{F}_2^n)^k$, every history
has probability exactly $(2^{nk})^{-1}$. This includes the cases $k = 0$ and $n = 0$. -/
theorem freivaldsHistory_pointMass {n k : Nat} (history : Fin k → Fin n → ZMod 2) :
    Cslib.Probability.PMF.uniformOfFintype (Fin k → Fin n → ZMod 2) history =
      ((2 : ℝ≥0∞) ^ (n * k))⁻¹ := by
  simp [Cslib.Probability.PMF.uniformOfFintype_apply, pow_mul]

/-- **Counting accepted histories of repeated Freivalds trials.** Let $n, k$ be natural numbers
and let $A, B, C$ be $n \times n$ matrices over $\mathbb{F}_2$. The number of histories
$(r_1, \dots, r_k)$ of seeds $r_i \in \mathbb{F}_2^n$ on which the repeated Freivalds executor
accepts equals $a^k$, where $a$ is the number of seeds $r \in \mathbb{F}_2^n$ on which a single
Freivalds trial accepts. -/
theorem freivaldsRepeat_acceptanceCard {n k : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n) :
    Fintype.card {history : Fin k → Fin n → ZMod 2 //
      (freivaldsRepeat A B C history).ret = true} =
      (Fintype.card {r : Fin n → ZMod 2 // (freivaldsTrial A B C r).ret = true}) ^ k := by
  classical
  let accepted := Finset.univ.filter fun r : Fin n → ZMod 2 =>
    (freivaldsTrial A B C r).ret = true
  have accepted_card :
      Fintype.card {r : Fin n → ZMod 2 // (freivaldsTrial A B C r).ret = true} =
        accepted.card :=
    Fintype.card_of_subtype accepted (by intro r; simp [accepted])
  calc
    Fintype.card {history : Fin k → Fin n → ZMod 2 //
        (freivaldsRepeat A B C history).ret = true} =
        (Fintype.piFinset fun _ : Fin k => accepted).card :=
      Fintype.card_of_subtype _ (by
        intro history
        simp [accepted, freivaldsRepeat_accept_iff])
    _ = accepted.card ^ k := Fintype.card_piFinset_const accepted k
    _ = _ := by rw [accepted_card]

/-- **Acceptance probability of repeated Freivalds trials.** Let $n, k$ be natural numbers and
let $A, B, C$ be $n \times n$ matrices over $\mathbb{F}_2$. If the history of $k$ seeds is drawn
uniformly from $(\mathbb{F}_2^n)^k$, the probability that the repeated Freivalds executor accepts
is $p^k$, where $p$ is the probability that a single Freivalds trial accepts on a seed drawn
uniformly from $\mathbb{F}_2^n$. -/
theorem freivaldsRepeatLaw_acceptance_power {n : Nat} (k : Nat)
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n) :
    freivaldsRepeatLaw k A B C true = (freivaldsTrialLaw A B C true) ^ k := by
  classical
  have fiber : freivaldsRepeatLaw k A B C true =
      (Fintype.card {history : Fin k → Fin n → ZMod 2 //
        (freivaldsRepeat A B C history).ret = true} : ℝ≥0∞) /
          Fintype.card (Fin k → Fin n → ZMod 2) := by
    calc
      freivaldsRepeatLaw k A B C true =
          (freivaldsRepeatLaw k A B C).toOuterMeasure {true} :=
        (PMF.toOuterMeasure_apply_singleton (freivaldsRepeatLaw k A B C) true).symm
      _ = (Cslib.Probability.PMF.uniformOfFintype (Fin k → Fin n → ZMod 2)).toOuterMeasure
          {history | (freivaldsRepeat A B C history).ret = true} := by
        rw [freivaldsRepeatLaw, PMF.toOuterMeasure_map_apply]
        rfl
      _ = _ := by
        rw [PMF.toOuterMeasure_apply, tsum_fintype]
        simp only [Set.indicator_apply, Set.mem_ofPred_eq,
          Cslib.Probability.PMF.uniformOfFintype_apply]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Fintype.card_subtype]
        rfl
  rw [fiber, freivaldsTrialLaw_acceptance, freivaldsRepeat_acceptanceCard,
    Fintype.card_pi_const]
  simp only [Nat.cast_pow, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

/-- **Completeness of repeated Freivalds trials.** Let $n, k$ be natural numbers and let
$A, B, C$ be $n \times n$ matrices over $\mathbb{F}_2$ with $AB = C$. If the history of $k$
seeds is drawn uniformly from $(\mathbb{F}_2^n)^k$, then the repeated Freivalds executor accepts
with probability $1$. -/
theorem freivaldsRepeatLaw_complete {n : Nat} (k : Nat)
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (correct : freivaldsMatrix A * freivaldsMatrix B = freivaldsMatrix C) :
    freivaldsRepeatLaw k A B C true = 1 := by
  rw [freivaldsRepeatLaw_acceptance_power, freivaldsTrialLaw_complete A B C correct]
  exact one_pow k

/-- **Soundness of repeated Freivalds trials.** Let $n, k$ be natural numbers and let
$A, B, C$ be $n \times n$ matrices over $\mathbb{F}_2$ with $AB \ne C$. If the history of $k$
seeds is drawn uniformly from $(\mathbb{F}_2^n)^k$, then the repeated Freivalds executor accepts
with probability at most $(2^k)^{-1}$. -/
theorem freivaldsRepeatLaw_sound {n : Nat} (k : Nat)
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (wrong : freivaldsMatrix A * freivaldsMatrix B ≠ freivaldsMatrix C) :
    freivaldsRepeatLaw k A B C true ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [freivaldsRepeatLaw_acceptance_power]
  calc
    (freivaldsTrialLaw A B C true) ^ k ≤ ((1 : ℝ≥0∞) / 2) ^ k := by
      gcongr
      exact freivaldsTrialLaw_sound A B C wrong
    _ = _ := by simp [div_eq_mul_inv, ENNReal.inv_pow]

end Cslib.Algorithms.Lean.Matrix
