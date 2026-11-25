/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.LikelihoodWeighting
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Forward sampling and rejection conditioning for Bayesian networks

Ancestral sampling draws variables in topological order, each from its
conditional distribution given the earlier values. For a finite chain and for
a Bayesian network, the resulting probability mass function is exactly the
joint distribution (`Chain.samplePMF_apply` and
`BayesNet.samplePMF_apply`). For evidence of positive probability,
`BayesNet.posteriorPMF` is the normalized joint restricted to assignments
consistent with the evidence, and `BayesNet.rejectionSampling_tsum` shows that
repeated forward sampling until an evidence-consistent sample appears outputs
that posterior law.

## References

* S. Russell and P. Norvig, *Artificial Intelligence: A Modern Approach*, 4th
  ed., Chapter 13, prior sampling and rejection sampling.
* D. Koller and N. Friedman, *Probabilistic Graphical Models*, MIT Press,
  2009, Chapter 12.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.GraphicalModels

open Finset
open scoped ENNReal

namespace Chain

/-- The conditional distribution of a chain as a probability mass function. -/
noncomputable def condPMF {α : Type*} [Fintype α] (c : Chain α)
    (k : ℕ) (y : Fin k → α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal ((c.cond k y).weights a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (c.cond k y).nonneg i),
      (c.cond k y).total_of_fintype, ENNReal.ofReal_one])

/-- Ancestral (forward) sampling from a chain: sample the first `n` variables
in order, each from its conditional distribution given the earlier values. -/
noncomputable def samplePMF {α : Type*} [Fintype α] (c : Chain α) :
    (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | n + 1 => (c.samplePMF n).bind fun y => (c.condPMF n y).map (Fin.snoc y)

/-- **Ancestral sampling has the chain joint as its law.** -/
theorem samplePMF_apply {α : Type*} [Fintype α] (c : Chain α) :
    ∀ (n : ℕ) (x : Fin n → α), c.samplePMF n x = ENNReal.ofReal (c.joint n x) := by
  intro n
  induction n with
  | zero =>
    intro x
    simp only [samplePMF, PMF.pure_apply, joint_zero, ENNReal.ofReal_one]
    rw [ite_eq_left (Subsingleton.elim _ _)]
  | succ n ih =>
    intro x
    simp only [samplePMF, PMF.bind_apply, PMF.map_apply]
    refine (tsum_eq_single (Fin.init x) ?_).trans ?_
    · intro y hy
      refine mul_eq_zero_of_right _ ?_
      rw [tsum_fintype]
      apply Finset.sum_eq_zero
      intro a _
      have hne : ¬ (x = Fin.snoc y a) := by
        intro hcon
        have h2 : Fin.init x = y := by rw [hcon, Fin.init_snoc]
        exact hy h2.symm
      exact ite_eq_right hne
    · refine (congrArg (c.samplePMF n (Fin.init x) * ·)
        (tsum_eq_single (x (Fin.last n)) ?_)).trans ?_
      · intro a ha
        have hne : ¬ (x = Fin.snoc (Fin.init x) a) := by
          intro hcon
          have h2 : x (Fin.last n) = a := by rw [hcon, Fin.snoc_last]
          exact ha h2.symm
        exact ite_eq_right hne
      · have htrue : x = Fin.snoc (Fin.init x) (x (Fin.last n)) :=
          (Fin.snoc_init_self x).symm
        rw [ite_eq_left htrue, ih]
        simp only [condPMF, PMF.ofFintype_apply]
        rw [← ENNReal.ofReal_mul (c.joint_nonneg n _)]
        rfl

end Chain

namespace BayesNet

/-- Ancestral (forward) sampling from a Bayesian network. -/
noncomputable def samplePMF {α : Type*} {n : ℕ} [Fintype α] [Nonempty α]
    (b : BayesNet α n) : PMF (Fin n → α) :=
  b.toChain.samplePMF n

/-- **Ancestral sampling from a Bayesian network has the network joint as
its law.** -/
theorem samplePMF_apply {α : Type*} {n : ℕ} [Fintype α] [Nonempty α]
    (b : BayesNet α n) (x : Fin n → α) :
    b.samplePMF x = ENNReal.ofReal (b.joint x) := by
  exact Chain.samplePMF_apply b.toChain n x

/-- The posterior law of a Bayesian network given evidence of positive
probability, as a probability mass function. -/
noncomputable def posteriorPMF {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α] [Nonempty α]
    (b : BayesNet α n) (E : Finset (Fin n)) (e : Fin n → α)
    (hE : b.evidenceProb E e ≠ 0) : PMF (Fin n → α) :=
  PMF.ofFintype (fun x => if ∀ k ∈ E, x k = e k
    then ENNReal.ofReal (b.joint x / b.evidenceProb E e) else 0) (by
    have hev_nonneg : 0 ≤ b.evidenceProb E e := by
      unfold evidenceProb
      exact Finset.sum_nonneg fun x _ => b.toChain.joint_nonneg n x
    change (∑ x, (if ∀ k ∈ E, x k = e k
      then ENNReal.ofReal (b.joint x / b.evidenceProb E e) else 0)) = 1
    rw [← Finset.sum_filter,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg
        (show 0 ≤ b.joint i from b.toChain.joint_nonneg n i) hev_nonneg),
      ← Finset.sum_div]
    change ENNReal.ofReal (b.evidenceProb E e / b.evidenceProb E e) = 1
    rw [div_self hE, ENNReal.ofReal_one])

theorem posteriorPMF_apply {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α] [Nonempty α]
    (b : BayesNet α n) (E : Finset (Fin n)) (e x : Fin n → α)
    (hE : b.evidenceProb E e ≠ 0) :
    b.posteriorPMF E e hE x =
      if ∀ k ∈ E, x k = e k then ENNReal.ofReal (b.joint x / b.evidenceProb E e)
      else 0 := by
  simp only [posteriorPMF, PMF.ofFintype_apply]

/-- **Rejection sampling outputs the posterior law.** In repeated independent
forward samples from the network, the probability that the first sample
consistent with the evidence is exactly `x`, after any number `k` of rejected
samples, sums to the posterior probability of `x`. -/
theorem rejectionSampling_tsum {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : BayesNet α n) (E : Finset (Fin n)) (e x : Fin n → α)
    (hE : b.evidenceProb E e ≠ 0) :
    (∑' k : ℕ, (1 - ENNReal.ofReal (b.evidenceProb E e)) ^ k *
      (if ∀ j ∈ E, x j = e j then ENNReal.ofReal (b.joint x) else 0)) =
      b.posteriorPMF E e hE x := by
  have hev_nonneg : 0 ≤ b.evidenceProb E e :=
    Finset.sum_nonneg fun x _ => b.toChain.joint_nonneg n x
  have hev_pos : 0 < b.evidenceProb E e := lt_of_le_of_ne hev_nonneg (Ne.symm hE)
  have hev_le_one : b.evidenceProb E e ≤ 1 := by
    unfold evidenceProb
    have hsub : (∑ x with ∀ k ∈ E, x k = e k, b.joint x) ≤ ∑ x, b.joint x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => b.toChain.joint_nonneg n x)
    rw [b.sum_joint] at hsub
    exact hsub
  rw [posteriorPMF_apply]
  by_cases hcon : ∀ j ∈ E, x j = e j
  · have hcon' : ∀ k ∈ E, x k = e k := hcon
    rw [ite_eq_left hcon, ite_eq_left hcon', ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
      ENNReal.sub_sub_cancel ENNReal.one_ne_top
        (ENNReal.ofReal_le_one.mpr hev_le_one),
      ENNReal.ofReal_div_of_pos hev_pos, div_eq_mul_inv]
    exact mul_comm _ _
  · have hcon' : ¬ ∀ k ∈ E, x k = e k := hcon
    rw [ite_eq_right hcon, ite_eq_right hcon']
    simp only [mul_zero, tsum_zero]

end BayesNet

end Cslib.MachineLearning.GraphicalModels
