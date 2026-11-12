/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalAdjustment

/-!
# Identifiability of causal quantities

A functional `Q` on a class `C` of models is *identified* from an observation map `obs` (for
causal models: the observational law) if two models of the class with the same observations
have the same value of `Q` (Pearl 2009, Definition 3.2.3). The back-door and front-door
adjustment formulas express `P(X_y = v | do(X_k = a))` through the observational joint law
alone, so on the classes of causal Bayesian networks that satisfy the respective criteria and
positivity hypotheses, this interventional probability is identified.

## Main definitions

* `IdentifiedOn C obs Q`: identification of `Q` from `obs` on the class `C`.
* `BayesNet.BackdoorCriterion`, `BayesNet.FrontdoorCriterion`: the graph hypotheses of
  `BayesNet.backdoor_adjustment` and `BayesNet.frontdoor_adjustment`.
* `BayesNet.backdoorClass pa k y Z a`, `BayesNet.frontdoorClass pa k y M`: the networks with the
  fixed graph `pa` satisfying the criterion and the positivity hypothesis of the formula.

## Main results

* `IdentifiedOn.of_eq_comp`, `IdentifiedOn.exists_eq_comp`: `Q` is identified on `C` if and
  only if it is a function of the observations on `C`.
* `BayesNet.identifiedOn_backdoorClass`, `BayesNet.identifiedOn_frontdoorClass`: back-door and
  front-door identification of `P(X_y = v | do(X_k = a))` from the joint law.

The proofs apply the adjustment theorems; the fixed-graph condition `b.pa = pa` is part of the
classes, as in the source, but is not needed for the identification argument.

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §3.2–3.3.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset

/-- A functional `Q` on a class `C` of models is **identified** from the observation map `obs`
(for causal models: the observational law) if any two models of the class with the same
observations have the same value of `Q`. -/
def IdentifiedOn {M O R : Type*} (C : Set M) (obs : M → O) (Q : M → R) : Prop :=
  ∀ m ∈ C, ∀ m' ∈ C, obs m = obs m' → Q m = Q m'

/-- A functional that is a function of the observations on the class is identified. -/
theorem IdentifiedOn.of_eq_comp {M O R : Type*} {C : Set M} {obs : M → O} {Q : M → R}
    (F : O → R) (h : ∀ m ∈ C, Q m = F (obs m)) : IdentifiedOn C obs Q := by
  intro m hm m' hm' hobs
  rw [h m hm, h m' hm', hobs]

/-- Conversely, an identified functional is a function of the observations on the class: some
`F` has `Q m = F (obs m)` for every `m ∈ C` (the form used for non-identification witnesses). -/
theorem IdentifiedOn.exists_eq_comp {M O R : Type*} [Nonempty R] {C : Set M} {obs : M → O}
    {Q : M → R} (h : IdentifiedOn C obs Q) : ∃ F : O → R, ∀ m ∈ C, Q m = F (obs m) := by
  classical
  refine ⟨fun o => if h' : ∃ m ∈ C, obs m = o then Q h'.choose else Classical.arbitrary R, ?_⟩
  intro m hm
  have hex : ∃ m' ∈ C, obs m' = obs m := ⟨m, hm, rfl⟩
  have hspec := Classical.choose_spec hex
  simp only [dite_eq_left hex]
  exact (h _ hspec.1 _ hm hspec.2).symm

namespace BayesNet

/-- The **back-door criterion** for the effect of node `k` on node `y` with adjustment set `Z`,
in the graph of `b`: no node of `Z` is a descendant of `k`, and `Z` blocks every path from `k`
to `y` that begins with an arrow into `k` (the graph hypotheses of
`BayesNet.backdoor_adjustment`). -/
def BackdoorCriterion {α : Type*} {n : ℕ} (b : BayesNet α n) (k y : Fin n)
    (Z : Finset (Fin n)) : Prop :=
  (∀ z ∈ Z, ¬b.IsDescendant k z) ∧
    ∀ p, b.IsPath k y p → (∃ h : 1 < p.length, b.Edge p[1] k) → b.PathBlocked (Z : Set (Fin n)) p

/-- The class of causal Bayesian networks with the fixed graph `pa` that satisfy the back-door
criterion for `(k, y, Z)` and the positivity hypothesis of `BayesNet.backdoor_adjustment` for
the treatment value `a`: `P(X_k = a, Z = z) > 0` whenever `P(Z = z) > 0`. -/
def backdoorClass {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (pa : (k : Fin n) → Finset (Fin k)) (k y : Fin n) (Z : Finset (Fin n)) (a : α) :
    Set (BayesNet α n) :=
  {b | b.pa = pa ∧ b.BackdoorCriterion k y Z ∧
    ∀ z : Z → α, ∑ x with (fun i : Z => x i) = z, b.joint x ≠ 0 →
      ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x ≠ 0}

/-- The **front-door criterion** for the effect of node `k` on node `y` with mediator set `M`,
in the graph of `b` (the graph hypotheses of `BayesNet.frontdoor_adjustment`): `M` intercepts
every directed path from `k` to `y`, every path from `k` to a node of `M` beginning with an arrow
into `k` is blocked by `∅`, and every path from a node of `M` to `y` beginning with an arrow
into that node is blocked by `{k}`. -/
def FrontdoorCriterion {α : Type*} {n : ℕ} (b : BayesNet α n) (k y : Fin n)
    (M : Finset (Fin n)) : Prop :=
  (∀ p : List (Fin n), p.IsChain b.Edge → p.head? = some k → p.getLast? = some y →
      ∃ m ∈ M, m ∈ p) ∧
    (∀ m ∈ M, ∀ p, b.IsPath k m p → (∃ h : 1 < p.length, b.Edge p[1] k) → b.PathBlocked ∅ p) ∧
    ∀ m ∈ M, ∀ p, b.IsPath m y p → (∃ h : 1 < p.length, b.Edge p[1] m) → b.PathBlocked {k} p

/-- The class of causal Bayesian networks with the fixed graph `pa` that satisfy the front-door
criterion for `(k, y, M)` and the positivity hypothesis of `BayesNet.frontdoor_adjustment`:
`P(X_k = a', M = m) > 0` for all `a'` and `m`. -/
def frontdoorClass {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (pa : (k : Fin n) → Finset (Fin k)) (k y : Fin n) (M : Finset (Fin n)) :
    Set (BayesNet α n) :=
  {b | b.pa = pa ∧ b.FrontdoorCriterion k y M ∧
    ∀ (a' : α) (m : M → α), ∑ x with x k = a' ∧ (fun i : M => x i) = m, b.joint x ≠ 0}

/-- **Back-door identification**: on the class of networks with a fixed graph satisfying the
back-door criterion and positivity, the interventional probability `P(X_y = v | do(X_k = a))`
is identified from the observational joint law. -/
theorem identifiedOn_backdoorClass {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (pa : (k : Fin n) → Finset (Fin k)) (k y : Fin n) (Z : Finset (Fin n)) (a v : α)
    (hky : k ≠ y) (hyZ : y ∉ Z) :
    IdentifiedOn (backdoorClass pa k y Z a) (fun b : BayesNet α n => b.joint)
      (fun b => ∑ x with x y = v, (b.intervene k a).joint x) := by
  refine IdentifiedOn.of_eq_comp
    (fun P : (Fin n → α) → ℝ =>
      ∑ z : Z → α, (∑ x with (fun i : Z => x i) = z, P x) *
        ((∑ x with x k = a ∧ x y = v ∧ (fun i : Z => x i) = z, P x) /
          ∑ x with x k = a ∧ (fun i : Z => x i) = z, P x)) ?_
  intro b hb
  obtain ⟨-, hcrit, hpos⟩ := hb
  exact BayesNet.backdoor_adjustment b k y Z a v hky hyZ hcrit.1 hcrit.2 hpos

/-- **Front-door identification**: on the class of networks with a fixed graph satisfying the
front-door criterion and positivity, `P(X_y = v | do(X_k = a))` is identified from the
observational joint law. -/
theorem identifiedOn_frontdoorClass {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (pa : (k : Fin n) → Finset (Fin k)) (k y : Fin n) (M : Finset (Fin n)) (a v : α)
    (hky : k ≠ y) (hkM : k ∉ M) (hyM : y ∉ M) :
    IdentifiedOn (frontdoorClass pa k y M) (fun b : BayesNet α n => b.joint)
      (fun b => ∑ x with x y = v, (b.intervene k a).joint x) := by
  refine IdentifiedOn.of_eq_comp
    (fun P : (Fin n → α) → ℝ =>
      ∑ m : M → α,
        ((∑ x with x k = a ∧ (fun i : M => x i) = m, P x) /
            ∑ x with x k = a, P x) *
          ∑ a' : α,
            ((∑ x with x k = a' ∧ x y = v ∧ (fun i : M => x i) = m, P x) /
                ∑ x with x k = a' ∧ (fun i : M => x i) = m, P x) *
              ∑ x with x k = a', P x) ?_
  intro b hb
  obtain ⟨-, hcrit, hpos⟩ := hb
  obtain ⟨hdir, hkm, hmy⟩ := hcrit
  exact BayesNet.frontdoor_adjustment b k y M a v hky hkM hyM hdir hkm hmy hpos

end BayesNet

end Cslib.MachineLearning.GraphicalModels
