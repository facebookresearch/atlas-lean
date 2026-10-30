/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Graphical causal identification: wanted results

Statements about causal Bayesian networks (`CSLibExt/MachineLearning/GraphicalModels/`), with
the do-operator `BayesNet.intervene`, d-separation `BayesNet.DSeparated` and conditional
independence of sets of variables `CondIndep` from `CausalBayesNet.lean`.

* `condIndep_of_dSeparated`: the global Markov property, d-separation implies conditional
  independence in every law that factorizes along the graph (Geiger, Verma & Pearl 1990;
  Lauritzen, Dawid, Larsen & Leimer 1990).
* `backdoor_adjustment`: the back-door adjustment (Pearl 1995; Pearl 2009,
  Theorem 3.3.2). The case where `Z` is the set of parents of the treatment is proved
  (`BayesNet.sum_intervene_joint_mul`).
* `frontdoor_adjustment`: the front-door adjustment (Pearl 1995; Pearl 2009,
  Theorem 3.3.4).

Not stated: the three rules of the do-calculus (Pearl 1995; Pearl 2009,
Theorem 3.4.1), which need interventions on sets of nodes and the mutilated graphs
`G_{\bar X}`, `G_{\underline Z}`; `BayesNet.intervene` intervenes on one node.

References: D. Geiger, T. Verma and J. Pearl, *Identifying independence in Bayesian networks*,
Networks 20(5) (1990), 507–534; S. L. Lauritzen, A. P. Dawid, B. N. Larsen and H.-G. Leimer,
*Independence properties of directed Markov fields*, Networks 20(5) (1990), 491–505;
J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–688;
J. Pearl, *Causality*, 2nd ed., Cambridge University Press (2009).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet

@[expose] public section

namespace MathlibExt.Probability.CausalGraphicalWanted

open Finset Cslib.MachineLearning.GraphicalModels

/-- **The global Markov property** (soundness of d-separation: Geiger, Verma & Pearl
1990; Lauritzen, Dawid, Larsen & Leimer 1990): if `Z` d-separates `X` from `Y` in the graph of a
Bayesian network, then `X` and `Y` are conditionally independent given `Z` under its joint
law. -/
theorem_wanted condIndep_of_dSeparated {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (b : BayesNet α n) (X Y Z : Finset (Fin n)) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : b.DSeparated (X : Set (Fin n)) (Y : Set (Fin n)) (Z : Set (Fin n))) :
    CondIndep b.joint X Y Z

/-- **The back-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.2): if the
set `Z` contains no descendant of the treatment node `k` and blocks every path between `k` and
the outcome node `y` that begins with an arrow into `k`, then
`P(X_y = v | do(X_k = a)) = ∑_z P(Z = z) P(X_y = v | X_k = a, Z = z)`, assuming
`P(X_k = a, Z = z) > 0` whenever `P(Z = z) > 0`. -/
theorem_wanted backdoor_adjustment {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (b : BayesNet α n) (k y : Fin n) (Z : Finset (Fin n)) (a v : α) (hky : k ≠ y)
    (hkZ : k ∉ Z) (hyZ : y ∉ Z) (hdesc : ∀ z ∈ Z, ¬b.IsDescendant k z)
    (hblock : ∀ p, b.IsPath k y p → (∃ h : 1 < p.length, b.Edge p[1] k) →
      b.PathBlocked (Z : Set (Fin n)) p)
    (hpos : ∀ z : Z → α, ∑ x with (fun i : Z => x i) = z, b.joint x ≠ 0 →
      ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x ≠ 0) :
    ∑ x with x y = v, (b.intervene k a).joint x =
      ∑ z : Z → α, (∑ x with (fun i : Z => x i) = z, b.joint x) *
        ((∑ x with x k = a ∧ x y = v ∧ (fun i : Z => x i) = z, b.joint x) /
          ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x)

/-- **The front-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.4): if the
set `M` intercepts every directed path from the treatment node `k` to the outcome node `y`, no
path from `k` to a node of `M` that begins with an arrow into `k` is open (blocked by `∅`), and
every path from a node of `M` to `y` that begins with an arrow into that node is blocked by
`{k}`, then
`P(X_y = v | do(X_k = a)) = ∑_m P(M = m | X_k = a) ∑_{a'} P(X_y = v | X_k = a', M = m) P(X_k = a')`,
assuming `P(X_k = a', M = m) > 0` for all `a'` and `m`. -/
theorem_wanted frontdoor_adjustment {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (b : BayesNet α n) (k y : Fin n) (M : Finset (Fin n)) (a v : α) (hky : k ≠ y)
    (hkM : k ∉ M) (hyM : y ∉ M)
    (hdir : ∀ p : List (Fin n), p.IsChain b.Edge → p.head? = some k → p.getLast? = some y →
      ∃ m ∈ M, m ∈ p)
    (hkm : ∀ m ∈ M, ∀ p, b.IsPath k m p → (∃ h : 1 < p.length, b.Edge p[1] k) →
      b.PathBlocked ∅ p)
    (hmy : ∀ m ∈ M, ∀ p, b.IsPath m y p → (∃ h : 1 < p.length, b.Edge p[1] m) →
      b.PathBlocked {k} p)
    (hpos : ∀ (a' : α) (m : M → α), ∑ x with x k = a' ∧ (fun i : M => x i) = m, b.joint x ≠ 0) :
    ∑ x with x y = v, (b.intervene k a).joint x =
      ∑ m : M → α,
        ((∑ x with x k = a ∧ (fun i : M => x i) = m, b.joint x) /
            ∑ x with x k = a, b.joint x) *
          ∑ a' : α,
            ((∑ x with x k = a' ∧ x y = v ∧ (fun i : M => x i) = m, b.joint x) /
                ∑ x with x k = a' ∧ (fun i : M => x i) = m, b.joint x) *
              ∑ x with x k = a', b.joint x

end MathlibExt.Probability.CausalGraphicalWanted
