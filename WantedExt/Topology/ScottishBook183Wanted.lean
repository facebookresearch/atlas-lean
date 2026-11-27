/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace MathlibExt.Topology.ScottishBook183Wanted

/-- **Bogolyubov's linearization claim (Scottish Book Problem 183).** The claim that for every
$n \in \mathbb{N}$ and every compact, connected, locally connected topological group $G$ acting
on $\mathbb{R}^n$ with continuous action map $G \times \mathbb{R}^n \to \mathbb{R}^n$, there is a
homeomorphism $\varphi$ of $\mathbb{R}^n$ such that for every $g \in G$ there is a linear map
$L_g \colon \mathbb{R}^n \to \mathbb{R}^n$ with $\varphi(g \cdot x) = L_g(\varphi(x))$ for all
$x \in \mathbb{R}^n$.

This is Bogolyubov's problem in its original form: coordinates can be introduced in which every
transformation of the group is linear. -/
def ScottishBookProblem183Claim : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [CompactSpace G] [ConnectedSpace G] [LocallyConnectedSpace G]
    [IsTopologicalGroup G]
    [MulAction G (Fin n → ℝ)] [ContinuousSMul G (Fin n → ℝ)],
    ∃ φ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ), ∀ g : G,
      ∃ L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), ∀ x, φ (g • x) = L (φ x)

/--
**Bogolyubov's Problem 183 has a negative answer.** Bogolyubov's linearization claim is false:
there are $n \in \mathbb{N}$ and a compact, connected, locally connected topological group $G$
acting continuously on $\mathbb{R}^n$ such that for no homeomorphism $\varphi$ of $\mathbb{R}^n$
is every map $\varphi \circ g \circ \varphi^{-1}$, for $g \in G$, linear.

Source: N. N. Bogolyubov,
Problem 183 of the Scottish Book; see the commentary in R. D. Mauldin
(ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted bogolyubov183_refuted : ¬ ScottishBookProblem183Claim

end MathlibExt.Topology.ScottishBook183Wanted
