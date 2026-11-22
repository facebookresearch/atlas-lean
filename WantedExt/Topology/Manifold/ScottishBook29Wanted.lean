/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Topology.Manifold.ScottishBook29Wanted

/-- The topology on a homeomorphism group: the topology induced by the
embedding `h ↦ (h, h⁻¹)` into continuous maps with the compact-open topology.
This is the usual topology on the homeomorphism group; Mathlib has no
`TopologicalSpace` instance on `Homeomorph`, so it is supplied here. -/
local instance homeomorphTopologicalSpace {X : Type*} [TopologicalSpace X] :
    TopologicalSpace (X ≃ₜ X) :=
  TopologicalSpace.induced (fun h : X ≃ₜ X => ((h : C(X, X)), (h.symm : C(X, X))))
    inferInstance

/--
**Normal subgroups of the identity component of the homeomorphism group of a sphere.** Let
$n \ne 4$ be a natural number and let $S^n$ be the unit sphere in $\mathbb{R}^{n+1}$. Give the
group $\mathrm{Homeo}(S^n)$ of homeomorphisms of $S^n$ the topology induced by the embedding
$h \mapsto (h, h^{-1})$ into pairs of continuous self-maps of $S^n$ with the compact-open
topology, and let $G_0$ be the connected component of the identity in $\mathrm{Homeo}(S^n)$.
If $N$ is a subgroup of $\mathrm{Homeo}(S^n)$ contained in $G_0$ such that $h k h^{-1} \in N$
for all $h \in G_0$ and $k \in N$, then either $N$ is the trivial subgroup or $G_0 \subseteq N$.
In other words, the only normal subgroups of $G_0$ are the trivial one and $G_0$ itself.

This is Ulam's Problem 29 of the Scottish Book, which asked the question for every $n$; the
case $n = 4$ is excluded here. The restriction $n \ne 4$ is the caveat attached to the sphere
case in the Encyclopedia of Mathematics; Epstein's theorem itself is stated for manifolds in
general.

Source: S. Ulam, Problem 29 of the Scottish Book; D. B. A. Epstein,
The simplicity of certain groups of homeomorphisms, Compositio Mathematica
22 (1970), 165-173; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted identity_component_of_sphere_homeomorphism_group_simple :
    ∀ (n : ℕ), n ≠ 4 →
      ∀ (N : Subgroup (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃ₜ
        ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))),
      (∀ h ∈ N, h ∈ connectedComponent 1) →
      (∀ h ∈ connectedComponent 1, ∀ k ∈ N, h * k * h⁻¹ ∈ N) →
      N = ⊥ ∨ ∀ h, h ∈ connectedComponent 1 → h ∈ N

end MathlibExt.Topology.Manifold.ScottishBook29Wanted
