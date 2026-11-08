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
Ulam, Problem 29 of the Scottish Book. Original question: is the group `H_n`
of all homeomorphisms of the surface of an `n`-dimensional sphere simple, in
the sense that the component of the identity contains no nontrivial normal
subgroup? The answer is affirmative: Epstein proved that the identity
component of the homeomorphism group of a manifold is simple. Formalized
here as: a subgroup of `H_n` that lies in the identity component and is
normal in the identity component (not merely normal in the full
homeomorphism group) is either trivial or contains the whole identity
component. Normality is in the identity component, per Epstein's theorem.
The statement is
guarded by `n ≠ 4`, the caveat attached to the sphere case in the
Encyclopedia of Mathematics; Epstein's theorem itself is stated for manifolds
in general. The cases `n = 2` (Schreier-Ulam) and `n ≠ 4` are covered.
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
