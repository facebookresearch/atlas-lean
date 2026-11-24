/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook35Wanted

/-- **Projective Hilbert space.** Let $E$ be a normed additive commutative group, in practice a
real inner product space. The projective Hilbert space of $E$ is the quotient of the unit sphere
$\{x \in E : \|x\| = 1\}$ by the relation identifying each $x$ with $-x$. Its points are the
antipodal pairs $\{x, -x\}$ of unit vectors, that is, the diameters of the unit sphere.

When $E$ is a real inner product space, it carries the quotient topology of the unit sphere. -/
def ProjectiveHilbertSpace (E : Type) [NormedAddCommGroup E] : Type :=
  Quot (fun x y : ↥(Metric.sphere (0 : E) 1) => (x : E) = y ∨ (x : E) = -(y : E))

/-- Quotient topology on projective Hilbert space. Mathlib's `Quot`
topology instance does not fire through the `ProjectiveHilbertSpace`
definition, so it is supplied here. -/
-- The `[InnerProductSpace ℝ E]` binder is scope, not structure: the
-- quotient topology does not need it, but removing it would leave the
-- `InnerProductSpace` binders of `ProjectiveHilbertSpaceHomeomorphicToHilbertSpace`
-- and the `theorem_wanted` below unused, and dropping those would change the
-- filed claim from Hilbert spaces to all normed spaces.
@[nolint unusedArguments]
instance (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    TopologicalSpace (ProjectiveHilbertSpace E) := by
  unfold ProjectiveHilbertSpace
  infer_instance

/-- **Projective Hilbert space homeomorphic to the space itself.** For a real inner product
space $E$, the statement that the projective Hilbert space of $E$, the unit sphere
$\{x \in E : \|x\| = 1\}$ with each $x$ identified with $-x$ and given the quotient topology,
is homeomorphic to $E$. -/
def ProjectiveHilbertSpaceHomeomorphicToHilbertSpace (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Prop :=
  Nonempty (ProjectiveHilbertSpace E ≃ₜ E)

/--
**Projective Hilbert space is not homeomorphic to Hilbert space.** Let $E$ be an
infinite-dimensional real Hilbert space. Then the projective Hilbert space of $E$, the unit
sphere $\{x \in E : \|x\| = 1\}$ with each $x$ identified with $-x$ and given the quotient
topology, is not homeomorphic to $E$.

This answers Ulam's Problem 35 of the Scottish Book in the negative. The projective space is the
standard model of the space of diameters of the unit sphere with the Hausdorff metric. Hilbert
space is contractible, hence simply connected, while projective Hilbert space is not, its
fundamental group being $\mathbb{Z}/2$ via the double covering by the unit sphere.

Source: S. Ulam, Problem 35 of the Scottish Book; see the commentary of
Holsztynski in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser,
2015), and the Hilbert-manifold classification by homotopy type.
-/
theorem_wanted projective_hilbert_space_not_homeomorphic_to_hilbert_space :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ¬ ProjectiveHilbertSpaceHomeomorphicToHilbertSpace E

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook35Wanted
