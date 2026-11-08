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

/-- The projective Hilbert space of `E`: diameters (lines through the origin)
of the unit sphere, identified with antipodal pairs of unit vectors, with the
quotient topology. -/
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

/-- The claim of Problem 35, that projective Hilbert space is homeomorphic to
Hilbert space itself. -/
def ProjectiveHilbertSpaceHomeomorphicToHilbertSpace (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Prop :=
  Nonempty (ProjectiveHilbertSpace E ≃ₜ E)

/--
Ulam, Problem 35 of the Scottish Book. Original question: is the projective
Hilbert space, the collection of all diameters of the unit sphere in Hilbert
space equipped with the Hausdorff metric, homeomorphic to Hilbert space
itself? The answer is no: Hilbert space is contractible, hence simply
connected, while projective Hilbert space is not, its fundamental group
being `Z / 2` via the double covering by the unit sphere. The projective
space here is the quotient of the unit sphere by the antipodal identification,
the standard model of the space of diameters.
Source: S. Ulam, Problem 35 of the Scottish Book; see the commentary of
Holsztynski in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser,
2015), and the Hilbert-manifold classification by homotopy type.
-/
theorem_wanted projective_hilbert_space_not_homeomorphic_to_hilbert_space :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ¬ ProjectiveHilbertSpaceHomeomorphicToHilbertSpace E

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook35Wanted
