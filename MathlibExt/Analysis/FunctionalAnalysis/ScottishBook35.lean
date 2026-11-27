/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Homotopy.Lifting

/-!
# Projective Hilbert space and Scottish Book Problem 35

The antipodal quotient of the unit sphere in an infinite-dimensional real Hilbert space
is not homeomorphic to the Hilbert space itself.
-/

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

open Metric Set Topology
open scoped InnerProductSpace

private abbrev UnitSphere (E : Type) [NormedAddCommGroup E] := sphere (0 : E) 1

private def projectivize {E : Type} [NormedAddCommGroup E] (x : UnitSphere E) :
    ProjectiveHilbertSpace E :=
  Quot.mk _ x

private theorem real_unit_eq_one_or_neg_one (g : UnitSphere ℝ) :
    (g : ℝ) = 1 ∨ (g : ℝ) = -1 := by
  have hg : |(g : ℝ)| = 1 := mem_sphere_zero_iff_norm.mp g.property
  exact (abs_eq zero_le_one).mp hg

private theorem projectivize_eq_iff_orbit {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x y : UnitSphere E} :
    projectivize x = projectivize y ↔ x ∈ MulAction.orbit (UnitSphere ℝ) y := by
  have hrel : (fun a b : UnitSphere E => (a : E) = b ∨ (a : E) = -(b : E)) =
      (MulAction.orbitRel (UnitSphere ℝ) (UnitSphere E)).r := by
    funext a b
    apply propext
    change ((a : E) = b ∨ (a : E) = -(b : E)) ↔ a ∈ MulAction.orbit (UnitSphere ℝ) b
    constructor
    · rintro (h | h)
      · exact ⟨1, by simpa using (Subtype.ext h).symm⟩
      · refine ⟨-1, Subtype.ext ?_⟩
        change (-1 : ℝ) • (b : E) = (a : E)
        simpa using h.symm
    · rintro ⟨g, rfl⟩
      change (g : ℝ) • (b : E) = b ∨ (g : ℝ) • (b : E) = -(b : E)
      rcases real_unit_eq_one_or_neg_one g with hg | hg <;> simp [hg]
  change Quot.mk _ x = Quot.mk _ y ↔ _
  rw [Quot.eq, hrel]
  exact (MulAction.orbitRel (UnitSphere ℝ) (UnitSphere E)).iseqv.eqvGen_iff

/-- Open hemispheres are disjoint from their antipodal translates. -/
private theorem isQuotientCoveringMap_projectivize {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    IsQuotientCoveringMap (@projectivize E _) (UnitSphere ℝ) where
  toIsQuotientMap := isQuotientMap_quot_mk
  toContinuousConstSMul := inferInstance
  apply_eq_iff_mem_orbit := projectivize_eq_iff_orbit
  disjoint x := by
    let U : Set (UnitSphere E) := {y | 0 < ⟪(x : E), (y : E)⟫_ℝ}
    have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
    have hx : x ∈ U := by
      change 0 < ⟪(x : E), (x : E)⟫_ℝ
      rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp x.property]
      positivity
    refine ⟨U, hU.mem_nhds hx, ?_⟩
    rintro g ⟨_, ⟨y, hy, rfl⟩, hgy⟩
    rcases real_unit_eq_one_or_neg_one g with hg | hg
    · exact Subtype.ext hg
    · change 0 < ⟪(x : E), (g : ℝ) • (y : E)⟫_ℝ at hgy
      rw [hg, neg_one_smul, inner_neg_right] at hgy
      exact (not_lt_of_ge (neg_nonpos.mpr (le_of_lt hy)) hgy).elim

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
theorem projective_hilbert_space_not_homeomorphic_to_hilbert_space :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ¬ ProjectiveHilbertSpaceHomeomorphicToHilbertSpace E := by
  intro E _ _ _ hInfinite ⟨e⟩
  have hRank : 1 < Module.rank ℝ E :=
    Cardinal.one_lt_aleph0.trans_le
      (le_of_not_gt fun h => hInfinite (Module.rank_lt_aleph0_iff.mp h))
  have : PathConnectedSpace (UnitSphere E) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hRank 0 zero_le_one)
  have : SimplyConnectedSpace (ProjectiveHilbertSpace E) :=
    e.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨x⟩ := (inferInstance : Nonempty (UnitSphere E))
  let p := projectivize (E := E)
  let z : p ⁻¹' {p x} := ⟨x, rfl⟩
  have hsurj := isQuotientCoveringMap_projectivize.fundamentalGroupToMulOpposite_surjective z
  obtain ⟨a, ha⟩ := hsurj (MulOpposite.op (1 : UnitSphere ℝ))
  obtain ⟨b, hb⟩ := hsurj (MulOpposite.op (-1 : UnitSphere ℝ))
  rw [Subsingleton.elim a b, hb] at ha
  exact (neg_ne_self.mpr one_ne_zero) (congrArg (fun g => (g.unop : ℝ)) ha)

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook35Wanted
