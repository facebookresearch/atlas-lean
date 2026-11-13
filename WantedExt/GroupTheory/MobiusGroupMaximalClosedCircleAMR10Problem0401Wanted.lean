/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PSL(2, ℝ) is a maximal closed subgroup of Homeo₊(S¹) (Bestvina, Q 4.1)

M. Bestvina, Questions in Geometric Group Theory, Q 4.1 (de la Harpe): is `PSL₂(ℝ)` a maximal closed
subgroup of `Homeo₊(S¹)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Circle

@[expose] public section

namespace MathlibExt.GroupTheory.MobiusGroupMaximalClosedCircleAMR10Problem0401Wanted

/-!
Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 4.1 (de la Harpe),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf. UnsolvedMath record UM-01100401
(`AMR-010-0401`), dataset ulamai/UnsolvedMath v1.8.0.

`S¹` is `Circle`. A homeomorphism preserves orientation when it lifts through `t ↦ exp(i t)` to a
strictly increasing map of `ℝ`. `PSL₂(ℝ)` acts on the circle by Möbius maps; conjugating by the
Cayley transform, these are `z ↦ (α z + β)/(β̄ z + ᾱ)` with `|α|² - |β|² = 1`. `Homeo₊(S¹)` carries
the uniform topology (as in Giblin–Markovic); this topology is metrizable, so closedness of a
subgroup `G ≤ Homeo₊(S¹)` is stated with uniformly convergent sequences. Maximality: every closed
`G` with `PSL₂(ℝ) ≤ G ≤ Homeo₊(S¹)` is one of the two. In the full group `Homeo(S¹)` the Möbius
group is not maximal (`PGL₂(ℝ)` lies between), so the orientation-preserving setting matters.
-/

/-- `f` preserves orientation: it lifts through `t ↦ exp(i t)` to a strictly increasing map of
`ℝ`. -/
def IsOrientationPreserving (f : Circle ≃ₜ Circle) : Prop :=
  ∃ F : ℝ → ℝ, StrictMono F ∧ ∀ t : ℝ, f (Circle.exp t) = Circle.exp (F t)

/-- `f` is a Möbius transformation of the circle, `z ↦ (α z + β) / (β̄ z + ᾱ)` with
`|α|² - |β|² = 1`: the action of `PSL(2, ℝ)`, conjugated by the Cayley transform to the unit
circle. -/
def IsMobius (f : Circle ≃ₜ Circle) : Prop :=
  ∃ α β : ℂ, ‖α‖ ^ 2 - ‖β‖ ^ 2 = 1 ∧
    ∀ z : Circle, (f z : ℂ) = (α * z + β) / (star β * z + star α)

/-- `G` is closed in `Homeo₊(S¹)` with the uniform topology: every orientation-preserving
homeomorphism that is a uniform limit of elements of `G` lies in `G`. -/
def IsUniformlyClosed (G : Subgroup (Circle ≃ₜ Circle)) : Prop :=
  ∀ (f : ℕ → Circle ≃ₜ Circle) (g : Circle ≃ₜ Circle), (∀ k, f k ∈ G) → IsOrientationPreserving g →
    TendstoUniformly (fun k => ⇑(f k)) ⇑g Filter.atTop → g ∈ G

/-- de la Harpe's question (Bestvina Q 4.1), answered: `PSL(2, ℝ)` is a maximal closed subgroup of
`Homeo₊(S¹)`: a closed subgroup of `Homeo₊(S¹)` containing the Möbius group is the Möbius group
or all of `Homeo₊(S¹)`. -/
def mobiusMaximalClosed : Prop :=
  ∀ G : Subgroup (Circle ≃ₜ Circle), (∀ g ∈ G, IsOrientationPreserving g) → IsUniformlyClosed G →
    (∀ g, IsMobius g → g ∈ G) →
      (∀ g ∈ G, IsMobius g) ∨ ∀ g, IsOrientationPreserving g → g ∈ G

/--
Resolved true: Giblin and Markovic classified the closed transitive subgroups of `Homeo₊(S¹)` that
contain a non-constant continuous path and deduced that `PSL(2, ℝ)` is a maximal closed subgroup of
the group of orientation-preserving circle homeomorphisms (uniform topology), confirming de la
Harpe's conjecture. Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q
4.1 (de la Harpe), https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf; resolution: J.
Giblin and V. Markovic, Classification of continuously transitive circle groups, Geom. Topol. 10
(2006), 1319-1346, arXiv:0903.0180, Theorem 1.3: "PSL(2, ℝ) is a maximal closed subgroup of
Homeo(S¹)", where Homeo(S¹) denotes the group of orientation preserving homeomorphisms with the
uniform topology (Section 1), https://arxiv.org/abs/0903.0180.
-/
public theorem_wanted mobiusMaximalClosed_holds : mobiusMaximalClosed

end MathlibExt.GroupTheory.MobiusGroupMaximalClosedCircleAMR10Problem0401Wanted
