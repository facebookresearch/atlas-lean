/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Orderability of boundary-fixing homeomorphisms of the disc (Kourovka Notebook Problem 17.20)

Kourovka Notebook, Archive of Solved Problems, Problem 17.20 (G. M. Bergman): if `M` is a real
manifold with nonempty boundary, and `G` the group of self-homeomorphisms of `M` which fix the
boundary pointwise, is `G` right-orderable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Topology.UnitInterval

@[expose] public section

namespace MathlibExt.GroupTheory.BoundaryFixingHomeomorphismsOrderableKourovka17Problem20Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.20 (G. M.
Bergman). UnsolvedMath record UM-00701322 (`KOU-17.20`), dataset ulamai/UnsolvedMath v1.8.0.

The resolution is a counterexample on the closed disc, modelled as the square `I² = [0, 1]²` with
its boundary, as in the source; the target is that this group, `fixingSubgroup` of the boundary in
`I² ≃ₜ I²`, has a right order (a linear order invariant under right multiplication). Its refutation
answers the general question negatively. Left- and right-orderability are equivalent (`g ↦ g⁻¹`).
-/

/-- **The closed square.** The closed square $I^2 = [0, 1] \times [0, 1]$, the product of two
copies of the unit interval, used as a model of the closed disc. -/
abbrev Square : Type := unitInterval × unitInterval

/-- **Boundary of the square.** The boundary $\partial I^2$ of the closed square
$I^2 = [0, 1] \times [0, 1]$ is the set of points $(x, y) \in I^2$ with $x = 0$, $x = 1$, $y = 0$
or $y = 1$. -/
def squareBoundary : Set Square := {x | x.1 = 0 ∨ x.1 = 1 ∨ x.2 = 0 ∨ x.2 = 1}

/-- **Boundary-fixing homeomorphisms of the square.** Let $I^2 = [0, 1] \times [0, 1]$ be the
closed square and $\partial I^2$ its boundary. $\mathrm{Homeo}(I^2; \partial I^2)$ is the subgroup
of the group of homeomorphisms of $I^2$ consisting of those homeomorphisms $h$ with $h(x) = x$ for
every $x \in \partial I^2$. -/
def boundaryFixingHomeomorphisms : Subgroup (Square ≃ₜ Square) :=
  fixingSubgroup (Square ≃ₜ Square) squareBoundary

/-- The right orders of `G`: linear orders (as relations) invariant under right multiplication. -/
def rightOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (a * c) (b * c)}

/-- **Right-orderability of the boundary-fixing homeomorphisms of the disc.** The proposition
(Kourovka Problem 17.20, G. M. Bergman, for the closed disc) that the group
$\mathrm{Homeo}(I^2; \partial I^2)$ of homeomorphisms of the closed square
$I^2 = [0, 1] \times [0, 1]$, a model of the closed disc, that fix the boundary $\partial I^2$
pointwise is right-orderable: it carries a linear order $\le$ such that $a \le b$ implies
$ac \le bc$ for all $a, b, c$. -/
def discBoundaryFixingHomeomorphismsRightOrderable : Prop :=
  (rightOrders boundaryFixingHomeomorphisms).Nonempty

/--
**Boundary-fixing homeomorphisms of the disc are not right-orderable.** Let
$I^2 = [0, 1] \times [0, 1]$ be the closed square, a model of the closed disc, and let
$\mathrm{Homeo}(I^2; \partial I^2)$ be the group of homeomorphisms of $I^2$ that fix every point of
the boundary $\partial I^2$. There is no linear order $\le$ on $\mathrm{Homeo}(I^2; \partial I^2)$
such that $a \le b$ implies $ac \le bc$ for all $a, b, c$; that is, this group is not
right-orderable.

This answers Kourovka Problem 17.20 negatively: Hyde constructs a finitely generated subgroup of
$\mathrm{Homeo}(I^2; \partial I^2)$ that admits no left order, and left- and right-orderability
are equivalent via $g \mapsto g^{-1}$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
17.20 (G. M. Bergman); resolution: J. Hyde, The group of boundary fixing homeomorphisms of the disc
is not left-orderable, Ann. of Math. (2) 190 (2019), 657-661, abstract (a finitely generated
subgroup of Homeo(I²; ∂I²) admits no left order, hence neither does Homeo(I²; ∂I²)); Kourovka
Archive, Problem 17.20 (No, not always), https://annals.math.princeton.edu/2019/190-2/p05.
-/
public theorem_wanted discBoundaryFixingHomeomorphismsRightOrderable_refuted :
    ¬ discBoundaryFixingHomeomorphismsRightOrderable

end MathlibExt.GroupTheory.BoundaryFixingHomeomorphismsOrderableKourovka17Problem20Wanted
