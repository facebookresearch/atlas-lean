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

/-- The closed square `I² = [0, 1] × [0, 1]`, a model of the closed disc. -/
abbrev Square : Type := unitInterval × unitInterval

/-- The boundary of the square `I²`. -/
def squareBoundary : Set Square := {x | x.1 = 0 ∨ x.1 = 1 ∨ x.2 = 0 ∨ x.2 = 1}

/-- `Homeo(I²; ∂I²)`: the homeomorphisms of the square that fix its boundary pointwise. -/
def boundaryFixingHomeomorphisms : Subgroup (Square ≃ₜ Square) :=
  fixingSubgroup (Square ≃ₜ Square) squareBoundary

/-- The right orders of `G`: linear orders (as relations) invariant under right multiplication. -/
def rightOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (a * c) (b * c)}

/-- Kourovka 17.20 (G. M. Bergman) for the closed disc: the group of homeomorphisms of the disc
(the square `I²`) fixing the boundary pointwise is right-orderable. -/
def discBoundaryFixingHomeomorphismsRightOrderable : Prop :=
  (rightOrders boundaryFixingHomeomorphisms).Nonempty

/--
Resolved false: Hyde constructs a finitely generated subgroup of `Homeo(I²; ∂I²)`, the
homeomorphisms of the square fixing its boundary pointwise, that admits no left order; so `Homeo(I²;
∂I²)` is not left-orderable, equivalently not right-orderable. The Kourovka Archive answers 17.20
"No, not always". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
17.20 (G. M. Bergman); resolution: J. Hyde, The group of boundary fixing homeomorphisms of the disc
is not left-orderable, Ann. of Math. (2) 190 (2019), 657-661, abstract (a finitely generated
subgroup of Homeo(I²; ∂I²) admits no left order, hence neither does Homeo(I²; ∂I²)); Kourovka
Archive, Problem 17.20 (No, not always), https://annals.math.princeton.edu/2019/190-2/p05.
-/
public theorem_wanted discBoundaryFixingHomeomorphismsRightOrderable_refuted :
    ¬ discBoundaryFixingHomeomorphismsRightOrderable

end MathlibExt.GroupTheory.BoundaryFixingHomeomorphismsOrderableKourovka17Problem20Wanted
