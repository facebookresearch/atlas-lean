/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Cocycle representatives of group-cohomology maps in degrees one and two

Let k be a commutative ring, f:G→H a homomorphism of groups in universe u, A a k-linear
H-representation, and φ:Res_f A→B a coefficient morphism to a G-representation. The induced
cohomology map is contravariant in the group and covariant in the coefficient map:
H^n(H,A)→H^n(G,B).

For a one-cocycle z, the image of [z] is represented by g↦φ(z(f(g))). For a two-cocycle z, it is
represented by (g,h)↦φ(z(f(g),f(h))). The representative formulas commute with the respective
class projections.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A : Rep k H} {B : Rep k G}

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G,H groups in the given universe u, A a k-linear H-representation,
and B a k-linear G-representation. Let f:G→H be a homomorphism and φ:Res_f A→B an equivariant
k-linear coefficient map. For z∈Z¹(H,A), the induced map H¹(H,A)→H¹(G,B) sends [z] to [z'],
where z'(g)=φ(z(f(g))). Equivalently map_{f,φ}(π₁z)=π₁(mapCocycles_{f,φ}z). -/
theorem map_H1π
    (f : G →* H) (phi : Rep.res f A ⟶ B) (z : cocycles₁ A) :
    map f phi 1 (H1π A z) = H1π B (mapCocycles₁ f phi z) := by
  rw [← ConcreteCategory.comp_apply, H1π_comp_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G,H groups in the given universe u, A a k-linear H-representation,
and B a k-linear G-representation. Let f:G→H be a homomorphism and φ:Res_f A→B an equivariant
k-linear coefficient map. For z∈Z²(H,A), the induced map H²(H,A)→H²(G,B) sends [z] to [z'],
where z'(g,h)=φ(z(f(g),f(h))). Thus map_{f,φ}(π₂z)=π₂(mapCocycles_{f,φ}z). -/
theorem map_H2π
    (f : G →* H) (phi : Rep.res f A ⟶ B) (z : cocycles₂ A) :
    map f phi 2 (H2π A z) = H2π B (mapCocycles₂ f phi z) := by
  rw [← ConcreteCategory.comp_apply, H2π_comp_map]
  rfl

end groupCohomology
