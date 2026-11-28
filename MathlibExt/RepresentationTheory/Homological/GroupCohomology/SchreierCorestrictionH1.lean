/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferIndependence

/-!
# Canonical corestriction in degree one

Let k be a commutative ring, G a group, H≤G a finite-index subgroup, and A a k-linear
G-representation in universe u. Degree-one corestriction is the k-linear map H¹(H,Res_H
A)→H¹(G,A) obtained from the finite right-transversal transfer; its value on cohomology is
independent of the transversal.

For a right transversal T, decompose t g=h_T(t,g) r_T(t,g), with h_T(t,g)∈H and r_T(t,g)∈T. The
transfer of a subgroup one-cocycle f is Tr_T(f)(g)=Σ_{t∈T}ρ(t⁻¹)f(h_T(t,g)). Canonical
corestriction sends [f] to [Tr_T(f)] for every such T.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Let k be a commutative ring, G a group, H≤G a finite-index subgroup, and A a k-linear
G-representation, in the given universe u. There is a k-linear map cor_H^G:H¹(H,Res_H
A)→H¹(G,A), independent of the right transversal used to construct it. For a right transversal
T, write t g=h_T(t,g) r_T(t,g), with h_T(t,g)∈H and r_T(t,g)∈T. The transferred one-cochain is
Tr_T(f)(g)=Σ_{t∈T}ρ(t⁻¹)f(h_T(t,g)). It sends the class of a subgroup one-cocycle f to the class
of Tr_T(f). -/
noncomputable def corestrictionH1 (A : Rep k G) [H.FiniteIndex] :
    groupCohomology.H1 (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H1 A :=
  corestrictionH1OfRightTransversal A
    (default : H.RightTransversal)

/-- Let k be a commutative ring, G a group, H≤G a finite-index subgroup, and A a k-linear
G-representation, in the given universe u. For any right transversal T of H in G, canonical
corestriction cor_H^G equals the k-linear cohomology map induced by Tr_T. For a right
transversal T, write t g=h_T(t,g) r_T(t,g), with h_T(t,g)∈H and r_T(t,g)∈T. The transferred
one-cochain is Tr_T(f)(g)=Σ_{t∈T}ρ(t⁻¹)f(h_T(t,g)). The equality holds for the complete maps
H¹(H,Res_H A)→H¹(G,A). -/
theorem corestrictionH1_eq_of_rightTransversal (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal) :
    corestrictionH1 A = corestrictionH1OfRightTransversal A T :=
  corestrictionH1OfRightTransversal_independent A
    (default : H.RightTransversal) T

/-- Let k be a commutative ring, G a group, H≤G a finite-index subgroup, and A a k-linear
G-representation, in the given universe u. For any right transversal T and subgroup one-cocycle
f∈Z¹(H,Res_H A), cor_H^G([f])=[Tr_T(f)] in H¹(G,A). For a right transversal T, write t
g=h_T(t,g) r_T(t,g), with h_T(t,g)∈H and r_T(t,g)∈T. The transferred one-cochain is
Tr_T(f)(g)=Σ_{t∈T}ρ(t⁻¹)f(h_T(t,g)). The transferred function is a G-one-cocycle, and its
cohomology class is independent of T. -/
@[simp]
theorem corestrictionH1_H1π (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal)
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH1 A
        (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A) f) =
      groupCohomology.H1π A (corestrictionCocyclesOne A T f) := by
  rw [corestrictionH1_eq_of_rightTransversal A T,
    corestrictionH1OfRightTransversal_H1π]

end groupCohomology
