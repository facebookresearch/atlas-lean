/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Explicit boundaries represent zero in group cohomology

Let k be a commutative ring, G any group, and A a k-linear representation in universe u. In the
nonnegative inhomogeneous cochain complex K, a cocycle z in degree n+1 with included cochain
equal to K.d_{n,n+1}(b) has zero cohomology class.

The cocycle inclusion is injective, so z is the cycle factorization of this differential. The
homology projection annihilates the differential, giving [z]=0 for every n≥0.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Let k be a commutative ring, G a group, A a k-linear representation in universe u, and K its
inhomogeneous cochain complex. For n≥0, z∈Z^{n+1}(G,A), and b∈K^n, if the cocycle inclusion
satisfies i_{n+1}(z)=K.d_{n,n+1}(b), then its class π_{n+1}(z) in H^{n+1}(G,A) equals zero. -/
theorem π_eq_zero_of_boundary_succ
    (A : Rep k G) (n : ℕ) (z : cocycles A (n + 1))
    (b : (inhomogeneousCochains A).X n)
    (hboundary : ((inhomogeneousCochains A).iCycles (n + 1)).hom z =
      ((inhomogeneousCochains A).d n (n + 1)).hom b) :
    π A (n + 1) z = 0 := by
  let K := inhomogeneousCochains A
  have hz : z = (K.toCycles n (n + 1)).hom b := by
    apply (ModuleCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
    change (K.iCycles (n + 1)).hom z =
      (K.iCycles (n + 1)).hom ((K.toCycles n (n + 1)).hom b)
    rw [hboundary]
    exact (ConcreteCategory.congr_hom (K.toCycles_i n (n + 1)) b).symm
  rw [hz]
  change (K.homologyπ (n + 1)).hom
    ((K.toCycles n (n + 1)).hom b) = 0
  rw [← ConcreteCategory.comp_apply,
    K.toCycles_comp_homologyπ]
  rfl

end groupCohomology
