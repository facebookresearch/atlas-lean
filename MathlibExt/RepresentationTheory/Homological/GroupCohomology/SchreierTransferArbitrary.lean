/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- AI-assisted original formalization: Avocado; responsible human author: @toskua.
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransfer
public import MathlibExt.GroupTheory.SchreierTransversal

/-!
# Arbitrary-degree Schreier cochain transfer

Iterating the Schreier representative update along a tuple of group
elements produces, at each coordinate, the corresponding subgroup factor.
This file packages that scan for `Fin n` tuples and defines the standard
chosen-transversal cochain-transfer formula in every degree.

The construction is a graded family of linear maps.  Compatibility with the
arbitrary inhomogeneous differential, descent to cohomology, independence
of the transversal, and comparison with Shapiro corestriction are separate
theorems.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance corestrictionArbitraryRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Chosen-transversal inhomogeneous cochain transfer in arbitrary degree. -/
noncomputable def corestrictionCochain (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    ((Fin n → H) → A) →ₗ[k] ((Fin n → G) → A) where
  toFun f g := ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹ (f (T.schreierFactorTuple t g))
  map_add' f₁ f₂ := by
    funext g
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext g
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

@[simp]
theorem corestrictionCochain_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin n → H) → A) (g : Fin n → G) :
    corestrictionCochain A T n f g =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (f (T.schreierFactorTuple t g)) :=
  rfl

/-- In degree one, the arbitrary tuple formula is the existing Schreier
cochain transfer. -/
theorem corestrictionCochain_one_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H → A) (g : G) :
    corestrictionCochain A T 1 (fun x ↦ f (x 0)) (fun _ ↦ g) =
      corestrictionCochainOne A T f g := by
  rw [corestrictionCochain_apply, corestrictionCochainOne_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [Subgroup.RightTransversal.schreierFactorTuple_zero]

end groupCohomology
