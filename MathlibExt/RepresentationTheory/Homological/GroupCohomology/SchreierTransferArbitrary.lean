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
# Schreier cochain transfer in every degree

Let H ≤ G have finite index, let T be a right transversal and let A be a k-linear
G-representation over a commutative ring. For g : Fin n → G, start at t₀ = t and write tᵢgᵢ =
aᵢtᵢ₊₁ with aᵢ ∈ H and tᵢ₊₁ ∈ T. The transfer formula is cor_Tⁿ(f)(g) = ∑ₜ ρ(t⁻¹)f(a₀,…,aₙ₋₁).

This gives a linear map from inhomogeneous H-cochains to G-cochains for every n, including n =
0. At n = 1 it agrees with the ordinary single-factor Schreier formula.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Finite representatives for arbitrary-degree cochain transfer.

The finite-index hypothesis gives a finite enumeration of the right transversal used in every
degree-n transfer sum. -/
noncomputable local instance corestrictionArbitraryRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The finite-tuple Schreier cochain map in each degree.

For f : Hⁿ → A and g : Gⁿ, sum ρ(t⁻¹)f(a₀,…,aₙ₋₁) over t ∈ T, where the aᵢ are the successive
subgroup factors of the Schreier scan starting at t. The map is k-linear. -/
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

/-- The finite-tuple formula for arbitrary-degree transfer.

The transfer of f at g is ∑ₜ ρ(t⁻¹)f(T.schreierFactorTuple t g), with the ordered subgroup
factors of the representative scan. -/
@[simp]
theorem corestrictionCochain_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin n → H) → A) (g : Fin n → G) :
    corestrictionCochain A T n f g =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (f (T.schreierFactorTuple t g)) :=
  rfl

/-- Agreement with the single-factor degree-one formula.

For f : H → A and g ∈ G, the degree-one tuple transfer of x ↦ f(x₀) on the constant one-entry
tuple g equals corestrictionCochainOne A T f g. -/
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
