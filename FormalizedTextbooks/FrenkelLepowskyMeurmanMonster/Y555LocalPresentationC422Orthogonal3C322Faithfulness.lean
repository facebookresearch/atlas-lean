/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original C322 inclusion is faithful inside the independently presented C422/S/Q group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3C322Intertwining

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A trivial projective parabolic image is trivial in its actual linear source lift. -/
theorem y422Orthogonal3C322Hom_projective_eq_one (x : Y322Presentation)
    (hx : Matrix.ProjGenLinGroup.mk (y422Orthogonal3C322Hom x) = 1) :
    y422Orthogonal3C322Hom x = 1 := by
  have hc := Matrix.ProjGenLinGroup.mk_eq_one.mp hx
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, hu⟩ := hc
  have hf : (Matrix.GeneralLinearGroup.scalar (Fin 8) u).val *ᵥ
      y422Orthogonal3FixedVector = y422Orthogonal3FixedVector := by
    rw [hu]
    exact y422Orthogonal3C322Hom_fixed x
  have hunit := (y422Orthogonal3Scalar_fixed_iff u).mp hf
  rw [hunit, map_one] at hu
  exact hu.symm

/-- A trivial linear parabolic lift forces triviality by the faithful original C322 action. -/
theorem y422Orthogonal3C322Hom_eq_one (x : Y322Presentation)
    (hx : y422Orthogonal3C322Hom x = 1) : x = 1 := by
  apply y322Orthogonal3Hom_injective
  rw [map_one]
  apply Units.ext
  have h := y422Orthogonal3C322Hom_intertwines x
  rw [hx, Units.val_one, Matrix.one_mul] at h
  have hl := congrArg (fun A => y422Orthogonal3C322Projection * A) h
  rw [← Matrix.mul_assoc, y422Orthogonal3C322Projection_embedding, one_mul] at hl
  exact hl.symm

/-- The actual projective restriction to the original C322 parabolic is injective. -/
theorem y422Orthogonal3C322Hom_projective_injective :
    Function.Injective (Matrix.ProjGenLinGroup.mk.comp y422Orthogonal3C322Hom) := by
  intro x y h
  let f := Matrix.ProjGenLinGroup.mk.comp y422Orthogonal3C322Hom
  change f x = f y at h
  have hm : f (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have he := y422Orthogonal3C322Hom_eq_one (x * y⁻¹)
    (y422Orthogonal3C322Hom_projective_eq_one (x * y⁻¹) hm)
  exact mul_inv_eq_one.mp he

/-- The original C322 source homomorphism into original C422/S/Q is genuinely injective. -/
theorem y422C322Hom_injective : Function.Injective y422C322Hom := by
  intro x y h
  apply y422Orthogonal3C322Hom_projective_injective
  have he := congrArg y422Orthogonal3ProjectiveHom h
  change (y422Orthogonal3ProjectiveHom.comp y422C322Hom) x =
    (y422Orthogonal3ProjectiveHom.comp y422C322Hom) y at he
  rw [y422Orthogonal3C322Hom_projective] at he
  exact he

/-- The original C322 source group is isomorphic to its actual parabolic image in C422/S/Q. -/
noncomputable def y422C322SourceEquiv : Y322Presentation ≃* y422C322Subgroup :=
  MonoidHom.ofInjective y422C322Hom_injective

/-- The genuine original C322 parabolic image has its exact previously proved source order. -/
theorem y422C322Subgroup_card : Nat.card y422C322Subgroup = 9170703360 := by
  rw [← Nat.card_congr y422C322SourceEquiv.toEquiv, y322Orthogonal3_exact_order_faithful.1]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
