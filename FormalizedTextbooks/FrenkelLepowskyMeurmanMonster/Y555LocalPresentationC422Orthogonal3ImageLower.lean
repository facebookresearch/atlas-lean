/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A checked projective orbit separates genuine source-parabolic cosets in the actual image. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3SortedPathCodes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3C322Faithfulness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The actual parabolic source inclusion projects to its genuine linear lift. -/
theorem y422Orthogonal3ProjectiveHom_C322 (x : Y322Presentation) :
    y422Orthogonal3ProjectiveHom (y422C322Hom x) =
      Matrix.ProjGenLinGroup.mk (y422Orthogonal3C322Hom x) :=
  congrArg (fun f : Y322Presentation →* Matrix.ProjGenLinGroup (Fin 8) (ZMod 3) => f x)
    y422Orthogonal3C322Hom_projective

/-- Actual original source elements combining the faithful parabolic with distinct orbit paths. -/
noncomputable def y422Orthogonal3ParabolicOrbitWord (p : Y322Presentation × Fin 1080) :
    Y422Presentation :=
  y422C322Hom p.1 * y422TPathValue (y422Orthogonal3SortedPath p.2)

/-- These actual source elements lie in the actual finite projective image. -/
noncomputable def y422Orthogonal3ParabolicOrbitImage (p : Y322Presentation × Fin 1080) :
    y422Orthogonal3ProjectiveImage :=
  ⟨y422Orthogonal3ProjectiveHom (y422Orthogonal3ParabolicOrbitWord p),
    ⟨y422Orthogonal3ParabolicOrbitWord p, rfl⟩⟩

/-- The linear source lift of each actual parabolic-orbit word retains both exact factors. -/
theorem y422Orthogonal3ParabolicOrbitImage_value (x : Y322Presentation) (i : Fin 1080) :
    (y422Orthogonal3ParabolicOrbitImage (x, i)).val =
      Matrix.ProjGenLinGroup.mk (y422Orthogonal3C322Hom x *
        y422Orthogonal3TPathValue (y422Orthogonal3SortedPath i)) := by
  simp only [y422Orthogonal3ParabolicOrbitImage, y422Orthogonal3ParabolicOrbitWord,
    map_mul, y422Orthogonal3ProjectiveHom_C322, y422Orthogonal3TPathValue_projective]

/-- Checked projective vector separation and faithful source-parabolic lifts give distinct
images. -/
theorem y422Orthogonal3ParabolicOrbitImage_injective :
    Function.Injective y422Orthogonal3ParabolicOrbitImage := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have hp := congrArg Subtype.val h
  rw [y422Orthogonal3ParabolicOrbitImage_value,
    y422Orthogonal3ParabolicOrbitImage_value] at hp
  have hinv : Matrix.ProjGenLinGroup.mk
      ((y422Orthogonal3C322Hom x *
        y422Orthogonal3TPathValue (y422Orthogonal3SortedPath i))⁻¹) =
      Matrix.ProjGenLinGroup.mk
      ((y422Orthogonal3C322Hom y *
        y422Orthogonal3TPathValue (y422Orthogonal3SortedPath j))⁻¹) := by
    simpa only [map_inv] using congrArg Inv.inv hp
  have hc := y422Orthogonal3ProjectiveVectorCode_of_projective_eq _ _ hinv
    y422Orthogonal3FixedVector
  have hx : ((y422Orthogonal3C322Hom x)⁻¹).val *ᵥ y422Orthogonal3FixedVector =
      y422Orthogonal3FixedVector := by
    rw [← map_inv]
    exact y422Orthogonal3C322Hom_fixed x⁻¹
  have hy : ((y422Orthogonal3C322Hom y)⁻¹).val *ᵥ y422Orthogonal3FixedVector =
      y422Orthogonal3FixedVector := by
    rw [← map_inv]
    exact y422Orthogonal3C322Hom_fixed y⁻¹
  simp only [mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy] at hc
  change y422Orthogonal3ProjectiveVectorCode
    (y422Orthogonal3TPathVector (y422Orthogonal3SortedPath i)) =
    y422Orthogonal3ProjectiveVectorCode
      (y422Orthogonal3TPathVector (y422Orthogonal3SortedPath j)) at hc
  have hij := y422Orthogonal3SortedPath_projectiveCode_injective hc
  subst j
  simp only [map_mul] at hp
  have hxy := mul_right_cancel hp
  have he : x = y := y422Orthogonal3C322Hom_projective_injective hxy
  exact Prod.ext he rfl

/-- The ambient actual projective matrix group is finite as a quotient of finite GL₈(F₃). -/
theorem y422Orthogonal3ProjectiveGroup_finite :
    Finite (Matrix.ProjGenLinGroup (Fin 8) (ZMod 3)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The actual projective image has the full checked parabolic-orbit lower bound. -/
theorem y422Orthogonal3ProjectiveImage_card_ge :
    9904359628800 ≤ Nat.card y422Orthogonal3ProjectiveImage := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 8) (ZMod 3)) :=
    y422Orthogonal3ProjectiveGroup_finite
  have : Finite y422Orthogonal3ProjectiveImage := by
    unfold y422Orthogonal3ProjectiveImage
    infer_instance
  have h := Nat.card_le_card_of_injective y422Orthogonal3ParabolicOrbitImage
    y422Orthogonal3ParabolicOrbitImage_injective
  rw [Nat.card_prod, Nat.card_fin, y322Orthogonal3_exact_order_faithful.1] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
