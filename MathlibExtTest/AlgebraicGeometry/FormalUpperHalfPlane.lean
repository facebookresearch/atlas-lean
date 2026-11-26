/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalUpperHalfPlane

@[expose] public section

noncomputable section

open CategoryTheory Opposite CerednikDrinfeld FormalOmega

-- The vertex chart ring corepresents the vertex chart functor: a natural isomorphism from the
-- functor corepresented by the bundled chart ring.
example (R : Type) [CommRing R] (q : ℕ) :
    coyoneda.obj (op (CommAlgCat.of R (chartVRing R q))) ≅ chartV R q :=
  chartVRing.corepIso R q

-- The edge chart ring corepresents the edge chart functor.
example (R : Type) [CommRing R] (π : R) (q : ℕ) :
    coyoneda.obj (op (CommAlgCat.of R (chartERing R π q))) ≅ chartE R π q :=
  chartERing.corepIso R π q

-- The isomorphism reads an algebra map out of the chart ring at the chart coordinates.
example (R : Type) [CommRing R] (q : ℕ) (B : CommAlgCat.{0} R)
    (φ : CommAlgCat.of R (chartVRing R q) ⟶ B) :
    ((chartVRing.corepIso R q).hom.app B φ).1 = φ (chartVRing.ζ R q) :=
  chartVRing.corepIso_hom_app_val B φ

example (R : Type) [CommRing R] (π : R) (q : ℕ) (B : CommAlgCat.{0} R)
    (φ : CommAlgCat.of R (chartERing R π q) ⟶ B) :
    ((chartERing.corepIso R π q).hom.app B φ).1 =
      (φ (chartERing.ξ R π q), φ (chartERing.η R π q)) :=
  chartERing.corepIso_hom_app_val B φ

-- Its inverse sends a point to the algebra map that evaluates the coordinates there.
example (R : Type) [CommRing R] (q : ℕ) (B : CommAlgCat.{0} R) (x : (chartV R q).obj B) :
    ((chartVRing.corepIso R q).inv.app B x).hom (chartVRing.ζ R q) = x.1 := by
  rw [chartVRing.corepIso_inv_app]
  simp

example (R : Type) [CommRing R] (π : R) (q : ℕ) (B : CommAlgCat.{0} R)
    (x : (chartE R π q).obj B) :
    ((chartERing.corepIso R π q).inv.app B x).hom (chartERing.ξ R π q) = x.1.1 ∧
      ((chartERing.corepIso R π q).inv.app B x).hom (chartERing.η R π q) = x.1.2 := by
  rw [chartERing.corepIso_inv_app]
  simp

-- The universal point: the coordinate `ζ` of the vertex chart ring, whose discriminant is a unit.
example (R : Type) [CommRing R] (q : ℕ) :
    (chartV R q).obj (CommAlgCat.of R (chartVRing R q)) :=
  chartVRing.point R q

example (R : Type) [CommRing R] (q : ℕ) :
    IsUnit (chartVRing.ζ R q ^ q - chartVRing.ζ R q) :=
  chartVRing.isUnit_ζ_pow_sub R q

-- A concrete point of the vertex chart: over `ℚ` and for `q = 3`, `ζ = 2` has discriminant
-- `2 ^ 3 - 2 = 6`, a unit.
private theorem isUnit_two_pow_three_sub_two : IsUnit ((2 : ℚ) ^ 3 - 2) :=
  isUnit_iff_ne_zero.mpr (by norm_num)

private def twoPoint : (chartV ℚ 3).obj (CommAlgCat.of ℚ ℚ) :=
  ⟨2, isUnit_two_pow_three_sub_two⟩

-- The algebra map out of the vertex chart ring that corresponds to this point sends `ζ` to `2`.
example : chartVRing.lift twoPoint (chartVRing.ζ ℚ 3) = 2 :=
  chartVRing.lift_ζ twoPoint

example : (chartVRing.corepEquiv ℚ 3 (CommAlgCat.of ℚ ℚ)).symm twoPoint (chartVRing.ζ ℚ 3) = 2 :=
  chartVRing.lift_ζ twoPoint

-- A concrete point of the edge chart: over `ℚ`, for `π = 6` and `q = 3`, the pair `(2, 3)` has
-- `2 * 3 = 6`, and `2 ^ 2 - 1 = 3` and `3 ^ 2 - 1 = 8` are units.
private def twoThreePoint : (chartE ℚ 6 3).obj (CommAlgCat.of ℚ ℚ) :=
  ⟨(2, 3), by norm_num, isUnit_iff_ne_zero.mpr (by norm_num),
    isUnit_iff_ne_zero.mpr (by norm_num)⟩

example : chartERing.lift twoThreePoint (chartERing.ξ ℚ 6 3) = 2 :=
  chartERing.lift_ξ twoThreePoint

example : chartERing.lift twoThreePoint (chartERing.η ℚ 6 3) = 3 :=
  chartERing.lift_η twoThreePoint

-- The chart condition excludes points: over `ℤ`, `2 ^ 3 - 2 = 6` is not a unit, so no point of
-- the `q = 3` vertex chart has coordinate `2`.
example (x : (chartV ℤ 3).obj (CommAlgCat.of ℤ ℤ)) : x.1 ≠ 2 := by
  intro h
  have hx := x.2
  rw [h, Int.isUnit_iff] at hx
  norm_num at hx

-- Over `ℚ`, `ζ = -1` has discriminant `(-1) ^ 3 - (-1) = 0`, so it is not a point of the chart.
example (x : (chartV ℚ 3).obj (CommAlgCat.of ℚ ℚ)) : x.1 ≠ -1 := by
  intro h
  have hx := x.2
  rw [h] at hx
  norm_num at hx

-- Mathlib's natural transformations carry the nilpotent-locus conditions: the identity is an
-- isomorphism there, and the inclusion of the unit vertex chart is injective.
example (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (F : CommAlgCat.{0} 𝒪 ⥤ Type) :
    IsIsoOnNilp π (𝟙 F) :=
  fun _ _ => Function.bijective_id

example (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (q : ℕ) : IsMonoOnNilp π (chartVUnitIncl 𝒪 q) :=
  fun _ _ _ _ h => Subtype.ext (congrArg Subtype.val h :)

-- The chart transition at a nonzero nilpotent: over `ℤ`, with `π = 3` and `q = 2`, in `ℤ/9ℤ`, where
-- `3` is nilpotent but not zero, and in its reduction `ℤ/3ℤ`, where `3` becomes `0`.
private theorem isNilpotent_three_zmod9 : IsNilpotent (algebraMap ℤ (ZMod 9) 3) :=
  ⟨2, by rw [map_ofNat]; decide⟩

private theorem isNilpotent_three_zmod3 : IsNilpotent (algebraMap ℤ (ZMod 3) 3) :=
  ⟨1, by rw [map_ofNat]; decide⟩

-- `ζ = 2` is a point of the unit vertex chart of `ℤ/9ℤ` for `q = 2`: `2 ^ 2 - 2 = 2` and `2` are
-- units, with inverse `5`.
private def twoUnitPoint9 : (chartVUnit ℤ 2).obj (CommAlgCat.of ℤ (ZMod 9)) :=
  ⟨2, IsUnit.of_mul_eq_one 5 (by decide), IsUnit.of_mul_eq_one 5 (by decide)⟩

-- The reduction `ℤ/9ℤ → ℤ/3ℤ`.
private def reduce9 : CommAlgCat.of ℤ (ZMod 9) ⟶ CommAlgCat.of ℤ (ZMod 3) :=
  CommAlgCat.ofHom (ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toIntAlgHom

-- The transition inverts `ζ`: it sends `ζ = 2` to `(ζ, π ζ⁻¹) = (2, 3 * 5) = (2, 6)`, a point of
-- the edge chart at the least exponent `q - 1 = 1`.
private theorem vertexToEdge_twoUnitPoint9 :
    (vertexToEdge (3 : ℤ) le_rfl (CommAlgCat.of ℤ (ZMod 9)) isNilpotent_three_zmod9
      twoUnitPoint9).1 = (2, 6) := by
  refine Prod.ext rfl ?_
  change algebraMap ℤ _ 3 * ↑(twoUnitPoint9.2.2.unit⁻¹) = (6 : ZMod 9)
  rw [Units.inv_eq_of_mul_eq_one_right (u := twoUnitPoint9.2.2.unit) (a := 5)
    (by rw [IsUnit.unit_spec]; decide), map_ofNat]
  decide

-- Reducing to `ℤ/3ℤ` gives `(2, 0)`, both by reducing the edge point and by applying the
-- transition to the reduced vertex point, as naturality under the nonidentity map `reduce9` says.
example : ((chartE ℤ 3 2).map reduce9 (vertexToEdge (3 : ℤ) le_rfl (CommAlgCat.of ℤ (ZMod 9))
    isNilpotent_three_zmod9 twoUnitPoint9)).1 = (2, 0) := by
  change Prod.map reduce9.hom reduce9.hom (vertexToEdge (3 : ℤ) le_rfl (CommAlgCat.of ℤ (ZMod 9))
    isNilpotent_three_zmod9 twoUnitPoint9).1 = (2, 0)
  rw [vertexToEdge_twoUnitPoint9]
  decide

example : (vertexToEdge (3 : ℤ) le_rfl (CommAlgCat.of ℤ (ZMod 3)) isNilpotent_three_zmod3
    ((chartVUnit ℤ 2).map reduce9 twoUnitPoint9)).1 = (2, 0) := by
  refine Prod.ext (by decide) ?_
  change algebraMap ℤ _ 3 * _ = (0 : ZMod 3)
  rw [map_ofNat, show (3 : ZMod 3) = 0 by decide, zero_mul]

example : (chartE ℤ 3 2).map reduce9 (vertexToEdge (3 : ℤ) le_rfl (CommAlgCat.of ℤ (ZMod 9))
      isNilpotent_three_zmod9 twoUnitPoint9) =
    vertexToEdge (3 : ℤ) le_rfl (CommAlgCat.of ℤ (ZMod 3)) isNilpotent_three_zmod3
      ((chartVUnit ℤ 2).map reduce9 twoUnitPoint9) :=
  vertexToEdge_natural (3 : ℤ) le_rfl isNilpotent_three_zmod9 isNilpotent_three_zmod3 reduce9
    twoUnitPoint9

-- In `ℤ/9ℤ` with `π = 3`, `π ζ⁻¹ = π ζ` for every unit `ζ` (units mod `3` square to `1`), so the
-- example above cannot tell `ζ⁻¹` from `ζ`. In `ℤ/25ℤ` with `π = 5` it can: `ζ = 2` has inverse
-- `13`, and the transition gives `(2, 5 * 13) = (2, 15)`, not `(2, 5 * 2) = (2, 10)`.
private theorem isNilpotent_five_zmod25 : IsNilpotent (algebraMap ℤ (ZMod 25) 5) :=
  ⟨2, by rw [map_ofNat]; decide⟩

private def twoUnitPoint25 : (chartVUnit ℤ 2).obj (CommAlgCat.of ℤ (ZMod 25)) :=
  ⟨2, IsUnit.of_mul_eq_one 13 (by decide), IsUnit.of_mul_eq_one 13 (by decide)⟩

example : (vertexToEdge (5 : ℤ) le_rfl (CommAlgCat.of ℤ (ZMod 25)) isNilpotent_five_zmod25
    twoUnitPoint25).1 = (2, 15) := by
  refine Prod.ext rfl ?_
  change algebraMap ℤ _ 5 * ↑(twoUnitPoint25.2.2.unit⁻¹) = (15 : ZMod 25)
  rw [Units.inv_eq_of_mul_eq_one_right (u := twoUnitPoint25.2.2.unit) (a := 13)
    (by rw [IsUnit.unit_spec]; decide), map_ofNat]
  decide
