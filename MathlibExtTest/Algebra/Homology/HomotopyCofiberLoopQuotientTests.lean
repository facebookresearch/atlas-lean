/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.HomotopyCofiberCoordinates
public import MathlibExt.Algebra.Homology.HomotopyCofiberHomotopyMapCoherence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.Ring

/-!
# A nonzero differential and homotopy on a loop-shaped cofiber

Over `ZMod 16`, multiplication by `4` is a nonzero square-zero differential on a one-point
loop. Multiplication by `2` is a nonzero homotopy on a commuting square. The cofiber charts
detect the negative shifted differential, the positive homotopy term and a nonidentity map.
The pasted homotopy uses the actual composition law of the induced cofiber maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex.homotopyCofiber

namespace MathlibExtTest.HomotopyCofiberLoopQuotient

private abbrev R := ZMod 16
private abbrev M := ModuleCat.of R R
private abbrev loop := ComplexShape.refl PUnit
local instance : DecidableRel loop.Rel := fun i j => (inferInstance : Decidable (i = j))
private abbrev u : PUnit := PUnit.unit
local instance : HasFiniteBiproducts (ModuleCat R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat R)
local instance : HasBinaryBiproducts (ModuleCat R) :=
  hasBinaryBiproducts_of_finite_biproducts (ModuleCat R)

private def scale (a : R) : M ⟶ M :=
  ModuleCat.ofHom (X := M) (Y := M) (a • (LinearMap.id : R →ₗ[R] R))
private lemma scale_apply (a x : R) : (scale a).hom x = a * x := rfl
private def K : HomologicalComplex (ModuleCat R) loop where
  X _ := M
  d _ _ := scale 4
  shape i j hij := False.elim (hij (Subsingleton.elim i j))
  d_comp_d' _ _ _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (4 : R) * (4 * x) = 0
    rw [← mul_assoc, show (4 : R) * 4 = 0 from by decide, zero_mul]
private def multiply (a : R) : K ⟶ K where
  f _ := scale a
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change R at x
    change (4 : R) * (a * x) = a * (4 * x)
    ring
private abbrev phi := multiply 5
private abbrev minus := multiply (-1)
private def H : Homotopy (phi ≫ minus) (minus ≫ phi) where
  hom _ _ := scale 2
  zero i j h := False.elim (h (Subsingleton.elim j i))
  comm _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change R at x
    change (-1 : R) * (5 * x) = 2 * (4 * x) + 4 * (2 * x) + 5 * (-1 * x)
    have h : (-1 : R) * 5 = 2 * 4 + 4 * 2 + 5 * (-1) := by decide
    calc
      (-1 : R) * (5 * x) = ((-1 : R) * 5) * x := (mul_assoc _ _ _).symm
      _ = (2 * 4 + 4 * 2 + 5 * (-1 : R)) * x := congrArg (fun r : R => r * x) h
      _ = 2 * (4 * x) + 4 * (2 * x) + 5 * (-1 * x) := by ring
private def predecessor : ∀ j : PUnit, ∃ i, loop.Rel i j := fun j => ⟨j, rfl⟩
private abbrev Cof := HomologicalComplex.homotopyCofiber phi
private abbrev chart := XIsoBiprod phi u u rfl
private abbrev induced := mapOfHomotopy phi phi predecessor minus minus H
private def differentialCoordinates : M ⊞ M ⟶ M ⊞ M :=
  chart.inv ≫ Cof.d u u ≫ chart.hom
private def mapCoordinates : M ⊞ M ⟶ M ⊞ M :=
  chart.inv ≫ induced.f u ≫ chart.hom
private lemma differential_block : differentialCoordinates =
    biprod.desc (biprod.lift (-scale 4) (scale 5)) (biprod.lift 0 (scale 4)) :=
  XIsoBiprod_inv_d_hom phi u u u rfl rfl
private lemma homotopy_block : mapCoordinates =
    biprod.desc (biprod.lift (scale (-1)) (scale 2)) (biprod.lift 0 (scale (-1))) := by
  apply biprod.hom_ext _ _
  · apply biprod.hom_ext'
    · simp only [mapCoordinates, Category.assoc, inl_XIsoBiprod_inv_assoc,
        inlX_mapOfHomotopy_assoc, add_comp, inrX_XIsoBiprod_hom_assoc,
        inlX_XIsoBiprod_hom_assoc, biprod.inl_desc_assoc, biprod.lift_fst,
        biprod.inr_fst, biprod.inl_fst, comp_zero, Category.comp_id, add_zero, zero_add]
      rfl
    · simp only [mapCoordinates, Category.assoc, inr_XIsoBiprod_inv_assoc,
        inrX_mapOfHomotopy_assoc, inrX_XIsoBiprod_hom_assoc,
        biprod.inr_desc_assoc, biprod.lift_fst, biprod.inr_fst, comp_zero]
  · apply biprod.hom_ext'
    · simp only [mapCoordinates, Category.assoc, inl_XIsoBiprod_inv_assoc,
        inlX_mapOfHomotopy_assoc, add_comp, inrX_XIsoBiprod_hom_assoc,
        inlX_XIsoBiprod_hom_assoc, biprod.inl_desc_assoc, biprod.lift_snd,
        biprod.inr_snd, biprod.inl_snd, comp_zero, Category.comp_id, zero_add, add_zero]
      rfl
    · simp only [mapCoordinates, Category.assoc, inr_XIsoBiprod_inv_assoc,
        inrX_mapOfHomotopy_assoc, inrX_XIsoBiprod_hom_assoc,
        biprod.inr_desc_assoc, biprod.lift_snd, biprod.inr_snd, Category.comp_id]
      rfl
private def diagonalInput : M ⟶ M ⊞ M := biprod.lift (𝟙 M) (𝟙 M)
private def firstValue (f : M ⊞ M ⟶ M ⊞ M) : R :=
  (diagonalInput ≫ f ≫ biprod.fst).hom (1 : R)
private def secondValue (f : M ⊞ M ⟶ M ⊞ M) : R :=
  (diagonalInput ≫ f ≫ biprod.snd).hom (1 : R)
private lemma first_row (a b c d : M ⟶ M) :
    diagonalInput ≫ biprod.desc (biprod.lift a b) (biprod.lift c d) ≫ biprod.fst =
      a + c := by
  simp [diagonalInput, biprod.desc_eq, Category.assoc, comp_add, add_comp]
private lemma second_row (a b c d : M ⟶ M) :
    diagonalInput ≫ biprod.desc (biprod.lift a b) (biprod.lift c d) ≫ biprod.snd =
      b + d := by
  simp [diagonalInput, biprod.desc_eq, Category.assoc, comp_add, add_comp]
private lemma differential_first : firstValue differentialCoordinates = 12 := by
  unfold firstValue
  rw [differential_block, first_row]
  change (-((4 : R) * 1)) + 0 = 12
  decide
private lemma differential_second : secondValue differentialCoordinates = 9 := by
  unfold secondValue
  rw [differential_block, second_row]
  change (5 : R) * 1 + 4 * 1 = 9
  decide
private lemma map_first : firstValue mapCoordinates = 15 := by
  unfold firstValue
  rw [homotopy_block, first_row]
  change (-1 : R) * 1 + 0 = 15
  decide
private lemma map_second : secondValue mapCoordinates = 1 := by
  unfold secondValue
  rw [homotopy_block, second_row]
  change (2 : R) * 1 + (-1) * 1 = 1
  decide

example : (4 : R) ≠ 0 := by decide
example : (4 : R) * 4 = 0 := by decide
example : H.hom u u ≠ 0 := by
  intro hz
  have h := congrArg (fun f : M ⟶ M => f.hom (1 : R)) hz
  change (2 : R) * 1 = 0 at h
  exact (by decide : (2 : R) * 1 ≠ 0) h
example : firstValue differentialCoordinates = 12 := differential_first
example : secondValue differentialCoordinates = 9 := differential_second
example : Cof.d u u ≫ Cof.d u u = 0 := Cof.d_comp_d u u u
example : Cof.d u u ≠ 0 := by
  intro hz
  have h : differentialCoordinates = 0 := by simp [differentialCoordinates, hz]
  have h0 : firstValue (0 : M ⊞ M ⟶ M ⊞ M) = 0 := by simp [firstValue]
  exact (by decide : (12 : R) ≠ 0)
    (differential_first.symm.trans ((congrArg firstValue h).trans h0))
example : firstValue mapCoordinates = 15 := map_first
example : secondValue mapCoordinates = 1 := map_second
example : induced ≠ 𝟙 Cof := by
  intro hz
  have h : mapCoordinates = 𝟙 (M ⊞ M) := by
    simp [mapCoordinates, hz]
  have h1 : firstValue (𝟙 (M ⊞ M)) = 1 := by simp [firstValue, diagonalInput]
  exact (by decide : (15 : R) ≠ 1)
    (map_first.symm.trans ((congrArg firstValue h).trans h1))
example : mapOfHomotopy phi phi predecessor (minus ≫ minus) (minus ≫ minus)
    (composeMapHomotopy phi phi phi minus minus minus minus H H) = induced ≫ induced :=
  mapOfHomotopy_comp phi phi phi predecessor minus minus minus minus H H

end MathlibExtTest.HomotopyCofiberLoopQuotient
