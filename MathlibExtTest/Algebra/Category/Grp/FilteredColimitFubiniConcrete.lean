/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits.Fubini
import Mathlib.Tactic.Ring

/-! A nonconstant grid of integer groups tests the chosen Fubini quotient maps. -/

open CategoryTheory CategoryTheory.Limits
open GrpCat.FilteredColimits.Fubini

noncomputable section

private abbrev ZGroup := GrpCat.of (Multiplicative ℤ)

private def scale (n : ℤ) : ZGroup ⟶ ZGroup :=
  GrpCat.ofHom
    { toFun := fun x => Multiplicative.ofAdd (n * x.toAdd)
      map_one' := by change Multiplicative.ofAdd (n * 0) = _; rw [mul_zero]; rfl
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd (n * (x.toAdd + y.toAdd)) =
          Multiplicative.ofAdd (n * x.toAdd + n * y.toAdd)
        rw [mul_add] }

private theorem scale_one : scale 1 = 𝟙 ZGroup := by
  apply GrpCat.ext
  intro x
  change (1 : ℤ) * (show ℤ from x) = (show ℤ from x)
  exact one_mul _

private theorem scale_comp (a b : ℤ) : scale a ≫ scale b = scale (b * a) := by
  apply GrpCat.ext
  intro x
  change b * (a * (show ℤ from x)) = b * a * (show ℤ from x)
  exact (mul_assoc _ _ _).symm

private def sign (cut n : ℕ) : ℤ := if n ≤ cut then 1 else -1

private theorem sign_sq (cut n : ℕ) : sign cut n * sign cut n = 1 := by
  by_cases h : n ≤ cut <;> simp [sign, h]

private theorem step_comp (cut i j k : ℕ) :
    scale (sign cut i * sign cut j) ≫ scale (sign cut j * sign cut k) =
      scale (sign cut i * sign cut k) := by
  rw [scale_comp]
  congr 1
  calc
    (sign cut j * sign cut k) * (sign cut i * sign cut j) =
        (sign cut j * sign cut j) * (sign cut i * sign cut k) := by ring
    _ = _ := by rw [sign_sq, one_mul]

-- The column arrows change sign at 1 → 2; the row arrows change sign at 0 → 1.
private def column : ℕ ⥤ GrpCat where
  obj _ := ZGroup
  map {i j} _ := scale (sign 1 i * sign 1 j)
  map_id n := by rw [sign_sq, scale_one]
  map_comp {i j k} _ _ := (step_comp 1 i j k).symm

private def columnScale (n : ℤ) : column ⟶ column where
  app _ := scale n
  naturality i j _ := by
    change scale (sign 1 i * sign 1 j) ≫ scale n = scale n ≫ scale (sign 1 i * sign 1 j)
    simp only [scale_comp, mul_comm n]

private def grid : ℕ ⥤ ℕ ⥤ GrpCat where
  obj _ := column
  map {i j} _ := columnScale (sign 0 i * sign 0 j)
  map_id i := NatTrans.ext (funext fun _ => by
    change scale (sign 0 i * sign 0 i) = 𝟙 ZGroup
    rw [sign_sq, scale_one])
  map_comp {i j k} _ _ := NatTrans.ext (funext fun _ => (step_comp 0 i j k).symm)

private def double : grid ⟶ grid where
  app _ := columnScale 2
  naturality i j _ := NatTrans.ext (funext fun _ => by
    change scale (sign 0 i * sign 0 j) ≫ scale 2 = scale 2 ≫ scale (sign 0 i * sign 0 j)
    rw [scale_comp, scale_comp, mul_comm 2])

private abbrev rowStep : (0 : ℕ) ⟶ 1 := homOfLE (by decide)
private abbrev columnStep : (1 : ℕ) ⟶ 2 := homOfLE (by decide)
private abbrev integer (n : ℤ) : Multiplicative ℤ := Multiplicative.ofAdd n

example : ((grid.map rowStep).app 1) (integer 3) = integer (-3) := rfl

example : (grid.obj 0).map columnStep (integer 3) = integer (-3) := rfl

example : ((grid.map rowStep).app 1) (integer 3) ≠ integer 3 := by
  change integer (-3) ≠ integer 3
  decide

private def rep (F : ℕ ⥤ ℕ ⥤ GrpCat) (i j : ℕ) (x : (F.obj i).obj j) :
    iteratedColimitFunctor.obj F :=
  GrpCat.FilteredColimits.G.mk (innerColimitDiagram F)
    ⟨i, GrpCat.FilteredColimits.G.mk (F.obj i) ⟨j, x⟩⟩

-- Undo both signs at each stage to detect a nonunit in the actual joint quotient.
private def detector : Cocone (Functor.uncurry.obj grid) where
  pt := ZGroup
  ι :=
    { app := fun p => scale (sign 0 p.1 * sign 1 p.2)
      naturality := by
        rintro ⟨i, j⟩ ⟨i', j'⟩ f
        change (scale (sign 0 i * sign 0 i') ≫ scale (sign 1 j * sign 1 j')) ≫
            scale (sign 0 i' * sign 1 j') = scale (sign 0 i * sign 1 j) ≫ 𝟙 ZGroup
        simp only [Category.comp_id, scale_comp]
        congr 1
        calc
          (sign 0 i' * sign 1 j') * ((sign 1 j * sign 1 j') * (sign 0 i * sign 0 i')) =
              (sign 0 i' * sign 0 i') * (sign 1 j' * sign 1 j') * (sign 0 i * sign 1 j) := by ring
          _ = _ := by rw [sign_sq, sign_sq, one_mul, one_mul] }

example : rep grid 0 1 (integer 3) ≠ 1 := by
  intro h
  let forgetSigns : (iteratedColimitFunctor.obj grid) →* ZGroup :=
    ((jointCoconeIsColimit grid).desc detector).hom
  have value : forgetSigns (rep grid 0 1 (integer 3)) = integer 3 :=
    ConcreteCategory.congr_hom ((jointCoconeIsColimit grid).fac detector (0, 1)) (integer 3)
  have impossible : (1 : Multiplicative ℤ) = integer 3 :=
    (map_one forgetSigns).symm.trans ((congrArg forgetSigns h).symm.trans value)
  exact (by decide : (1 : Multiplicative ℤ) ≠ integer 3) impossible

example : rep grid 1 1 (integer (-3)) = rep grid 0 1 (integer 3) := by
  have value := ConcreteCategory.congr_hom (jointLeg_naturality grid rowStep (𝟙 (1 : ℕ)))
    (integer 3)
  exact value

example : (fubiniIso grid).hom (rep grid 0 1 (integer 3)) =
    rep grid.flip 1 0 (integer 3) :=
  fubiniIso_hom_apply grid 0 1 (integer 3)

example : (fubiniIso grid).inv (rep grid.flip 1 0 (integer 3)) =
    rep grid 0 1 (integer 3) :=
  fubiniIso_inv_apply grid 0 1 (integer 3)

example :
    ((fubiniIso grid).hom ≫ iteratedColimitFunctor.map ((flipFunctor ℕ ℕ GrpCat).map double))
        (rep grid 0 1 (integer 3)) = rep grid.flip 1 0 (integer 6) := by
  rw [← fubiniIso_naturality double, GrpCat.comp_apply]
  have scaled := ConcreteCategory.congr_hom (iteratedColimit_map_fac double 0 1)
    (integer 3)
  change (iteratedColimitFunctor.map double) (rep grid 0 1 (integer 3)) =
    rep grid 0 1 (integer 6) at scaled
  rw [scaled]
  exact fubiniIso_hom_apply grid 0 1 (integer 6)
