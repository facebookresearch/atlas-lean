/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.HahnSeries.MonoidAlgebra
import Mathlib.Tactic.NormNum

open HahnSeries

private noncomputable def sourcePMonoidHom :
    Multiplicative (ℤ × ℤ) →* HahnSeries ℤ (AddMonoidAlgebra ℚ ℤ) where
  toFun p := single p.toAdd.2 (AddMonoidAlgebra.single p.toAdd.1 1)
  map_one' := rfl
  map_mul' p q := by
    change
      single (p.toAdd.2 + q.toAdd.2)
          (AddMonoidAlgebra.single (p.toAdd.1 + q.toAdd.1) 1) = _
    rw [single_mul_single, AddMonoidAlgebra.single_mul_single, one_mul]

private noncomputable def sourceMMonoidHom :
    Multiplicative (ℤ × ℤ) →* HahnSeries ℤ (AddMonoidAlgebra ℚ ℤ) where
  toFun p := single p.toAdd.1 (AddMonoidAlgebra.single p.toAdd.2 1)
  map_one' := rfl
  map_mul' p q := by
    change
      single (p.toAdd.1 + q.toAdd.1)
          (AddMonoidAlgebra.single (p.toAdd.2 + q.toAdd.2) 1) = _
    rw [single_mul_single, AddMonoidAlgebra.single_mul_single, one_mul]

private noncomputable def sourceToP :
    AddMonoidAlgebra ℚ (ℤ × ℤ) →ₐ[ℚ] HahnSeries ℤ (AddMonoidAlgebra ℚ ℤ) :=
  AddMonoidAlgebra.lift ℚ _ _ sourcePMonoidHom

private noncomputable def sourceToM :
    AddMonoidAlgebra ℚ (ℤ × ℤ) →ₐ[ℚ] HahnSeries ℤ (AddMonoidAlgebra ℚ ℤ) :=
  AddMonoidAlgebra.lift ℚ _ _ sourceMMonoidHom

private theorem sourceToP_eq (f : AddMonoidAlgebra ℚ (ℤ × ℤ)) :
    sourceToP f = ofBivariateAddMonoidAlgebra f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simpa using congr($h₁ + $h₂)
  | single p r =>
      obtain ⟨x, y⟩ := p
      ext h g
      by_cases hg : g = x <;> by_cases hh : h = y <;>
        simp [sourceToP, sourcePMonoidHom, AddMonoidAlgebra.lift_single, hg, hh]

private theorem sourceToM_eq (f : AddMonoidAlgebra ℚ (ℤ × ℤ)) :
    sourceToM f =
      ofBivariateAddMonoidAlgebra
        (AddMonoidAlgebra.mapDomainRingEquiv ℚ
          (AddEquiv.prodComm (M := ℤ) (N := ℤ)) f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simpa using congr($h₁ + $h₂)
  | single p r =>
      obtain ⟨x, y⟩ := p
      ext h g
      by_cases hg : g = y <;> by_cases hh : h = x <;>
        simp [sourceToM, sourceMMonoidHom, AddMonoidAlgebra.lift_single, hg, hh]

private theorem sourceToP_coeff (f : AddMonoidAlgebra ℚ (ℤ × ℤ)) (x y : ℤ) :
    ((sourceToP f).coeff y).coeff x = f.coeff (x, y) := by
  rw [sourceToP_eq]
  simp

private theorem sourceToM_coeff (f : AddMonoidAlgebra ℚ (ℤ × ℤ)) (x y : ℤ) :
    ((sourceToM f).coeff x).coeff y = f.coeff (x, y) := by
  rw [sourceToM_eq]
  simp

private noncomputable def asymmetric : AddMonoidAlgebra ℚ (ℤ × ℤ) :=
  AddMonoidAlgebra.single (-2, 3) 5 + AddMonoidAlgebra.single (4, -1) (-7)

example : ((sourceToP asymmetric).coeff 3).coeff (-2) = 5 := by
  simp [sourceToP_coeff, asymmetric]

example : ((sourceToP asymmetric).coeff (-1)).coeff 4 = -7 := by
  simp [sourceToP_coeff, asymmetric]

example : ((sourceToP asymmetric).coeff (-2)).coeff 3 = 0 := by
  simp [sourceToP_coeff, asymmetric]

example : ((sourceToM asymmetric).coeff (-2)).coeff 3 = 5 := by
  simp [sourceToM_coeff, asymmetric]

example : ((sourceToM asymmetric).coeff 4).coeff (-1) = -7 := by
  simp [sourceToM_coeff, asymmetric]

example : ((sourceToM asymmetric).coeff 3).coeff (-2) = 0 := by
  simp [sourceToM_coeff, asymmetric]

example :
    ((((ofBivariateAddMonoidAlgebra
          (AddMonoidAlgebra.single (1, -3) (2 : ℚ))) *
        ofBivariateAddMonoidAlgebra
          (AddMonoidAlgebra.single (-2, 2) (3 : ℚ))).coeff (-1)).coeff (-1)) = 6 := by
  rw [← map_mul]
  norm_num

example : ofBivariateAddMonoidAlgebra (R := ℚ) (G := ℤ) (H := ℤ) 0 = 0 := by
  exact map_zero _

example :
    ((ofBivariateAddMonoidAlgebra
      (AddMonoidAlgebra.single (2, 0) (3 : ℕ) +
        AddMonoidAlgebra.single (2, 0) 4)).coeff 0).coeff 2 = 7 := by
  simp

example : Function.Injective
    (ofBivariateAddMonoidAlgebra :
      AddMonoidAlgebra ℚ (ℤ × ℤ) → HahnSeries ℤ (AddMonoidAlgebra ℚ ℤ)) :=
  ofBivariateAddMonoidAlgebra_injective

#print axioms HahnSeries.ofAddMonoidAlgebra
#print axioms HahnSeries.coeff_ofAddMonoidAlgebra
#print axioms HahnSeries.ofAddMonoidAlgebra_apply
#print axioms HahnSeries.ofAddMonoidAlgebra_injective
#print axioms HahnSeries.ofBivariateAddMonoidAlgebra
#print axioms HahnSeries.coeff_coeff_ofBivariateAddMonoidAlgebra
#print axioms HahnSeries.ofBivariateAddMonoidAlgebra_injective
