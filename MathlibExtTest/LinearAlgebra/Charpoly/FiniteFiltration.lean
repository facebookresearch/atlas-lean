/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExtTest.LinearAlgebra.Basis.FiniteFiltration
public import MathlibExt.LinearAlgebra.Charpoly.FiniteFiltration
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum

/-!
# Distinct graded eigenvalues in a proper two-step flag

The triangular map (x,y) ↦ (3x+7y,5y) acts by 3 and 5 on the two graded lines.
Its characteristic polynomial is (X-3)(X-5), with constant coefficient 15 and
linear coefficient -8. The off-diagonal entry is nonzero.
-/

@[expose] public section

noncomputable section
open Polynomial
open scoped BigOperators
namespace MathlibExtTest.FiniteFiltration

def triangular : V →ₗ[ℚ] V := Matrix.toLin' !![3, 7; 0, 5]

@[simp]
theorem triangular_apply (x : V) : triangular x = ![3 * x 0 + 7 * x 1, 5 * x 1] := by
  ext i
  fin_cases i <;> simp [triangular, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem triangular_stable (j : Fin 3) : flag j.val ≤ (flag j.val).comap triangular := by
  intro x hx
  change triangular x ∈ flag j.val
  fin_cases j
  · have hx0 : x = 0 := by simpa [flag] using hx
    simp [flag, hx0]
  · have hx1 : x 1 = 0 := by simpa [flag] using hx
    simp [flag, triangular_apply, hx1]
  · simp [flag]

def stageEnd (j : Fin 3) : flag j.val →ₗ[ℚ] flag j.val :=
  triangular.restrict (triangular_stable j)

def triangularStep (i : Fin 2) :
    LinearMap.InvariantExtension (R := ℚ) (stageEnd i.castSucc) (stageEnd i.succ) where
  submodule := (flag i.val).comap (flag (i.val + 1)).subtype
  stable := by
    intro x hx
    change triangular (x : V) ∈ flag i.val
    exact triangular_stable i.castSucc hx
  equiv := (Submodule.comapSubtypeEquivOfLe (flag_le i)).symm
  intertwines := by
    apply LinearMap.ext
    intro x
    rfl

def gradedEigenvalue (i : Fin 2) : ℚ := if i = 0 then 3 else 5

theorem quotient_coordinate_action (i : Fin 2) (q : Graded i) :
    gradedCoordinate i ((triangularStep i).quotientMap q) =
      gradedEigenvalue i * gradedCoordinate i q := by
  refine Submodule.Quotient.induction_on
    ((flag i.val).comap (flag (i.val + 1)).subtype) q ?_
  intro v
  rw [LinearMap.InvariantExtension.quotientMap_mk (triangularStep i) v]
  fin_cases i
  · have hv1 : (v : V) 1 = 0 := by simpa [flag] using v.property
    simp [gradedCoordinate, coordinate, triangularStep, stageEnd, gradedEigenvalue,
      triangular_apply, hv1]
  · simp [gradedCoordinate, coordinate, triangularStep, stageEnd, gradedEigenvalue,
      triangular_apply]

theorem quotient_conj (i : Fin 2) :
    (gradedEquiv i).conj (triangularStep i).quotientMap =
      (gradedEigenvalue i • LinearMap.id : ℚ →ₗ[ℚ] ℚ) := by
  apply LinearMap.ext
  intro c
  have h := quotient_coordinate_action i ((gradedEquiv i).symm (c : ℚ))
  simpa [LinearEquiv.conj_apply, ← gradedEquiv_apply] using h

theorem scalar_charpoly (c : ℚ) :
    (c • LinearMap.id : ℚ →ₗ[ℚ] ℚ).charpoly = X - C c := by
  rw [← LinearMap.charpoly_toMatrix (c • LinearMap.id) (Module.Basis.singleton (Fin 1) ℚ),
    Matrix.charpoly, Matrix.det_fin_one]
  simp [LinearMap.toMatrix_apply]

theorem quotient_charpoly (i : Fin 2) :
    (triangularStep i).quotientMap.charpoly = X - C (gradedEigenvalue i) := by
  calc
    _ = ((gradedEquiv i).conj (triangularStep i).quotientMap).charpoly :=
      (LinearEquiv.charpoly_conj (gradedEquiv i) (triangularStep i).quotientMap).symm
    _ = _ := by rw [quotient_conj, scalar_charpoly]

theorem triangular_charpoly :
    triangular.charpoly = (X - C (3 : ℚ)) * (X - C (5 : ℚ)) := by
  letI : Subsingleton (flag 0) := by
    change Subsingleton (⊥ : Submodule ℚ V)
    infer_instance
  let e : flag 2 ≃ₗ[ℚ] V := Submodule.topEquiv
  have hconj : e.conj (stageEnd (2 : Fin 3)) = triangular := by
    apply LinearMap.ext
    intro x
    rfl
  calc
    triangular.charpoly = (stageEnd (2 : Fin 3)).charpoly := by
      rw [← hconj]
      exact LinearEquiv.charpoly_conj e _
    _ = ∏ i : Fin 2, (triangularStep i).quotientMap.charpoly :=
      LinearMap.charpoly_eq_prod_graded_of_bottom_subsingleton
        (R := ℚ) (n := 2) (M := fun j : Fin 3 => flag j.val)
        stageEnd triangularStep (fun i => by
          change Module.Free ℚ (Graded i)
          infer_instance)
    _ = _ := by simp [quotient_charpoly, gradedEigenvalue, Fin.prod_univ_two]

example :
    (triangularStep (1 : Fin 2)).quotientMap
        (Submodule.Quotient.mk (coordinateVector 1 1) : Graded (1 : Fin 2)) =
      (Submodule.Quotient.mk (coordinateVector 1 5) : Graded (1 : Fin 2)) := by
  apply (gradedEquiv 1).injective
  simp [gradedEquiv_apply, quotient_coordinate_action, gradedEigenvalue,
    gradedCoordinate, coordinate, coordinateVector]

example : triangular.charpoly.coeff 0 = 15 := by
  norm_num [triangular_charpoly, Polynomial.coeff_mul]
example : triangular.charpoly.coeff 1 = -8 := by
  norm_num [triangular_charpoly, Polynomial.coeff_mul]

example : (0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)).charpoly = 1 :=
  LinearMap.charpoly_eq_one_of_subsingleton _

end MathlibExtTest.FiniteFiltration
