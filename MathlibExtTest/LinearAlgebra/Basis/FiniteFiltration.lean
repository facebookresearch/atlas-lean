/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.Basis.FiniteFiltration
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The two-dimensional coordinate flag

The rational flag is 0 ⊂ {(a,0)} ⊂ ℚ². Its two graded coordinates are evaluation
at the corresponding coordinate. The first assembled vector is (1,0), while
the second vector is checked through its chosen quotient class.
-/

@[expose] public section

noncomputable section
namespace MathlibExtTest.FiniteFiltration

abbrev V := Fin 2 → ℚ
abbrev GradeIndex (_ : ℕ) := Fin 1

def flag : ℕ → Submodule ℚ V
  | 0 => ⊥
  | 1 => LinearMap.ker (LinearMap.proj (1 : Fin 2))
  | _ + 2 => ⊤

theorem flag_le (i : Fin 2) : flag i.val ≤ flag (i.val + 1) := by
  fin_cases i <;> simp [flag]

abbrev Graded (i : Fin 2) :=
  flag (i.val + 1) ⧸ (flag i.val).comap (flag (i.val + 1)).subtype

def coordinate (i : Fin 2) : flag (i.val + 1) →ₗ[ℚ] ℚ :=
  (LinearMap.proj i).comp (flag (i.val + 1)).subtype

def coordinateVector (i : Fin 2) (c : ℚ) : flag (i.val + 1) :=
  ⟨Pi.single i c, by fin_cases i <;> simp [flag]⟩

theorem lower_le_coordinate_ker (i : Fin 2) :
    (flag i.val).comap (flag (i.val + 1)).subtype ≤ (coordinate i).ker := by
  intro x hx
  change (x : V) ∈ flag i.val at hx
  change coordinate i x = 0
  fin_cases i
  · change (x : V) = 0 at hx
    change (x : V) 0 = 0
    exact congrFun hx 0
  · change (x : V) 1 = 0 at hx
    change (x : V) 1 = 0
    exact hx

def gradedCoordinate (i : Fin 2) : Graded i →ₗ[ℚ] ℚ :=
  ((flag i.val).comap (flag (i.val + 1)).subtype).liftQ
    (coordinate i) (lower_le_coordinate_ker i)

theorem gradedCoordinate_zero (i : Fin 2) :
    ∀ x : Graded i, gradedCoordinate i x = 0 → x = 0 := by
  intro x
  refine Submodule.Quotient.induction_on
    ((flag i.val).comap (flag (i.val + 1)).subtype) x ?_
  intro v hv
  have hcoord : coordinate i v = 0 := by simpa [gradedCoordinate] using hv
  apply (Submodule.Quotient.mk_eq_zero
    ((flag i.val).comap (flag (i.val + 1)).subtype)).mpr
  change (v : V) ∈ flag i.val
  fin_cases i
  · have h0 : (v : V) 0 = 0 := hcoord
    have h1 : (v : V) 1 = 0 := v.property
    have hz : (v : V) = 0 := by
      funext j
      fin_cases j
      · exact h0
      · exact h1
    change (v : V) = 0
    exact hz
  · change (v : V) 1 = 0
    exact hcoord

theorem gradedCoordinate_bijective (i : Fin 2) :
    Function.Bijective (gradedCoordinate i) := by
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply gradedCoordinate_zero i
    simp only [map_sub, hxy, sub_self]
  · intro c
    refine ⟨Submodule.Quotient.mk (coordinateVector i c), ?_⟩
    simp [gradedCoordinate, coordinate, coordinateVector]

def gradedEquiv (i : Fin 2) : Graded i ≃ₗ[ℚ] ℚ :=
  LinearEquiv.ofBijective (gradedCoordinate i) (gradedCoordinate_bijective i)

theorem gradedEquiv_apply (i : Fin 2) (x : Graded i) :
    gradedEquiv i x = gradedCoordinate i x := rfl

instance gradedFree (i : Fin 2) : Module.Free ℚ (Graded i) :=
  Module.Free.of_equiv (gradedEquiv i).symm

instance gradedFinite (i : Fin 2) : Module.Finite ℚ (Graded i) :=
  Module.Finite.equiv (gradedEquiv i).symm

def gradedBasis (i : Fin 2) : Module.Basis (GradeIndex i.val) ℚ (Graded i) :=
  (Module.Basis.singleton (Fin 1) ℚ).map (gradedEquiv i).symm

@[simp]
theorem gradedBasis_apply (i : Fin 2) (a : Fin 1) :
    gradedBasis i a = Submodule.Quotient.mk (coordinateVector i 1) := by
  apply (gradedEquiv i).injective
  rw [gradedBasis, Module.Basis.map_apply, Module.Basis.singleton_apply]
  rw [LinearEquiv.apply_symm_apply]
  change 1 = gradedCoordinate i (Submodule.Quotient.mk (coordinateVector i 1))
  simp [gradedCoordinate, coordinate, coordinateVector]

def zeroBasis : Module.Basis (Module.Basis.FiltrationIndex GradeIndex 0) ℚ (flag 0) :=
  Module.Basis.ofFiltrationStage flag rfl GradeIndex 0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

def firstBasis : Module.Basis (Module.Basis.FiltrationIndex GradeIndex 1) ℚ (flag 1) :=
  Module.Basis.ofFiltrationStage flag rfl GradeIndex 1
    (fun i => flag_le i.castSucc) (fun i => gradedBasis i.castSucc)

def secondBasis : Module.Basis (Module.Basis.FiltrationIndex GradeIndex 2) ℚ (flag 2) :=
  Module.Basis.ofFiltrationStage flag rfl GradeIndex 2 flag_le gradedBasis

def ambientBasis : Module.Basis (Module.Basis.FiltrationIndex GradeIndex 2) ℚ V :=
  Module.Basis.ofFiltration flag rfl GradeIndex 2 flag_le gradedBasis rfl

example : Fintype.card (Module.Basis.FiltrationIndex GradeIndex 0) = 0 := by
  simp [Module.Basis.FiltrationIndex]
example (x : flag 0) : zeroBasis.repr x = 0 := by
  ext i
  exact Fin.elim0 i.1

-- The public castSucc formula retains the nonempty first grade.
example :
    ((secondBasis ⟨(0 : Fin 1).castSucc, 0⟩ : flag 2) : V) =
      (firstBasis ⟨(0 : Fin 1), 0⟩ : flag 1) := by
  simpa only [secondBasis, firstBasis] using
    (Module.Basis.ofFiltrationStage_castSucc
      flag rfl GradeIndex 1 flag_le gradedBasis (0 : Fin 1) (0 : Fin 1))

-- Both grades are nonzero; the second test detects an incorrect chosen quotient.
example (i : Fin 2) :
    (Submodule.Quotient.mk
        (Module.Basis.ofFiltrationStageVector flag rfl GradeIndex 2 flag_le gradedBasis i 0) :
      Graded i) =
      (Submodule.Quotient.mk (coordinateVector i 1) : Graded i) := by
  exact (Module.Basis.ofFiltrationStageVector_mk
    flag rfl GradeIndex 2 flag_le gradedBasis i (0 : Fin 1)).trans
      (gradedBasis_apply i (0 : Fin 1))

theorem first_vector :
    ((secondBasis ⟨(0 : Fin 2), 0⟩ : flag 2) : V) = Pi.single 0 1 := by
  have h := Module.Basis.ofFiltrationStageVector_mk
    flag rfl GradeIndex 2 flag_le gradedBasis (0 : Fin 2) (0 : Fin 1)
  rw [gradedBasis_apply] at h
  have hmem := (Submodule.Quotient.eq _).mp h
  have hz :
      ((Module.Basis.ofFiltrationStageVector flag rfl GradeIndex 2 flag_le gradedBasis 0 0 :
          flag 1) : V) - Pi.single 0 1 = 0 := by
    change
      ((Module.Basis.ofFiltrationStageVector flag rfl GradeIndex 2 flag_le gradedBasis 0 0 :
        flag 1) : V) - Pi.single 0 1 ∈ (⊥ : Submodule ℚ V) at hmem
    exact (Submodule.mem_bot ℚ).mp hmem
  simpa only [secondBasis, Module.Basis.ofFiltrationStageVector] using sub_eq_zero.mp hz

example : ambientBasis ⟨(0 : Fin 2), 0⟩ = Pi.single 0 1 := by
  exact (Module.Basis.ofFiltration_apply
    flag rfl GradeIndex 2 flag_le gradedBasis rfl ⟨(0 : Fin 2), (0 : Fin 1)⟩).trans first_vector

theorem flag_zero : flag 0 = ⊥ := rfl
theorem flag_two_top : flag 2 = ⊤ := rfl

-- Default simp compares the two public constructors on the proper nonempty flag.
example (i : Fin 1) (a : Fin 1) :
    ((Module.Basis.ofFiltrationStage (R := ℚ) (M := V)
        flag flag_zero GradeIndex 2 flag_le gradedBasis ⟨i.castSucc, a⟩ : flag 2) : V) =
      ((Module.Basis.ofFiltrationStage (R := ℚ) (M := V)
        flag flag_zero GradeIndex 1 (fun j => flag_le j.castSucc)
          (fun j => gradedBasis j.castSucc) ⟨i, a⟩ : flag 1) : V) ∧
    Module.Basis.ofFiltration (R := ℚ) (M := V)
        flag flag_zero GradeIndex 2 flag_le gradedBasis flag_two_top ⟨i.castSucc, a⟩ =
      ((Module.Basis.ofFiltrationStage (R := ℚ) (M := V)
        flag flag_zero GradeIndex 2 flag_le gradedBasis ⟨i.castSucc, a⟩ : flag 2) : V) := by
  simp

end MathlibExtTest.FiniteFiltration
