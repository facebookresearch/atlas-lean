/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurve.ComponentGroup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open ModularCurve

/-- A difference of unit vectors lies in the character lattice. -/
example : Pi.single (0 : Fin 2) (1 : ℤ) - Pi.single 1 1 ∈
    characterLattice (Fin 2) :=
  single_sub_single_mem (0 : Fin 2) 1

/-- The same difference is not detected by the degree: its degree
vanishes, while a single unit vector has degree `1`. -/
example : degreeOn (Fin 2) (Pi.single (0 : Fin 2) (1 : ℤ)) = 1 :=
  degreeOn_single (Fin 2) (0 : Fin 2) 1

/-- The width pairing on `Fin 2` with unit widths is the dot product. -/
example (D D' : Fin 2 → ℤ) :
    widthPairing (fun _ => 1) D D' = ∑ x : Fin 2, D x * D' x := by
  simp [widthPairing_apply]

/-- The component group and its projection for unit widths on
`Fin 2`. -/
example : Module.Dual ℤ (characterLattice (Fin 2)) →ₗ[ℤ]
    componentGroup (fun _ : Fin 2 => 1) :=
  componentGroupProj _

/-! ### The cokernel of the Gram map on `Fin 2` -/

/-- The character lattice of `Fin 2`: the two values cancel. -/
private theorem mem_characterLattice_fin2 (x : Fin 2 → ℤ) :
    x ∈ characterLattice (Fin 2) ↔ x 1 = -x 0 := by
  rw [mem_characterLattice, Fin.sum_univ_two]
  omega

/-- The generator `(1, -1)` of the character lattice of `Fin 2`. -/
private def genFin2 : characterLattice (Fin 2) :=
  ⟨![1, -1], by simp [mem_characterLattice_fin2]⟩

/-- The value at index `0`, a functional on the character lattice. -/
private def evalFin2 : Module.Dual ℤ (characterLattice (Fin 2)) :=
  (LinearMap.proj 0).comp (characterLattice (Fin 2)).subtype

/-- With widths `e 0, e 1`, the Gram pairing on the character lattice of
`Fin 2` is `e 0 + e 1` times the product of the index-`0` values. -/
private theorem gramMap_fin2 (e : Fin 2 → ℕ) (x y : characterLattice (Fin 2)) :
    gramMap e x y = ((e 0 : ℤ) + e 1) * (x.1 0 * y.1 0) := by
  have hx := (mem_characterLattice_fin2 x.1).1 x.2
  have hy := (mem_characterLattice_fin2 y.1).1 y.2
  rw [gramMap_apply, Fin.sum_univ_two, hx, hy]
  ring

/-- The class of `n` times the index-`0` functional vanishes in the
cokernel exactly when `e 0 + e 1` divides `n`. -/
private theorem componentGroupProj_smul_evalFin2_eq_zero_iff (e : Fin 2 → ℕ) (n : ℤ) :
    componentGroupProj e (n • evalFin2) = 0 ↔ ((e 0 : ℤ) + e 1) ∣ n := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    have h := LinearMap.congr_fun hy genFin2
    rw [gramMap_fin2] at h
    simp [evalFin2, genFin2] at h
    exact ⟨y.1 0, by linarith⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k • genFin2, LinearMap.ext fun x => ?_⟩
    rw [gramMap_fin2]
    simp [evalFin2, genFin2]
    ring

/-- Unit widths: the class of the index-`0` functional has order `2`. -/
example : componentGroupProj (fun _ : Fin 2 => 1) evalFin2 ≠ 0 ∧
    componentGroupProj (fun _ : Fin 2 => 1) ((2 : ℤ) • evalFin2) = 0 := by
  refine ⟨?_, (componentGroupProj_smul_evalFin2_eq_zero_iff _ 2).2 (by norm_num)⟩
  simpa using (componentGroupProj_smul_evalFin2_eq_zero_iff (fun _ => 1) 1).not.2 (by norm_num)

/-- Zero widths: the Gram map vanishes and `n ↦ n • evalFin2` gives a
bijection from `ℤ` onto the cokernel, which is therefore infinite. -/
example : Function.Bijective
    fun n : ℤ => componentGroupProj (fun _ : Fin 2 => 0) (n • evalFin2) := by
  refine ⟨fun n m h => ?_, fun q => ?_⟩
  · have h0 : componentGroupProj (fun _ : Fin 2 => 0) ((n - m) • evalFin2) = 0 := by
      rw [sub_smul, map_sub]
      exact sub_eq_zero.2 h
    rw [componentGroupProj_smul_evalFin2_eq_zero_iff] at h0
    simpa [sub_eq_zero] using h0
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨f genFin2, congrArg (Submodule.Quotient.mk (p := _)) (LinearMap.ext fun x => ?_)⟩
    have hx : x = x.1 0 • genFin2 := by
      ext i
      fin_cases i <;> simp [genFin2, (mem_characterLattice_fin2 x.1).1 x.2]
    conv_rhs => rw [hx]
    simp [evalFin2, mul_comm]

example : Infinite (componentGroup (fun _ : Fin 2 => 0)) := by
  refine Infinite.of_injective (fun n : ℤ => componentGroupProj _ (n • evalFin2)) fun n m h => ?_
  have h0 : componentGroupProj (fun _ : Fin 2 => 0) ((n - m) • evalFin2) = 0 := by
    rw [sub_smul, map_sub]
    exact sub_eq_zero.2 h
  rw [componentGroupProj_smul_evalFin2_eq_zero_iff] at h0
  simpa [sub_eq_zero] using h0

/-- A character evaluated at constant weights is trivial. -/
example (a : characterLattice (Fin 2)) (c : Multiplicative ℤ) :
    CharacterLattice.evalHom a (fun _ => c) = 1 :=
  CharacterLattice.evalHom_const a c

/-- Permuting by the swap equivalence preserves the character
lattice. -/
example (a : characterLattice (Fin 2)) :
    (CharacterLattice.permMap (Equiv.swap (0 : Fin 2) 1) a : Fin 2 → ℤ) 0 =
      (a : Fin 2 → ℤ) 1 := by
  simp

/-! ### Correspondences -/

/-- Without a common row sum, `corrMapFun` leaves the character lattice: `diag(1, 0)` sends
`(1, -1)` to `(1, 0)`, of degree `1`. -/
example : CharacterLattice.corrMapFun (fun s s' : Fin 2 => ![![1, 0], ![0, 0]] s s') ![1, -1] =
      ![1, 0] ∧ (![1, 0] : Fin 2 → ℤ) ∉ characterLattice (Fin 2) := by
  refine ⟨?_, by simp [mem_characterLattice_fin2]⟩
  funext s'
  fin_cases s' <;> simp [Fin.sum_univ_two]

/-- With the common row sum `2`, `corrMap` sends `(1, -1)` to `(-1, 1)`. -/
example : (CharacterLattice.corrMap (fun s s' : Fin 2 => ![![0, 2], ![1, 1]] s s') 2
      (fun s => by fin_cases s <;> simp [Fin.sum_univ_two]) genFin2 : Fin 2 → ℤ) = ![-1, 1] := by
  funext s'
  fin_cases s' <;> simp [genFin2, Fin.sum_univ_two]
