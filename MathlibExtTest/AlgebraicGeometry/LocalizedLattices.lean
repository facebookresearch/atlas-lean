/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.LocalizedLattices
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Concrete Z[t,1/2]-bounds: the upper one-step lattice contains1/2,
whereas the lower one-step lattice excludes1. This distinguishes the two
actual integral bounds; no lattice/Grassmannian provider is assumed.
-/

open MathlibExt.LinearAlgebra.LocalizedLattices

noncomputable section

private abbrev R := Polynomial ℤ

private def unitVector : Ambient R (2 : R) 1 := fun _ ↦ 1

private lemma unit_standard : unitVector ∈ standard R (2 : R) 1 := by
  refine LinearMap.mem_range.mpr ⟨fun _ ↦ 1, ?_⟩
  ext i
  change algebraMap R (FractionRing R (2 : R)) 1 = 1
  exact map_one _

example : (fun _ : Fin 1 ↦ IsLocalization.Away.invSelf
    (S := FractionRing R (2 : R)) (2 : R)) ∈
    upper R (2 : R) 1 1 := by
  apply Submodule.mem_map.mpr
  refine ⟨unitVector, unit_standard, ?_⟩
  ext i
  simp [scale, unitVector]

example : unitVector ∉ lower R (2 : R) 1 1 := by
  intro h
  obtain ⟨x, hx, hscale⟩ := Submodule.mem_map.mp h
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
  have hi := congrFun hscale (0 : Fin 1)
  simp only [scale, LinearMap.coe_mk, AddHom.coe_mk,
    standardMap, pow_one, unitVector] at hi
  change algebraMap R (FractionRing R (2 : R)) 2 *
    algebraMap R (FractionRing R (2 : R)) (z 0) = 1 at hi
  have htwo : (2 : R) ≠ 0 := by
    intro hzero
    have he := congrArg (Polynomial.evalRingHom (0 : ℤ)) hzero
    simp only [map_ofNat, map_zero] at he
    exact (by decide : (2 : ℤ) ≠ 0) he
  have hinj := IsLocalization.injective (FractionRing R (2 : R))
    (powers_le_nonZeroDivisors_of_noZeroDivisors htwo)
  have hz : (2 : R) * z 0 = 1 := hinj (by
    simpa only [map_mul, map_one] using hi)
  have hz0 := congrArg (Polynomial.evalRingHom (0 : ℤ)) hz
  simp only [map_mul, map_ofNat, map_one] at hz0
  exact (by norm_num : ¬ (2 : ℤ) ∣ 1) ⟨(Polynomial.evalRingHom (0 : ℤ)) (z 0), hz0.symm⟩
