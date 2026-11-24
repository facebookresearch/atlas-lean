/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.CokernelLengthComposition

/-!
# Literal pivot elimination on arbitrary module blocks

The pivot is nonzero, with no unit-pivot premise. The actual elimination map
and Schur map retain the original off-diagonal maps. Their composition and
injectivity are earned from the actual module operations. These are the
arbitrary-size prerequisites for singular determinant/cokernel length.
-/

@[expose] public section
noncomputable section

universe u v

namespace LinearMap

variable {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]

/-- The original pivot block acting on the full module R × N. -/
def pivotBlock (a : R) (r : N →ₗ[R] R) (c : R →ₗ[R] N) (B : N →ₗ[R] N) :
    R × N →ₗ[R] R × N :=
  (a • LinearMap.fst R R N + r.comp (LinearMap.snd R R N)).prod
    (c.comp (LinearMap.fst R R N) + B.comp (LinearMap.snd R R N))

/-- The literal lower elimination map, with the original nonunit pivot. -/
def pivotElimination (a : R) (c : R →ₗ[R] N) : R × N →ₗ[R] R × N :=
  (LinearMap.fst R R N).prod
    (-(c.comp (LinearMap.fst R R N)) + a • LinearMap.snd R R N)

/-- The actual Schur block; the full original off-diagonal product remains. -/
def pivotSchur (a : R) (r : N →ₗ[R] R) (c : R →ₗ[R] N) (B : N →ₗ[R] N) : N →ₗ[R] N :=
  a • B - c.comp r

/-- Actual pivot elimination produces the original upper block map with
the full Schur block, without inverting the pivot. -/
theorem pivotElimination_comp (a : R) (r : N →ₗ[R] R) (c : R →ₗ[R] N) (B : N →ₗ[R] N) :
    (pivotElimination a c).comp (pivotBlock a r c B) =
      (a • LinearMap.fst R R N + r.comp (LinearMap.snd R R N)).prod
        ((pivotSchur a r c B).comp (LinearMap.snd R R N)) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · rfl
  · change -(c (a * x + r y)) + a • (c x + B y) = a • B y - c (r y)
    have hc : c (a * x) = a • c x := c.map_smul a x
    rw [map_add, hc, smul_add]
    abel

/-- A nonzero pivot earns injectivity of the actual elimination map on
every torsion-free module; a unit or finite-rank premise is unnecessary. -/
theorem pivotElimination_injective [NoZeroSMulDivisors R N] (a : R) (ha : a ≠ 0)
    (c : R →ₗ[R] N) : Function.Injective (pivotElimination a c) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨x, y⟩ h
  have hx : x = 0 := congrArg Prod.fst h
  have hy : -(c x) + a • y = 0 := congrArg Prod.snd h
  rw [hx, map_zero, neg_zero, zero_add] at hy
  have hy0 : y = 0 := (eq_zero_or_eq_zero_of_smul_eq_zero hy).resolve_left ha
  exact Prod.ext hx hy0

/-- Injectivity of the original block and its nonzero pivot earns the full
Schur block's injectivity by clearing that pivot in the actual source vector. -/
theorem pivotSchur_injective [NoZeroSMulDivisors R N]
    (a : R) (ha : a ≠ 0) (r : N →ₗ[R] R) (c : R →ₗ[R] N) (B : N →ₗ[R] N)
    (hA : Function.Injective (pivotBlock a r c B)) : Function.Injective (pivotSchur a r c B) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hzero : pivotBlock a r c B (-r y, a • y) = 0 := by
    apply Prod.ext
    · change a * (-r y) + r (a • y) = 0
      rw [map_smul]
      simp
    · change c (-r y) + B (a • y) = 0
      rw [map_neg, map_smul]
      have hs : a • B y = c (r y) := sub_eq_zero.mp hy
      rw [hs, neg_add_cancel]
  have hv : (-r y, a • y) = (0, 0) := hA (hzero.trans (pivotBlock a r c B).map_zero.symm)
  have hy0 : a • y = 0 := congrArg Prod.snd hv
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hy0).resolve_left ha

/-- The actual elimination map has precisely the full cokernel length of
its lower scalar block. The proof uses actual product changes of basis and
the upper block exact sequence, retaining nonunit pivots. -/
theorem length_coker_pivotElimination (a : R) (c : R →ₗ[R] N) :
    Module.length R ((R × N) ⧸ (pivotElimination a c).range) =
      Module.length R (N ⧸ (a • (LinearMap.id : N →ₗ[R] N)).range) := by
  let e := LinearEquiv.prodComm R R N
  let E := pivotElimination a c
  let H : N × R →ₗ[R] N × R :=
    ((a • (LinearMap.id : N →ₗ[R] N)).comp (LinearMap.fst R N R) +
      (-c).comp (LinearMap.snd R N R)).prod (LinearMap.snd R N R)
  have he : (e.toLinearMap.comp E).comp e.symm.toLinearMap = H := by
    apply LinearMap.ext
    rintro ⟨y, x⟩
    apply Prod.ext
    · change -c x + a • y = a • y + -c x
      exact add_comm _ _
    · rfl
  have hpost := length_coker_postcompose_equiv E e
  have hpre := length_coker_precompose_equiv (e.toLinearMap.comp E) e.symm
  have hchange : Module.length R ((R × N) ⧸ E.range) =
      Module.length R ((N × R) ⧸ H.range) := by
    rw [he] at hpre
    exact hpost.symm.trans hpre.symm
  have hblock := length_coker_upper_block_of_injective
    (a • (LinearMap.id : N →ₗ[R] N)) (-c) (LinearMap.id : R →ₗ[R] R)
    (fun x y h => h)
  have hzero : Module.length R (R ⧸ (LinearMap.id : R →ₗ[R] R).range) = 0 := by
    rw [LinearMap.range_eq_top.mpr Function.surjective_id]
    exact Module.length_eq_zero
  rw [hzero, add_zero] at hblock
  exact hchange.trans hblock

/-- Full pivot elimination earns the all-module cokernel length relation
needed by determinant induction. Injectivity is derived for the actual
elimination and Schur maps; no finite-length or norm/order equality premise
is introduced. -/
theorem length_coker_pivot_relation [NoZeroSMulDivisors R N]
    (a : R) (ha : a ≠ 0) (r : N →ₗ[R] R) (c : R →ₗ[R] N) (B : N →ₗ[R] N)
    (hA : Function.Injective (pivotBlock a r c B)) :
    Module.length R ((R × N) ⧸ (pivotBlock a r c B).range) +
        Module.length R (N ⧸ (a • (LinearMap.id : N →ₗ[R] N)).range) =
      Module.length R (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) +
        Module.length R (N ⧸ (pivotSchur a r c B).range) := by
  have hcomp := length_coker_comp_of_injective (pivotBlock a r c B) (pivotElimination a c)
    (pivotElimination_injective a ha c)
  rw [length_coker_pivotElimination a c] at hcomp
  have hs := pivotSchur_injective a ha r c B hA
  have hupper := length_coker_upper_block_of_injective
    (a • (LinearMap.id : R →ₗ[R] R)) r (pivotSchur a r c B) hs
  have hproduct : (pivotElimination a c).comp (pivotBlock a r c B) =
      ((a • (LinearMap.id : R →ₗ[R] R)).comp (LinearMap.fst R R N) +
        r.comp (LinearMap.snd R R N)).prod ((pivotSchur a r c B).comp (LinearMap.snd R R N)) :=
    pivotElimination_comp a r c B
  rw [hproduct] at hcomp
  exact hcomp.symm.trans hupper

end LinearMap
