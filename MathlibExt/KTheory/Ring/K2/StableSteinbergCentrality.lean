/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergRootNormalization
public import MathlibExt.KTheory.Ring.K2.StableSteinbergRootInjectivity

/-! # Stable Steinberg kernel centrality

The kernel of `toStableE` is central.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

open scoped commutatorElement

universe u

variable {R : Type u} [Ring R]

private lemma commute_of_mem_ker_normalizer_injOn
    {H : Subgroup (StableSteinberg R)} {z y : StableSteinberg R}
    (hz : z ∈ MonoidHom.ker (toStableE (R := R)))
    (hNorm : z ∈ Subgroup.normalizer H)
    (hy : y ∈ H)
    (hinj : Set.InjOn (toStableE (R := R)) (H : Set (StableSteinberg R))) :
    Commute z y := by
  have hz_one : toStableE (R := R) z = 1 :=
    (MonoidHom.mem_ker.mp hz)
  have hconj_mem : z * y * z⁻¹ ∈ H := by
    have h := (Subgroup.mem_normalizer_iff.mp hNorm) y
    exact h.mp hy
  have h_toStableE_eq : toStableE (R := R) (z * y * z⁻¹) = toStableE (R := R) y := by
    calc toStableE (R := R) (z * y * z⁻¹)
        = toStableE (R := R) z * toStableE (R := R) y * (toStableE (R := R) z)⁻¹ := by
          simp
      _ = (1 : StableE R) * toStableE (R := R) y * (1 : StableE R)⁻¹ := by
          rw [hz_one]
      _ = toStableE (R := R) y := by
          simp
  have h_eq : z * y * z⁻¹ = y :=
    hinj hconj_mem hy h_toStableE_eq
  have h_comm : z * y = y * z := by
    calc z * y = (z * y * z⁻¹) * z := by
          rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
      _ = y * z := by rw [h_eq]
  exact h_comm

/-- The kernel of `toStableE` is contained in the center. -/
public theorem ker_toStableE_le_center {R : Type u} [Ring R] :
    MonoidHom.ker (toStableE (R := R)) ≤ Subgroup.center (StableSteinberg R) := by
  intro z hz
  obtain ⟨m, hm⟩ := exists_mem_finiteStage (R := R) z
  have h_comm_gen : ∀ (i j : ℕ) (hij : i ≠ j) (a : R),
      Commute z (x (R := R) i j hij a) := by
    intro i j hij a
    let n := max m (max i j + 1)
    have hm_le : m ≤ n := Nat.le_max_left m (max i j + 1)
    have hz_n : z ∈ finiteStage (R := R) n :=
      finiteStage_mono hm_le hm
    have hi_lt_max : i ≤ max i j := Nat.le_max_left i j
    have hj_lt_max : j ≤ max i j := Nat.le_max_right i j
    have h_max_lt : max i j < max i j + 1 := Nat.lt_succ_self (max i j)
    have hi_lt_succ : i < max i j + 1 :=
      Nat.lt_of_le_of_lt hi_lt_max h_max_lt
    have hj_lt_succ : j < max i j + 1 :=
      Nat.lt_of_le_of_lt hj_lt_max h_max_lt
    have h_succ_le : max i j + 1 ≤ n := Nat.le_max_right m (max i j + 1)
    have hi_lt_n : i < n := Nat.lt_of_lt_of_le hi_lt_succ h_succ_le
    have hj_lt_n : j < n := Nat.lt_of_lt_of_le hj_lt_succ h_succ_le
    have hi_n : i ≠ n := Nat.ne_of_lt hi_lt_n
    have hn_j : n ≠ j := Ne.symm (Nat.ne_of_lt hj_lt_n)
    let u := x (R := R) i n hi_n a
    let v := x (R := R) n j hn_j (1 : R)
    have hu_mem : u ∈ lastColumnSubgroup (R := R) n :=
      x_mem_lastColumnSubgroup hi_lt_n
    have hv_mem : v ∈ lastRowSubgroup (R := R) n :=
      x_mem_lastRowSubgroup hj_lt_n
    have hNormCol : z ∈ Subgroup.normalizer (lastColumnSubgroup (R := R) n) :=
      (finiteStage_le_normalizer_lastColumnSubgroup (R := R) n) hz_n
    have hNormRow : z ∈ Subgroup.normalizer (lastRowSubgroup (R := R) n) :=
      (finiteStage_le_normalizer_lastRowSubgroup (R := R) n) hz_n
    have hinjCol : Set.InjOn (toStableE (R := R))
        (lastColumnSubgroup (R := R) n : Set (StableSteinberg R)) :=
      toStableE_injOn_lastColumnSubgroup (R := R) n
    have hinjRow : Set.InjOn (toStableE (R := R))
        (lastRowSubgroup (R := R) n : Set (StableSteinberg R)) :=
      toStableE_injOn_lastRowSubgroup (R := R) n
    have hCommU : Commute z u :=
      commute_of_mem_ker_normalizer_injOn hz hNormCol hu_mem hinjCol
    have hCommV : Commute z v :=
      commute_of_mem_ker_normalizer_injOn hz hNormRow hv_mem hinjRow
    have hchev : ⁅u, v⁆ = x (R := R) i j hij a := by
      have h := x_chev (R := R) i n j hi_n hn_j hij a (1 : R)
      simp only [mul_one] at h
      exact h
    have hCommU_inv : Commute z u⁻¹ := hCommU.inv_right
    have hCommV_inv : Commute z v⁻¹ := hCommV.inv_right
    have hCommUV : Commute z (u * v) := hCommU.mul_right hCommV
    have hCommUV_invU : Commute z (u * v * u⁻¹) := hCommUV.mul_right hCommU_inv
    have hCommCommutator : Commute z (u * v * u⁻¹ * v⁻¹) :=
      hCommUV_invU.mul_right hCommV_inv
    have hCommutatorComm : Commute z ⁅u, v⁆ := by
      rw [commutatorElement_def]
      exact hCommCommutator
    rw [hchev] at hCommutatorComm
    exact hCommutatorComm
  have h_all : ∀ (s : SteinbergGenerator R),
      (PresentedGroup.of s : StableSteinberg R) ∈ Subgroup.centralizer {z} := by
    intro s
    cases s with
    | mk i j hij a =>
      have hComm := h_comm_gen i j hij a
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hComm.symm
  have h_mem : ∀ (g : StableSteinberg R), g ∈ Subgroup.centralizer {z} := by
    intro g
    exact PresentedGroup.generated_by (steinbergRelations R)
      (Subgroup.centralizer {z}) h_all g
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ Subgroup.centralizer {z} := h_mem y
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  exact hy

public theorem lastColumnSubgroup_inf_ker_toStableE_eq_bot {R : Type u} [Ring R] (n : ℕ) :
    lastColumnSubgroup (R := R) n ⊓ MonoidHom.ker (toStableE (R := R)) = ⊥ := by
  ext x
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · rintro ⟨hxCol, hxKer⟩
    have hOne : (1 : StableSteinberg R) ∈ lastColumnSubgroup (R := R) n :=
      (lastColumnSubgroup (R := R) n).one_mem
    have hEq : toStableE (R := R) x = toStableE (R := R) 1 := by
      rw [hxKer, MonoidHom.map_one]
    exact toStableE_injOn_lastColumnSubgroup (R := R) n hxCol hOne hEq
  · intro hx
    subst hx
    exact ⟨(lastColumnSubgroup (R := R) n).one_mem, by simp⟩

public theorem lastRowSubgroup_inf_ker_toStableE_eq_bot {R : Type u} [Ring R] (n : ℕ) :
    lastRowSubgroup (R := R) n ⊓ MonoidHom.ker (toStableE (R := R)) = ⊥ := by
  ext x
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · rintro ⟨hxRow, hxKer⟩
    have hOne : (1 : StableSteinberg R) ∈ lastRowSubgroup (R := R) n :=
      (lastRowSubgroup (R := R) n).one_mem
    have hEq : toStableE (R := R) x = toStableE (R := R) 1 := by
      rw [hxKer, MonoidHom.map_one]
    exact toStableE_injOn_lastRowSubgroup (R := R) n hxRow hOne hEq
  · intro hx
    subst hx
    exact ⟨(lastRowSubgroup (R := R) n).one_mem, by simp⟩

end StableSteinberg

end AlgebraicKTheory

end
