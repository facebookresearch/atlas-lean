/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.TensorPower.DirectLimit
public import MathlibExt.Algebra.Colimit.Module
public import Mathlib.Order.Lattice
public meta import Lean.Elab.Tactic.Omega
public meta import Mathlib.Tactic.NormNum

/-!
# Incomparable stages, genuine eventual vanishing and empty tensor families

Two incomparable stages `(1,0)` and `(0,1)` map their coefficient classes to the common
stage `(1,1)`. The semiring is the natural numbers and the modules are additive monoids.
A second system has a nonzero tensor at `(0,0)` and kills it when the first coordinate
becomes positive. Finite-family and tensor-power vanishing are earned from that actual
transition, and the empty factor family retains its coefficient class.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped TensorProduct
open Module Module.DirectLimit

namespace DirectedStagesTests

-- These test-local priorities retain the exact native scalar dictionaries on ℕ tensor carriers.
local attribute [instance 10000] Semiring.toModule PiTensorProduct.instModule
  TensorProduct.instModule Module.DirectLimit.module

private abbrev I := ℕ × ℕ
private abbrev G (_ : I) := ℕ
private def constantMap (_i _j : I) (_h : _i ≤ _j) : ℕ →ₗ[ℕ] ℕ := LinearMap.id

private instance : DirectedSystem G (constantMap · · ·) where
  map_self {i} x := rfl
  map_map {k j i} hij hjk x := rfl

example : DirectedSystem (fun i : I => G i ⊗[ℕ] G i)
    (TensorProduct.diagonalTransition constantMap constantMap · · ·) := inferInstance

private abbrev a : I := (1, 0)
private abbrev b : I := (0, 1)
private abbrev c : I := (1, 1)

example : ¬ a ≤ b ∧ ¬ b ≤ a := by decide

example :
    TensorProduct.directLimitDiagonal constantMap constantMap
      (Module.DirectLimit.of ℕ I G constantMap a 2 ⊗ₜ[ℕ]
        Module.DirectLimit.of ℕ I G constantMap b 3) =
      TensorProduct.diagonalStageAt constantMap constantMap a b c
        (by decide) (by decide) (2 ⊗ₜ[ℕ] 3) := by
  rw [TensorProduct.directLimitDiagonal_tmul_of_of]
  exact LinearMap.congr_fun
    (TensorProduct.diagonalStage_eq constantMap constantMap a b c (by decide) (by decide))
    (2 ⊗ₜ[ℕ] 3)

example :
    (TensorProduct.directLimitDiagonal constantMap constantMap).symm
      (TensorProduct.diagonalStageAt constantMap constantMap a b c
        (by decide) (by decide) (2 ⊗ₜ[ℕ] 3)) =
      Module.DirectLimit.of ℕ I G constantMap a 2 ⊗ₜ[ℕ]
        Module.DirectLimit.of ℕ I G constantMap b 3 := by
  rw [← TensorProduct.diagonalStage_eq constantMap constantMap a b c (by decide) (by decide)]
  rw [← TensorProduct.directLimitDiagonal_tmul_of_of, LinearEquiv.symm_apply_apply]
  rfl

private def killedMap (i j : I) (_h : i ≤ j) : ℕ →ₗ[ℕ] ℕ :=
  if i.1 = 0 ∧ 0 < j.1 then 0 else LinearMap.id

private instance : DirectedSystem G (killedMap · · ·) where
  map_self {i} x := by
    by_cases hi : i.1 = 0 <;> simp [killedMap, hi]
  map_map {k j i} hij hjk x := by
    have h₁ : i.1 ≤ j.1 := hij.1
    have h₂ : j.1 ≤ k.1 := hjk.1
    by_cases hi : i.1 = 0
    · by_cases hj : j.1 = 0
      · by_cases hk : k.1 = 0
        · simp [killedMap, hi, hj, hk]
        · have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hk
          simp [killedMap, hi, hj, hkpos]
      · have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj
        have hkpos : 0 < k.1 := lt_of_lt_of_le hjpos h₂
        simp [killedMap, hi, hj, hjpos, hkpos]
    · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi
      have hjpos : 0 < j.1 := lt_of_lt_of_le hipos h₁
      have hkpos : 0 < k.1 := lt_of_lt_of_le hjpos h₂
      simp [killedMap, hi, ne_of_gt hjpos, hjpos, hkpos]

private abbrev start : I := (0, 0)
private abbrev later : I := (1, 0)
private def stageTensor : G start ⊗[ℕ] G start := 1 ⊗ₜ[ℕ] 1

example : stageTensor ≠ 0 := by
  intro h
  have h' := congrArg (TensorProduct.lid ℕ ℕ) h
  simp [stageTensor] at h'

private theorem stage_class_zero : Module.DirectLimit.of ℕ I G killedMap start 1 = 0 := by
  have h : Module.DirectLimit.of ℕ I G killedMap later
      (killedMap start later (by decide) (1 : G start)) =
      Module.DirectLimit.of ℕ I G killedMap start 1 := Module.DirectLimit.of_f
  simpa [killedMap, start, later] using h.symm

private theorem tensor_class_zero :
    TensorProduct.map (Module.DirectLimit.of ℕ I G killedMap start)
      (Module.DirectLimit.of ℕ I G killedMap start) stageTensor = 0 := by
  simp [stageTensor, stage_class_zero]

example : TensorProduct.map (killedMap start later (by decide))
    (killedMap start later (by decide)) stageTensor = 0 := by
  simp [stageTensor, killedMap, start, later]

example : ∃ j : I, ∃ h : start ≤ j,
    TensorProduct.map (killedMap start j h) (killedMap start j h) stageTensor = 0 :=
  TensorProduct.exists_eq_zero_of_map_to_directLimit_diagonal_eq_zero
    killedMap killedMap stageTensor tensor_class_zero

-- Even a finite family uses one common later stage; the family is genuinely nonzero initially.
example : ∃ j : I, ∃ h : start ≤ j, ∀ q : Fin 2,
    killedMap start j h (if q = 0 then 1 else 2) = 0 := by
  apply Module.DirectLimit.of.zero_exact_finite_family killedMap
    (fun q : Fin 2 => if q = 0 then 1 else 2)
  intro q
  split_ifs
  · exact stage_class_zero
  · have h : Module.DirectLimit.of ℕ I G killedMap later
        (killedMap start later (by decide) (2 : G start)) =
        Module.DirectLimit.of ℕ I G killedMap start 2 := Module.DirectLimit.of_f
    simpa [killedMap, start, later] using h.symm

private abbrev emptyFamily (_ : Fin 0) (_ : I) := ℕ
private def emptyTransition (_ : Fin 0) : ∀ i j : I, i ≤ j → ℕ →ₗ[ℕ] ℕ := constantMap
private instance (q : Fin 0) : DirectedSystem (emptyFamily q) (emptyTransition q · · ·) := by
  exact inferInstanceAs (DirectedSystem G (constantMap · · ·))

example : DirectedSystem
    (fun i : I => G i ⊗[ℕ] (⨂[ℕ] q : Fin 0, emptyFamily q i))
    (TensorProduct.finiteDiagonalTransition constantMap emptyTransition · · ·) := inferInstance

-- The empty factor family retains the genuine coefficient class rather than becoming zero.
example :
    TensorProduct.directLimitFinite constantMap emptyTransition
      (Module.DirectLimit.of ℕ I G constantMap a 4 ⊗ₜ[ℕ]
        PiTensorProduct.tprod ℕ (fun q : Fin 0 => nomatch q)) =
      Module.DirectLimit.of ℕ I
        (fun i : I => G i ⊗[ℕ] (⨂[ℕ] q : Fin 0, emptyFamily q i))
        (TensorProduct.finiteDiagonalTransition constantMap emptyTransition) a
          (4 ⊗ₜ[ℕ] PiTensorProduct.tprod ℕ (fun q : Fin 0 => nomatch q)) :=
  TensorProduct.directLimitFinite_of_tprod constantMap emptyTransition a 4
    (fun q : Fin 0 => nomatch q)

private def constantLimitValue : Module.DirectLimit G constantMap →ₗ[ℕ] ℕ :=
  Module.DirectLimit.lift ℕ I G constantMap (fun _ => LinearMap.id)
    (fun _ _ _ _ => rfl)

private def emptyValue :
    Module.DirectLimit G constantMap ⊗[ℕ]
      (⨂[ℕ] q : Fin 0, Module.DirectLimit (emptyFamily q) (emptyTransition q)) →ₗ[ℕ] ℕ :=
  (TensorProduct.lid ℕ ℕ).toLinearMap.comp
    (TensorProduct.map constantLimitValue
      (PiTensorProduct.isEmptyEquiv (R := ℕ) (Fin 0)).toLinearMap)

private theorem empty_coefficient_value :
    emptyValue
      (Module.DirectLimit.of ℕ I G constantMap a 4 ⊗ₜ[ℕ]
        PiTensorProduct.tprod ℕ (fun q : Fin 0 => nomatch q)) = 4 := by
  simp [emptyValue, constantLimitValue]

example :
    (Module.DirectLimit.of ℕ I G constantMap a 4 ⊗ₜ[ℕ]
      PiTensorProduct.tprod ℕ (fun q : Fin 0 => nomatch q) :
        Module.DirectLimit G constantMap ⊗[ℕ]
          (⨂[ℕ] q : Fin 0, Module.DirectLimit (emptyFamily q) (emptyTransition q))) ≠ 0 := by
  intro h
  have h' := congrArg emptyValue h
  rw [empty_coefficient_value, map_zero] at h'
  norm_num at h'

example : DirectedSystem (fun i : I => TensorPower ℕ 2 (G i))
    (TensorPower.directedTransition constantMap 1 · · ·) := inferInstance

example :
    (TensorPower.directLimit constantMap 1).symm
      (Module.DirectLimit.of ℕ I (fun i => TensorPower ℕ 2 (G i))
        (TensorPower.directedTransition constantMap 1) a
          (PiTensorProduct.tprod ℕ (fun q : Fin 2 => if q = 0 then 2 else 3))) =
      PiTensorProduct.tprod ℕ (fun q : Fin 2 =>
        Module.DirectLimit.of ℕ I G constantMap a (if q = 0 then 2 else 3)) :=
  TensorPower.directLimit_symm_of_tprod constantMap 1 a
    (fun q : Fin 2 => if q = 0 then 2 else 3)

private def nativePowerElement : TensorPower ℕ 2 (G start) :=
  PiTensorProduct.tprod ℕ (fun _ : Fin 2 => 1)

private def nativePowerValue : TensorPower ℕ 2 ℕ →ₗ[ℕ] ℕ :=
  (TensorProduct.lid ℕ ℕ).toLinearMap.comp
    ((TensorProduct.map
      (PiTensorProduct.subsingletonEquiv (R := ℕ) (s := fun _ : Fin 1 => ℕ) 0).toLinearMap
      (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp
      (PiTensorProduct.finSnocEquiv ℕ 1 (fun _ : Fin 2 => ℕ)).toLinearMap)

example : nativePowerElement ≠ 0 := by
  intro h
  have h' := congrArg nativePowerValue h
  simp [nativePowerValue, nativePowerElement] at h'

example : ∃ j : I, ∃ h : start ≤ j,
    TensorPower.directedTransition killedMap 1 start j h nativePowerElement = 0 := by
  apply TensorPower.exists_eq_zero_of_map_to_directLimit_eq_zero killedMap 1 nativePowerElement
  have h := PiTensorProduct.map_tprod
    (fun _ : Fin 2 => Module.DirectLimit.of ℕ I G killedMap start)
    (fun _ : Fin 2 => (1 : ℕ))
  rw [nativePowerElement]
  change PiTensorProduct.map (fun _ : Fin 2 => Module.DirectLimit.of ℕ I G killedMap start)
    (PiTensorProduct.tprod ℕ (fun _ : Fin 2 => (1 : ℕ))) = 0
  rw [h]
  have hzero : (fun _ : Fin 2 => Module.DirectLimit.of ℕ I G killedMap start 1) =
      (fun _ => (0 : Module.DirectLimit G killedMap)) := by
    funext q
    exact stage_class_zero
  rw [hzero]
  exact (PiTensorProduct.tprod ℕ).map_coord_zero (0 : Fin 2) rfl

end DirectedStagesTests
