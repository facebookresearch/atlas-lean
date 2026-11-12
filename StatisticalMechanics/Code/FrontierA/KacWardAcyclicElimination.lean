/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















import Code.FrontierA.KacWardGauge
import Code.Onsager.TorusDecoration
import Mathlib.Algebra.Ring.GeomSum

open scoped BigOperators

namespace StatMech.FrontierA

open Matrix



theorem kw_fourPort_even_iff_unique_trivalent_completion
    (b0 b1 b2 b3 : Fin 2) :
    b0 + b1 + b2 + b3 = 0 ↔
      ∃! y : Fin 3 -> Fin 2,
        StatMech.Onsager.ons_decChainEven b0 b1 b2 b3 y := by
  constructor
  · exact StatMech.Onsager.ons_decChain_existsUnique b0 b1 b2 b3
  · rintro ⟨y, hy, _⟩
    exact StatMech.Onsager.ons_decChainEven_port_even hy


noncomputable def kwNilpotentResolvent
    {Internal : Type*} [Fintype Internal] [DecidableEq Internal]
    (internal : Matrix Internal Internal ℂ) (nilpotenceIndex : ℕ) :
    Matrix Internal Internal ℂ :=
  ∑ k ∈ Finset.range nilpotenceIndex, internal ^ k

theorem kwNilpotentResolvent_mul
    {Internal : Type*} [Fintype Internal] [DecidableEq Internal]
    (internal : Matrix Internal Internal ℂ) (nilpotenceIndex : ℕ)
    (hpow : internal ^ nilpotenceIndex = 0) :
    kwNilpotentResolvent internal nilpotenceIndex * (1 - internal) = 1 := by
  rw [kwNilpotentResolvent, geom_sum_mul_neg, hpow, sub_zero]

theorem kw_mul_nilpotentResolvent
    {Internal : Type*} [Fintype Internal] [DecidableEq Internal]
    (internal : Matrix Internal Internal ℂ) (nilpotenceIndex : ℕ)
    (hpow : internal ^ nilpotenceIndex = 0) :
    (1 - internal) * kwNilpotentResolvent internal nilpotenceIndex = 1 := by
  rw [kwNilpotentResolvent, mul_neg_geom_sum, hpow, sub_zero]


noncomputable def kwInternalGadgetTransition
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ) :
    Matrix (External ⊕ Internal) (External ⊕ Internal) ℂ :=
  Matrix.fromBlocks external enter exit internal



noncomputable def kwEliminateAcyclicInternal
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ)
    (nilpotenceIndex : ℕ) : Matrix External External ℂ :=
  external + enter * kwNilpotentResolvent internal nilpotenceIndex * exit

theorem kw_one_sub_internalGadget
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ) :
    1 - kwInternalGadgetTransition external enter exit internal =
      Matrix.fromBlocks (1 - external) (-enter) (-exit) (1 - internal) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [kwInternalGadgetTransition, Matrix.one_apply]



theorem kw_det_eliminateAcyclicInternal
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ)
    (nilpotenceIndex : ℕ) (hpow : internal ^ nilpotenceIndex = 0) :
    (1 - kwInternalGadgetTransition external enter exit internal).det =
      (1 - kwEliminateAcyclicInternal external enter exit internal
        nilpotenceIndex).det := by
  let resolvent := kwNilpotentResolvent internal nilpotenceIndex
  letI : Invertible (1 - internal) :=
    ⟨resolvent,
      kwNilpotentResolvent_mul internal nilpotenceIndex hpow,
      kw_mul_nilpotentResolvent internal nilpotenceIndex hpow⟩
  rw [kw_one_sub_internalGadget, Matrix.det_fromBlocks₂₂]
  have hdetInternal : (1 - internal).det = 1 :=
    det_one_sub_eq_one_of_isNilpotent internal ⟨nilpotenceIndex, hpow⟩
  rw [hdetInternal, one_mul]
  have hinv : ⅟(1 - internal) = resolvent := rfl
  rw [hinv]
  congr 1
  unfold kwEliminateAcyclicInternal
  change (1 - external) - (-enter) * resolvent * (-exit) =
    1 - (external + enter *
      kwNilpotentResolvent internal nilpotenceIndex * exit)
  change (1 - external) - (-enter) * resolvent * (-exit) =
    1 - (external + enter * resolvent * exit)
  simp
  noncomm_ring

end StatMech.FrontierA
