/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
import CSLibExt.MachineLearning.Clustering.Kleinberg
import Mathlib.Data.Fin.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Setoid.Partition
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Cslib.MachineLearning.Clustering

/-! Independent clients for the Kleinberg interface. -/

private def p0 : Fin 2 := ⟨0, by decide⟩
private def p1 : Fin 2 := ⟨1, by decide⟩
private def q0 : Fin 3 := ⟨0, by decide⟩
private def q1 : Fin 3 := ⟨1, by decide⟩
private def q2 : Fin 3 := ⟨2, by decide⟩

private noncomputable def unit2 : Dissimilarity 2 where
  toFun := fun i j => if i = j then 0 else 1
  symm := fun i j => by
    show (if i = j then (0 : Real) else 1) = (if j = i then 0 else 1)
    by_cases h : i = j
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · have k : ¬ j = i := fun kk => h kk.symm
      rw [ite_eq_right h, ite_eq_right k]
  diag := fun _ => by exact ite_eq_left rfl
  pos := fun i j hne => by rw [ite_eq_right hne]; exact zero_lt_one

private theorem unit2_apply (i j : Fin 2) :
    unit2.toFun i j = if i = j then (0 : Real) else 1 := rfl

theorem unit2_off : unit2.toFun p0 p1 = 1 := by
  rw [unit2_apply, ite_eq_right (by decide : p0 ≠ p1)]

theorem unit2_scale_two :
    (Dissimilarity.scale 2 unit2 2 (lt_trans zero_lt_one one_lt_two)).toFun p0 p1 = 2 := by
  rw [Dissimilarity.scale_apply, unit2_off, mul_one]

theorem gamma_half_top :
    IsGammaTransform 2 ⊤ unit2
      (Dissimilarity.scale 2 unit2 (1 / 2 : Real) (by norm_num)) := by
  constructor
  · intro i j _
    rw [Dissimilarity.scale_apply, unit2_apply]
    by_cases h : i = j
    · simp [h]
    · rw [ite_eq_right h, mul_one]; norm_num
  · intro i j hn
    exact False.elim (hn trivial)

theorem gamma_double_bot :
    IsGammaTransform 2 ⊥ unit2
      (Dissimilarity.scale 2 unit2 (2 : Real) (by norm_num)) := by
  constructor
  · intro i j hb
    have heq : i = j := by simpa using hb
    rw [Dissimilarity.scale_apply, unit2_apply, ite_eq_left heq]
    simp
  · intro i j hn
    rw [Dissimilarity.scale_apply, unit2_apply]
    by_cases h : i = j
    · have hBot : (⊥ : Setoid (Fin 2)).r i j := by simpa using h
      exact False.elim (hn hBot)
    · rw [ite_eq_right h, mul_one]; norm_num

private noncomputable def constTop2 : Dissimilarity 2 → Setoid (Fin 2) :=
  fun _ => ⊤

theorem constTop2_scale : ScaleInvariant 2 constTop2 := fun _ _ _ => rfl
theorem constTop2_cons : Consistent 2 constTop2 := fun _ _ _ h _ => h
theorem constTop2_not_surj : ¬ Function.Surjective constTop2 := by
  intro hsurj
  obtain ⟨d, hd⟩ := hsurj ⊥
  have hne : p0 ≠ p1 := by decide
  have hTop : (⊤ : Setoid (Fin 2)).r p0 p1 := trivial
  have hTopBot : (⊤ : Setoid (Fin 2)) = ⊥ := hd
  have hBot : (⊥ : Setoid (Fin 2)).r p0 p1 := by rw [← hTopBot]; exact hTop
  have heq : p0 = p1 := by simpa using hBot
  exact hne heq

private noncomputable def zero1 : Dissimilarity 1 where
  toFun := fun _ _ => 0
  symm := fun _ _ => rfl
  diag := fun _ => rfl
  pos := fun i j hne => False.elim (hne (Subsingleton.elim i j))

private noncomputable def constTop1 : Dissimilarity 1 → Setoid (Fin 1) :=
  fun _ => ⊤

theorem constTop1_scale : ScaleInvariant 1 constTop1 := fun _ _ _ => rfl
theorem constTop1_cons : Consistent 1 constTop1 := fun _ _ _ h _ => h
theorem constTop1_surj : Function.Surjective constTop1 := by
  intro Γ
  refine ⟨zero1, ?_⟩
  have hsub : ∀ a b : Fin 1, Γ.r a b := fun a b => by
    have hab : a = b := Subsingleton.elim a b
    subst hab
    exact Γ.iseqv.refl a
  have h : Γ = ⊤ := Setoid.ext fun a b => ⟨fun _ => trivial, fun _ => hsub a b⟩
  exact h.symm

private noncomputable def tri3 : Dissimilarity 3 where
  toFun := fun i j => if i = j then 0 else if i.val + j.val = 2 then 3 else 1
  symm := fun i j => by
    show (if i = j then (0 : Real) else if i.val + j.val = 2 then 3 else 1) =
      (if j = i then 0 else if j.val + i.val = 2 then 3 else 1)
    by_cases h : i = j
    · have hj : j = i := h.symm
      rw [ite_eq_left h, ite_eq_left hj]
    · have k : ¬ j = i := fun kk => h kk.symm
      rw [ite_eq_right h, ite_eq_right k]
      by_cases hsum : i.val + j.val = 2
      · have hsum' : j.val + i.val = 2 := by
          rw [Nat.add_comm j.val i.val]; exact hsum
        rw [ite_eq_left hsum, ite_eq_left hsum']
      · have hsum' : ¬ j.val + i.val = 2 := by
          rw [Nat.add_comm j.val i.val]; exact hsum
        rw [ite_eq_right hsum, ite_eq_right hsum']
  diag := fun _ => by exact ite_eq_left rfl
  pos := fun i j hne => by
    rw [ite_eq_right hne]
    by_cases hsum : i.val + j.val = 2
    · rw [ite_eq_left hsum]; norm_num
    · rw [ite_eq_right hsum]; norm_num

private theorem tri3_apply (i j : Fin 3) :
    tri3.toFun i j =
      if i = j then (0 : Real) else if i.val + j.val = 2 then 3 else 1 := rfl

theorem tri3_01 : tri3.toFun q0 q1 = 1 := by
  rw [tri3_apply, ite_eq_right (by decide : q0 ≠ q1),
    ite_eq_right (by decide : ¬ q0.val + q1.val = 2)]

theorem tri3_12 : tri3.toFun q1 q2 = 1 := by
  rw [tri3_apply, ite_eq_right (by decide : q1 ≠ q2),
    ite_eq_right (by decide : ¬ q1.val + q2.val = 2)]

theorem tri3_02 : tri3.toFun q0 q2 = 3 := by
  rw [tri3_apply, ite_eq_right (by decide : q0 ≠ q2),
    ite_eq_left (by decide : q0.val + q2.val = 2)]

theorem tri3_violates :
    tri3.toFun q0 q1 + tri3.toFun q1 q2 < tri3.toFun q0 q2 := by
  rw [tri3_01, tri3_12, tri3_02]; norm_num

theorem partition_bridge :
    (Setoid.Partition.orderIso (Fin 2))
        (((Setoid.Partition.orderIso (Fin 2)).symm)
          ((Setoid.Partition.orderIso (Fin 2)) (⊤ : Setoid (Fin 2)))) =
      (Setoid.Partition.orderIso (Fin 2)) (⊤ : Setoid (Fin 2)) :=
  OrderIso.apply_symm_apply _ _
