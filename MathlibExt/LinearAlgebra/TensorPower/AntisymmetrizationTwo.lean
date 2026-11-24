/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.LinearAlgebra.TensorPower.Antisymmetrization
public import MathlibExt.GroupTheory.Perm.OrderedDeletion

/-!
# Antisymmetrization of two vectors

The signed place-permutation sum in degree two is the first tensor word
minus its transposition. The formula uses integral signs and requires no
factorial inverse or rational scalar structure.
-/

@[expose] public section
noncomputable section

universe u v

namespace TensorPower

variable (k : Type u) [CommRing k] (V : Type v) [AddCommGroup V] [Module k V]

/-- The actual full exterior antisymmetrization is the original ordered tensor minus its reversed tensor. -/
theorem exteriorAntisymmetrization_two (x y : V) :
    exteriorAntisymmetrization k V 2 (exteriorPower.ιMulti k 2 (Fin.cons x (fun _ : Fin 1 => y))) =
      PiTensorProduct.tprod k (Fin.cons x (fun _ : Fin 1 => y)) -
        PiTensorProduct.tprod k (Fin.cons y (fun _ : Fin 1 => x)) := by
  classical
  let a : Fin 2 → V := Fin.cons x (fun _ : Fin 1 => y)
  letI : Unique (Equiv.Perm (Fin 1)) :=
    { default := 1, uniq := fun π => Subsingleton.elim _ _ }
  have hdefault : (default : Equiv.Perm (Fin 1)) = 1 := Subsingleton.elim _ _
  have h₀ : a ∘ Equiv.Perm.orderedFirst (0 : Fin 2) (1 : Equiv.Perm (Fin 1)) = a := by
    funext j
    cases j using Fin.cases with
    | zero => rw [Function.comp_apply, Equiv.Perm.orderedFirst_zero]
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [Function.comp_apply, Equiv.Perm.orderedFirst_succ]
      rfl
  have h₁ : a ∘ Equiv.Perm.orderedFirst (1 : Fin 2) (1 : Equiv.Perm (Fin 1)) =
      Fin.cons y (fun _ : Fin 1 => x) := by
    funext j
    cases j using Fin.cases with
    | zero => rw [Function.comp_apply, Equiv.Perm.orderedFirst_zero]; rfl
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [Function.comp_apply, Equiv.Perm.orderedFirst_succ]
      rfl
  rw [exteriorAntisymmetrization_ιMulti, Equiv.Perm.sum_orderedFirst 1]
  simp only [Fintype.sum_unique, hdefault, Units.smul_def]
  change (∑ i : Fin 2, (Equiv.Perm.sign (Equiv.Perm.orderedFirst i 1) : ℤ) •
      PiTensorProduct.tprod k (a ∘ Equiv.Perm.orderedFirst i 1)) =
    PiTensorProduct.tprod k a - PiTensorProduct.tprod k (Fin.cons y (fun _ : Fin 1 => x))
  rw [Fin.sum_univ_two, h₀, h₁, Equiv.Perm.sign_orderedFirst, Equiv.Perm.sign_orderedFirst]
  norm_num [sub_eq_add_neg, a]

end TensorPower
