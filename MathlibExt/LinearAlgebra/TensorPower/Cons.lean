/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The first coordinate of a tensor power

The cons equivalence separates the first factor of an indexed tensor
power. It is natural in the linear map on each factor and is defined
for modules over a commutative semiring.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

namespace TensorPower

universe u v w

/-- A first coordinate followed by the remaining tensor-power coordinates. -/
def consIndexEquiv (n : ℕ) : PUnit.{1} ⊕ Fin n ≃ Fin (n + 1) :=
  ((_root_.finSuccEquiv n).trans
    ((Equiv.optionEquivSumPUnit.{0, 0} (Fin n)).trans
      (Equiv.sumComm (Fin n) PUnit.{1}))).symm

@[simp]
theorem consIndexEquiv_inl (n : ℕ) (x : PUnit.{1}) :
    consIndexEquiv n (Sum.inl x) = 0 := by
  cases x
  simp [consIndexEquiv]

@[simp]
theorem consIndexEquiv_inr (n : ℕ) (i : Fin n) :
    consIndexEquiv n (Sum.inr i) = i.succ := by
  simp [consIndexEquiv]

variable (k : Type u) (M : Type v) [CommSemiring k] [AddCommMonoid M] [Module k M]

/-- A tensor power of degree zero is canonically the scalar module. -/
def zeroEquiv : TensorPower k 0 M ≃ₗ[k] k :=
  PiTensorProduct.isEmptyEquiv (Fin 0)

/-- Separate the first tensor coordinate from a tensor power. -/
def consEquiv (n : ℕ) : M ⊗[k] TensorPower k n M ≃ₗ[k] TensorPower k (n + 1) M :=
  ((PiTensorProduct.subsingletonEquiv
      (R := k) (s := fun _ : PUnit.{1} => M) PUnit.unit).symm.rTensor
        (TensorPower k n M)).trans
    ((PiTensorProduct.tmulEquiv k M).trans
      (PiTensorProduct.reindex k (fun _ : PUnit.{1} ⊕ Fin n => M)
        (consIndexEquiv n)))

/-- The computed equivalence puts the literal first factor before the tail. -/
@[simp]
theorem consEquiv_tmul (n : ℕ) (m : M) (s : Fin n → M) :
    consEquiv k M n (m ⊗ₜ[k] PiTensorProduct.tprod k s) =
      PiTensorProduct.tprod k (Fin.cons m s) := by
  simp only [consEquiv, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    PiTensorProduct.subsingletonEquiv_symm_apply', PiTensorProduct.tmulEquiv_apply,
    PiTensorProduct.reindex_tprod]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  obtain ⟨j, rfl⟩ := (consIndexEquiv n).surjective i
  rcases j with j | j
  · cases j
    change Sum.elim (fun _ : PUnit.{1} => m) s
      ((consIndexEquiv n).symm (consIndexEquiv n (Sum.inl PUnit.unit))) = m
    rw [Equiv.symm_apply_apply]
    rfl
  · change Sum.elim (fun _ : PUnit.{1} => m) s
      ((consIndexEquiv n).symm (consIndexEquiv n (Sum.inr j))) = s j
    rw [Equiv.symm_apply_apply]
    rfl

/-- Splitting a pure tensor recovers its actual first coordinate and tail. -/
@[simp]
theorem consEquiv_symm_tprod (n : ℕ) (a : Fin (n + 1) → M) :
    (consEquiv k M n).symm (PiTensorProduct.tprod k a) =
      a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a) := by
  apply (consEquiv k M n).injective
  simp only [LinearEquiv.apply_symm_apply, consEquiv_tmul, Fin.cons_self_tail]

variable {k M} {N : Type w} [AddCommMonoid N] [Module k N]

/-- Applying the original linear map to every factor commutes with cons coordinates. -/
theorem consEquiv_naturality (f : M →ₗ[k] N) (n : ℕ) :
    (consEquiv k N n).toLinearMap.comp
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => f))) =
      (PiTensorProduct.map (fun _ : Fin (n + 1) => f)).comp
        (consEquiv k M n).toLinearMap := by
  apply TensorProduct.ext'
  intro m y
  have h :
      ((consEquiv k N n).toLinearMap.comp
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => f)))).comp
          (TensorProduct.mk k M (TensorPower k n M) m) =
      ((PiTensorProduct.map (fun _ : Fin (n + 1) => f)).comp
        (consEquiv k M n).toLinearMap).comp
          (TensorProduct.mk k M (TensorPower k n M) m) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro s
    change consEquiv k N n
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => f))
          (m ⊗ₜ[k] PiTensorProduct.tprod k s)) =
      PiTensorProduct.map (fun _ : Fin (n + 1) => f)
        (consEquiv k M n (m ⊗ₜ[k] PiTensorProduct.tprod k s))
    simp only [TensorProduct.map_tmul, PiTensorProduct.map_tprod, consEquiv_tmul]
    apply congrArg (PiTensorProduct.tprod k)
    funext i
    cases i using Fin.cases <;> simp
  exact DFunLike.congr_fun h y


/-- Insert an actual first vector while retaining the original cons coordinates. -/
def consInsert (k : Type u) (M : Type v) [CommSemiring k] [AddCommMonoid M]
    [Module k M] (e : M) (n : ℕ) :
    M ⊗[k] TensorPower k n M →ₗ[k] M ⊗[k] TensorPower k (n + 1) M :=
  (TensorProduct.mk k M (TensorPower k (n + 1) M) e).comp
    (consEquiv k M n).toLinearMap

/-- The inserted vector precedes the first input vector and its tail. -/
@[simp]
theorem consInsert_tmul (k : Type u) (M : Type v) [CommSemiring k] [AddCommMonoid M]
    [Module k M] (e : M) (n : ℕ) (m : M) (a : Fin n → M) :
    consInsert k M e n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      e ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons m a) := by
  change e ⊗ₜ[k] consEquiv k M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  exact congrArg (fun y : TensorPower k (n + 1) M => e ⊗ₜ[k] y)
    (consEquiv_tmul k M n m a)

/-- Every original linear map takes insertion of e to insertion of its actual image. -/
theorem consInsert_naturality (f : M →ₗ[k] N) (e : M) (n : ℕ) :
    (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin (n + 1) => f))).comp
        (consInsert k M e n) =
      (consInsert k N (f e) n).comp
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => f))) := by
  apply LinearMap.ext
  intro x
  change TensorProduct.map f (PiTensorProduct.map (fun _ : Fin (n + 1) => f))
      (e ⊗ₜ[k] consEquiv k M n x) =
    f e ⊗ₜ[k] consEquiv k N n
      (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => f)) x)
  rw [TensorProduct.map_tmul]
  have h := DFunLike.congr_fun (consEquiv_naturality f n) x
  exact congrArg (fun y => f e ⊗ₜ[k] y) h.symm

end TensorPower
