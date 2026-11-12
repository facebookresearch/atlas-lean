/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianTrivialityReduction









open Finset
open scoped BigOperators

namespace StatMech.FrontierA

variable {X : Type*} [Fintype X] [AddCommGroup X]



def finiteSusceptibility (G : X -> Real) : Real :=
  ∑ x, G x



def finiteIntegratedTreeDiagram (G : X -> Real) : Real :=
  ∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, ∑ y : X,
    G y * G (y - x₂) * G (y - x₃) * G (y - x₄)


def finiteIntegratedFourthCumulant (U : X -> X -> X -> Real) : Real :=
  ∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, U x₂ x₃ x₄

private lemma sum_sub_left (G : X -> Real) (y : X) :
    (∑ x : X, G (y - x)) = ∑ z : X, G z := by
  exact Equiv.sum_comp (Equiv.subLeft y) G

private lemma sum_three_mul
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (a : Real) (A : I -> Real) (B : J -> Real) (C : K -> Real) :
    (∑ i, ∑ j, ∑ k, a * A i * B j * C k) =
      a * (∑ i, A i) * (∑ j, B j) * (∑ k, C k) := by
  calc
    _ = ∑ i, ∑ j, (a * A i * B j) * (∑ k, C k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ i, (a * A i) * (∑ j, B j) * (∑ k, C k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul]
      rw [← Finset.mul_sum]
    _ = a * (∑ i, A i) * (∑ j, B j) * (∑ k, C k) := by
      rw [← Finset.sum_mul]
      rw [← Finset.sum_mul]
      rw [show (∑ i, a * A i) = a * (∑ i, A i) by rw [Finset.mul_sum]]


theorem finiteIntegratedTreeDiagram_eq_susceptibility_pow_four (G : X -> Real) :
    finiteIntegratedTreeDiagram G = finiteSusceptibility G ^ 4 := by
  unfold finiteIntegratedTreeDiagram finiteSusceptibility
  have hreorder :
      (∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, ∑ y : X,
        G y * G (y - x₂) * G (y - x₃) * G (y - x₄)) =
      ∑ y : X, ∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X,
        G y * G (y - x₂) * G (y - x₃) * G (y - x₄) := by
    calc
      _ = ∑ x₂ : X, ∑ x₃ : X, ∑ y : X, ∑ x₄ : X,
          G y * G (y - x₂) * G (y - x₃) * G (y - x₄) := by
        apply Finset.sum_congr rfl
        intro x₂ _
        apply Finset.sum_congr rfl
        intro x₃ _
        rw [Finset.sum_comm]
      _ = ∑ x₂ : X, ∑ y : X, ∑ x₃ : X, ∑ x₄ : X,
          G y * G (y - x₂) * G (y - x₃) * G (y - x₄) := by
        apply Finset.sum_congr rfl
        intro x₂ _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hreorder]
  calc
    (∑ y : X, ∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X,
        G y * G (y - x₂) * G (y - x₃) * G (y - x₄)) =
        ∑ y : X, G y * (∑ x : X, G x) ^ 3 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [sum_three_mul (G y) (fun x => G (y - x))
        (fun x => G (y - x)) (fun x => G (y - x))]
      rw [sum_sub_left]
      ring
    _ = (∑ x : X, G x) ^ 4 := by
      rw [← Finset.sum_mul]
      ring



theorem finiteIntegratedFourthCumulant_treeDiagram_bound
    (G : X -> Real) (U : X -> X -> X -> Real)
    (htree : ∀ x₂ x₃ x₄,
      0 <= -U x₂ x₃ x₄ ∧
      -U x₂ x₃ x₄ <= 2 * ∑ y : X,
        G y * G (y - x₂) * G (y - x₃) * G (y - x₄)) :
    0 <= -finiteIntegratedFourthCumulant U ∧
      -finiteIntegratedFourthCumulant U <=
        2 * finiteSusceptibility G ^ 4 := by
  have hnonneg : 0 <= ∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, -U x₂ x₃ x₄ :=
    Finset.sum_nonneg fun x₂ _ => Finset.sum_nonneg fun x₃ _ =>
      Finset.sum_nonneg fun x₄ _ => (htree x₂ x₃ x₄).1
  have hupper : (∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, -U x₂ x₃ x₄) <=
      ∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, 2 * ∑ y : X,
        G y * G (y - x₂) * G (y - x₃) * G (y - x₄) :=
    Finset.sum_le_sum fun x₂ _ => Finset.sum_le_sum fun x₃ _ =>
      Finset.sum_le_sum fun x₄ _ => (htree x₂ x₃ x₄).2
  have hneg : (∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, -U x₂ x₃ x₄) =
      -finiteIntegratedFourthCumulant U := by
    simp [finiteIntegratedFourthCumulant]
  have htreeSum :
      (∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, 2 * ∑ y : X,
        G y * G (y - x₂) * G (y - x₃) * G (y - x₄)) =
        2 * finiteSusceptibility G ^ 4 := by
    calc
      _ = 2 * finiteIntegratedTreeDiagram G := by
        unfold finiteIntegratedTreeDiagram
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x₂ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x₃ _
        rw [Finset.mul_sum]
      _ = _ := by rw [finiteIntegratedTreeDiagram_eq_susceptibility_pow_four]
  rw [hneg] at hnonneg hupper
  rw [htreeSum] at hupper
  exact ⟨hnonneg, hupper⟩

end StatMech.FrontierA
