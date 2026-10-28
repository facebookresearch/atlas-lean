/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsXiTensorCoords

/-! The genuine Xi coordinate sum has only four physical columns per output row. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The four coordinates in the output row's actual MOG tetrad. -/
def generatedAxisGlobalXiColumn (i : Fin 24) (b : Fin 4) : Fin 24 :=
  ⟨4 * (i.val / 4) + b.val, by have hi := i.isLt; have hb := b.isLt; omega⟩

/-- Every numerator entry outside the output tetrad is exactly zero. -/
theorem generatedAxisGlobalXi_numerator_tetrads : ∀ i : Fin 24, ∀ a : Fin 6,
    ∀ b : Fin 4,
    co1XiNumerator i (finProdFinEquiv (a, b)) =
      if a.val = i.val / 4 then co1XiNumerator i (generatedAxisGlobalXiColumn i b) else 0 := by
  decide +kernel

/-- The real row action is exactly its four-column tetrad sum. -/
theorem generatedAxisGlobalXi_numerator_row (i : Fin 24) (v : Fin 24 → ℝ) :
    (∑ j : Fin 24, (co1XiNumerator i j : ℝ) * v j) =
      ∑ b : Fin 4, (co1XiNumerator i (generatedAxisGlobalXiColumn i b) : ℝ) *
        v (generatedAxisGlobalXiColumn i b) := by
  let k : Fin 6 := ⟨i.val / 4, by have hi := i.isLt; omega⟩
  have hc (b : Fin 4) : finProdFinEquiv (k, b) = generatedAxisGlobalXiColumn i b := by
    apply Fin.ext
    change b.val + 4 * k.val = 4 * (i.val / 4) + b.val
    dsimp [k]
    omega
  have hs := Equiv.sum_comp (finProdFinEquiv : Fin 6 × Fin 4 ≃ Fin 24)
    (fun j => (co1XiNumerator i j : ℝ) * v j)
  rw [← hs, Fintype.sum_prod_type]
  calc
    _ = ∑ a : Fin 6, if a = k then
        ∑ b : Fin 4, (co1XiNumerator i (generatedAxisGlobalXiColumn i b) : ℝ) *
          v (generatedAxisGlobalXiColumn i b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = k
      · subst a
        simp only [ite_true, hc]
      · have hav : a.val ≠ i.val / 4 := by
          intro h
          apply ha
          apply Fin.ext
          exact h
        simp only [ha, ite_false]
        simp_rw [generatedAxisGlobalXi_numerator_tetrads]
        simp only [hav, ↓reduceIte]
        simp only [Int.cast_zero, zero_mul, Finset.sum_const_zero]
    _ = _ := by simp

/-- The exact real Xi coefficient needs only sixty-four shifted rows and four columns. -/
theorem generatedAxisGlobalXi_tensor_tetrad (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    16 * localTensorRepresentation xiSpinLocalFiber T t i =
      ∑ a : XiGrayIndex, ∑ b : Fin 4,
        qSign (generatedAxisGlobalXiSpinPhase a t) *
          (co1XiNumerator i (generatedAxisGlobalXiColumn i b) : ℝ) *
            T (t + xiGrayCode a) (generatedAxisGlobalXiColumn i b) := by
  rw [generatedAxisGlobalXi_tensor_coordinate]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = qSign (generatedAxisGlobalXiSpinPhase a t) *
        (∑ j : Fin 24, (co1XiNumerator i j : ℝ) * T (t + xiGrayCode a) j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = qSign (generatedAxisGlobalXiSpinPhase a t) *
        (∑ b : Fin 4, (co1XiNumerator i (generatedAxisGlobalXiColumn i b) : ℝ) *
          T (t + xiGrayCode a) (generatedAxisGlobalXiColumn i b)) := by
      rw [generatedAxisGlobalXi_numerator_row]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
