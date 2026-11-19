/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Externalities.Coase
import Mathlib.Tactic

/-! Examples and checks for `MathlibExt.Economics.Externalities.Coase` (Atlas AP02.T03). -/

namespace MathlibExtTest.Economics.Externalities.Coase

open MathlibExt.Economics.Coase

/-- Factory (agent 0) values running at 10; resident (agent 1) values quiet at 6. -/
def v : Fin 2 → Bool → ℝ := fun i b =>
  if i = 0 then (if b then 10 else 0) else (if b then 0 else 6)

example :
    (∃ m : Fin 2 → ℝ, ParetoEfficient v 0 true m ∧ ∀ i, utility v true 0 i ≤ utility v true m i) ∧
    (∃ m : Fin 2 → ℝ, ParetoEfficient v 0 true m ∧ ∀ i, utility v false 0 i ≤ utility v true m i) ∧
    (∀ m : Fin 2 → ℝ, Feasible (0 : Fin 2 → ℝ) m → ¬ ParetoEfficient v 0 false m) := by
  have hT : totalValue v true = 10 := by simp [totalValue, v]
  have hF : totalValue v false = 6 := by simp [totalValue, v]
  have hmax : ∀ a', totalValue v a' ≤ totalValue v true := by
    intro a'
    cases a' with
    | false => rw [hF, hT]; norm_num
    | true => exact le_refl _
  refine ⟨?_, ?_, ?_⟩
  · exact exists_paretoEfficient_individuallyRational v 0 true true hmax
  · exact exists_paretoEfficient_individuallyRational v 0 false true hmax
  · intro m _ hPE
    rw [paretoEfficient_iff] at hPE
    obtain ⟨-, hmax'⟩ := hPE
    have hle := hmax' true
    rw [hT, hF] at hle
    norm_num at hle

example :
    ∃ (aF aR : Bool) (mF mR : Fin 2 → ℝ),
      ParetoEfficient v ![0, 0] aF mF ∧
      ParetoEfficient v ![3, 5] aR mR ∧
      totalValue v aF = totalValue v aR ∧ totalValue v aF = 10 := by
  have hT : totalValue v true = 10 := by simp [totalValue, v]
  have hF : totalValue v false = 6 := by simp [totalValue, v]
  have hmax : ∀ a', totalValue v a' ≤ totalValue v true := by
    intro a'
    cases a' with
    | false => rw [hF, hT]; norm_num
    | true => exact le_refl _
  obtain ⟨mF, hPEF, _⟩ :=
    exists_paretoEfficient_individuallyRational v ![0, 0] true true hmax
  obtain ⟨mR, hPER, _⟩ :=
    exists_paretoEfficient_individuallyRational v ![3, 5] false true hmax
  have heq := totalValue_eq_of_paretoEfficient hPEF hPER
  exact ⟨true, true, mF, mR, hPEF, hPER, heq, hT⟩

end MathlibExtTest.Economics.Externalities.Coase
