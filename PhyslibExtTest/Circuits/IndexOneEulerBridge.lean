/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.IndexOneEulerBridge

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv
open PhyslibExt.Circuits.IndexOneElimination PhyslibExt.Circuits.IndexOneDuhamel
open PhyslibExt.Circuits.IndexOneEulerBridge

namespace PhyslibExtTest.Circuits.IndexOneEulerBridge

attribute [local instance] invertibleOne

/-- The fixture `x' = y`, `0 = x + y` has reduced Lipschitz constant `1`. -/
lemma fixture_reducedLipschitzConstant :
    (reducedLipschitzConstant (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) : ℝ) = 1 := by
  have hop : reducedOperator (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      -ContinuousLinearMap.id ℝ (Fin 1 → ℝ) := by
    ext v i
    rw [reducedOperator_apply]
    simp [schur, Matrix.neg_mulVec]
  rw [reducedLipschitzConstant, coe_nnnorm, hop, norm_neg, ContinuousLinearMap.norm_id]

/-- The fixture has reconstruction gain `‖D⁻¹ * C‖ = 1`. -/
lemma fixture_reconstructionGain :
    reconstructionGain (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  have hid : LinearMap.toContinuousLinearMap
      (Matrix.toLin' ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 1)) =
      ContinuousLinearMap.id ℝ (Fin 1 → ℝ) := by
    ext v i
    simp
  rw [reconstructionGain, hid, ContinuousLinearMap.norm_id]

/-- The norm of a difference of constant vectors on `Fin 1`. -/
lemma norm_const_sub_const (a b : ℝ) :
    ‖(fun _ : Fin 1 => a) - (fun _ : Fin 1 => b)‖ = |a - b| := by
  rw [show ((fun _ : Fin 1 => a) - fun _ : Fin 1 => b) = fun _ : Fin 1 => a - b from rfl,
    pi_norm_const, Real.norm_eq_abs]

/-- **Euler error bound on the fixture.** Instantiating `indexOneEuler_error` on `x' = y`,
`0 = x + y` over `[0, 1]` with exact solution `(e^{-t}, -e^{-t})` and Euler iterates started with
mismatch `1/10`: one constant `K` bounds the state and reconstructed algebraic errors at every
admissible sample, for both step sizes `1/2` and `1/4`. -/
lemma fixture_euler_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, (h = 1 / 2 ∨ h = 1 / 4) → ∀ k : ℕ, (k : ℝ) * h ≤ 1 →
      ‖scalarEulerIterates h k - (fun _ => Real.exp (-((k : ℝ) * h)))‖ ≤
          Real.exp 1 * (1 / 10) + K * h ∧
        ‖reconstructedAlgebraic (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (fun _ _ => 0) 0 h
            (scalarEulerIterates h) k - (fun _ => -Real.exp (-((k : ℝ) * h)))‖ ≤
          Real.exp 1 * (1 / 10) + K * h := by
  obtain ⟨hX, -, -, hcons, -, -, -⟩ := scalarEuler_twoStepSizes (1 / 2) (Or.inl rfl)
  obtain ⟨-, K, hK, hbound⟩ := indexOneEuler_error (0 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (fun _ _ => 0) (fun _ _ => 0) contDiff_const contDiff_const 0 1 one_pos (fun _ => 1)
    (fun _ => -1) hcons
  clear hX
  refine ⟨K, hK, fun h hh k hk => ?_⟩
  obtain ⟨hX, h0, -, -, hsol, -, -⟩ := scalarEuler_twoStepSizes h hh
  have hpos : h ∈ Set.Ioc (0 : ℝ) (1 - 0) := by
    rcases hh with rfl | rfl <;> norm_num
  have hx0 : (fun (t : ℝ) (_ : Fin 1) => Real.exp (-t)) 0 = fun _ => 1 := by
    funext i
    simp
  obtain ⟨hstate, halg⟩ := hbound _ _ hx0 hsol h hpos _ hX k (by linarith)
  have hmis : ‖scalarEulerIterates h 0 - fun _ => (1 : ℝ)‖ = 1 / 10 := by
    rw [h0, pi_norm_const, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [hmis, fixture_reducedLipschitzConstant, sub_zero, one_mul, zero_add] at hstate halg
  rw [fixture_reconstructionGain, one_mul] at halg
  exact ⟨hstate, halg⟩

/-- At the horizon `T = 1`, the two step sizes give the concrete endpoint values `11/40` and
`891/2560`, both within the same bound `e/10 + K h` of the exact value `e^{-1}`. -/
example :
    ∃ K : ℝ, 0 ≤ K ∧
      |11 / 40 - Real.exp (-1)| ≤ Real.exp 1 * (1 / 10) + K * (1 / 2) ∧
      |891 / 2560 - Real.exp (-1)| ≤ Real.exp 1 * (1 / 10) + K * (1 / 4) := by
  obtain ⟨K, hK, hbound⟩ := fixture_euler_error
  obtain ⟨-, -, -, -, -, h2, -⟩ := scalarEuler_twoStepSizes (1 / 2) (Or.inl rfl)
  obtain ⟨-, -, -, -, -, -, h4⟩ := scalarEuler_twoStepSizes (1 / 4) (Or.inr rfl)
  have hA := (hbound (1 / 2) (Or.inl rfl) 2 (by norm_num)).1
  have hB := (hbound (1 / 4) (Or.inr rfl) 4 (by norm_num)).1
  rw [h2, norm_const_sub_const] at hA
  rw [h4, norm_const_sub_const] at hB
  norm_num at hA hB
  exact ⟨K, hK, hA, hB⟩

/-- The reconstructed algebraic iterates of the fixture are the negated states, so at the horizon
they sit within the same bound of the exact algebraic value `-e^{-1}`. -/
example :
    ∃ K : ℝ, 0 ≤ K ∧
      |-(11 / 40) + Real.exp (-1)| ≤ Real.exp 1 * (1 / 10) + K * (1 / 2) := by
  obtain ⟨K, hK, hbound⟩ := fixture_euler_error
  obtain ⟨-, -, hrec, -, -, h2, -⟩ := scalarEuler_twoStepSizes (1 / 2) (Or.inl rfl)
  have hA := (hbound (1 / 2) (Or.inl rfl) 2 (by norm_num)).2
  rw [hrec, h2] at hA
  rw [show (-(fun _ : Fin 1 => (11 / 40 : ℝ)) - fun _ => -Real.exp (-(((2 : ℕ) : ℝ) * (1 / 2)))) =
      (fun _ : Fin 1 => -(11 / 40 : ℝ)) - fun _ => -Real.exp (-(((2 : ℕ) : ℝ) * (1 / 2))) from rfl,
    norm_const_sub_const] at hA
  norm_num at hA
  exact ⟨K, hK, hA⟩

/-- The inconsistent algebraic value `0` against the state `1` of the fixture is bounded by `K h`
for no constant `K`. -/
example (K : ℝ) :
    ¬ ∀ h ∈ Set.Ioc (0 : ℝ) (1 - 0),
      ‖(fun _ => (0 : ℝ)) - algebraicReconstruction (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) ((fun (_ : ℝ) (_ : Fin 1) => (0 : ℝ)) 0)‖ ≤
        K * h := by
  refine not_forall_le_of_not_consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) 0 1 one_pos (fun _ => 1) (fun _ => 0) ?_ K
  intro h
  have h0 := congrFun h 0
  simp at h0

end PhyslibExtTest.Circuits.IndexOneEulerBridge
