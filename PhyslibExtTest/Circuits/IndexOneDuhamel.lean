/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.IndexOneDuhamel
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv
open PhyslibExt.Circuits.IndexOneElimination PhyslibExt.Circuits.IndexOneDuhamel

namespace PhyslibExtTest.Circuits.IndexOneDuhamel

/-- With `A = 0` and unit blocks `B = C = D = 1`, the Schur complement
is `-1`, so the reduced operator negates its argument. -/
example (v : Fin 1 → ℝ) :
    @reducedOperator (Fin 1) (Fin 1) _ _ _ _ (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne v = -v := by
  rw [reducedOperator_apply]
  simp [schur, Matrix.neg_mulVec]

/-- The explicit coupled pair `x t = 3 e^{-t}`, `y t = -3 e^{-t}` solves
`x' = y`, `0 = x + y`. -/
lemma coupled_satisfies :
    satisfiesDescriptorSystem (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun t _ => 3 * Real.exp (-t)) (fun t _ => -(3 * Real.exp (-t))) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fun _ : Fin 1 => 3 * Real.exp (-t))
      (fun _ : Fin 1 => -(3 * Real.exp (-t))) t := by
    intro t
    rw [hasDerivAt_pi]
    intro _
    have h1 := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_mul 3
    convert h1 using 1 <;> first | rfl | ring
  refine ⟨fun t => (hd t).differentiableAt, ?_, ?_⟩
  · intro t
    rw [(hd t).deriv]
    funext i
    simp
  · intro t
    funext i
    simp

/-- Existence and uniqueness on the coupled system `x' = y`,
`0 = x + y`: the consistent pair `(3, -3)` at `t₀ = 0` yields a
solution, and uniqueness identifies it with `x t = 3 e^{-t}`,
`y t = -3 e^{-t}`. -/
example :
    ∃ x : ℝ → Fin 1 → ℝ, ∃ y : ℝ → Fin 1 → ℝ,
      satisfiesDescriptorSystem (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) (fun _ _ => 0) x y ∧
      x = (fun t _ => 3 * Real.exp (-t)) ∧ y = (fun t _ => -(3 * Real.exp (-t))) := by
  have hcons : consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      ((fun _ _ => 0 : ℝ → Fin 1 → ℝ) 0) (fun _ => 3) (fun _ => -3) := by
    funext i
    simp
  obtain ⟨x, y, hsat, -, -, -, -, -, huniq⟩ :=
    @descriptor_existsUnique_of_consistentPair (Fin 1) (Fin 1) _ _ _ _
      (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne
      (fun _ _ => 0) (fun _ _ => 0) continuous_const continuous_const 0
      (fun _ => 3) (fun _ => -3) hcons
  have hx0 : (fun t (_ : Fin 1) => 3 * Real.exp (-t)) 0 = fun _ => 3 := by
    funext i
    simp
  obtain ⟨hx, hy⟩ := huniq _ _ coupled_satisfies hx0
  exact ⟨x, y, hsat, hx.symm, hy.symm⟩

/-- Existence under smooth nonzero algebraic forcing: for `x' = 0`,
`0 = y + sin t`, the consistent pair `(3, 0)` at `t₀ = 0` gives a
solution with continuous algebraic component, which is `-sin t`. -/
example :
    ∃ x : ℝ → Fin 1 → ℝ, ∃ y : ℝ → Fin 1 → ℝ,
      satisfiesDescriptorSystem (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) (fun t _ => Real.sin t) x y ∧
      Continuous y ∧ ∀ t, y t = fun _ => -Real.sin t := by
  have hg : Continuous (fun t (_ : Fin 1) => Real.sin t) :=
    continuous_pi fun _ => Real.continuous_sin
  have hcons : consistentPair (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      ((fun t (_ : Fin 1) => Real.sin t) 0) (fun _ => 3) (fun _ => 0) := by
    funext i
    simp
  obtain ⟨x, y, hsat, -, -, hycont, -, hyrec, -⟩ :=
    @descriptor_existsUnique_of_consistentPair (Fin 1) (Fin 1) _ _ _ _
      (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne
      (fun _ _ => 0) (fun t _ => Real.sin t) continuous_const hg 0
      (fun _ => 3) (fun _ => 0) hcons
  refine ⟨x, y, hsat, hycont, fun t => ?_⟩
  rw [hyrec t]
  funext i
  simp [algebraicReconstruction]

/-- Consistency check at concrete values: for unit blocks, state `2`
and forcing `5`, the algebraic value `-7` is consistent and `0` is
not. -/
example :
    consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun _ => 5) (fun _ => 2) (fun _ => -7) ∧
      ¬ consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun _ => 5) (fun _ => 2) (fun _ => 0) := by
  refine ⟨?_, fun h => ?_⟩
  · funext i
    simp
    norm_num
  · have h0 := congrFun h 0
    simp at h0
    norm_num at h0

/-- Nonexistence: for `x' = 0`, `0 = y`, no solution passes through
the inconsistent pair `(0, 1)` at `t₀ = 0`. -/
example :
    ¬ ∃ x : ℝ → Fin 1 → ℝ, ∃ y : ℝ → Fin 1 → ℝ,
      satisfiesDescriptorSystem (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) (fun _ _ => 0) x y ∧
      x 0 = (fun _ => 0) ∧ y 0 = (fun _ => 1) := by
  apply not_exists_solution_of_not_consistentPair
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- Nonexistence with a singular algebraic block: for `0 = 0 * y + 1`,
no initial pair is consistent, so no solution exists through any
pair. -/
example (x₀ y₀ : Fin 1 → ℝ) :
    ¬ ∃ x : ℝ → Fin 1 → ℝ, ∃ y : ℝ → Fin 1 → ℝ,
      satisfiesDescriptorSystem (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) (fun _ _ => 1) x y ∧
      x 0 = x₀ ∧ y 0 = y₀ := by
  apply not_exists_solution_of_not_consistentPair
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- A continuous but nondifferentiable algebraic forcing yields a
solution whose algebraic component is not differentiable. -/
example :
    ∃ x : ℝ → Fin 1 → ℝ, ∃ y : ℝ → Fin 1 → ℝ,
      satisfiesDescriptorSystem (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 1
        (fun _ _ => 0) (fun t _ => |t|) x y ∧
      ¬ DifferentiableAt ℝ y 0 :=
  exists_solution_algebraic_not_differentiableAt

end PhyslibExtTest.Circuits.IndexOneDuhamel
