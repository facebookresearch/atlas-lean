/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_flowChart_add_single_eq_mul_conj.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The `exactSource` consumers restate the statement of the source theorem.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.ArchFlowChart

@[expose] public section

open NumberField AutomorphicForm
open scoped Classical

namespace AutomorphicFormArchFlowChartTest

/-- Consumer with the original `Type` binders. -/
private theorem exactSource (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (j : Fin L₀.length) (t : Fin L₀.length → ℝ) (s : ℝ) :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt K d.2.1 d.2.2 t)
        (fun d => archFlowAtComplex K d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun i => flow (L₀.get i) (t i)).prod
    let tailMatR : InfinitePlace K → GL (Fin 2) ℝ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inl d => if d.1 = w then archFlowMatrix d.2.2 (t i) else 1
        | Sum.inr _ => (1 : GL (Fin 2) ℝ)).drop (j.val + 1)).prod
    let tailMatC : InfinitePlace K → GL (Fin 2) ℂ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inr d => if d.1 = w then archFlowMatrixComplex d.2.2 (t i) else 1
        | Sum.inl _ => (1 : GL (Fin 2) ℂ)).drop (j.val + 1)).prod
    match L₀.get j with
    | Sum.inl d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archRealGLAt K d.2.1 ((tailMatR d.1)⁻¹ * archFlowMatrix d.2.2 s * tailMatR d.1)
    | Sum.inr d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archComplexGLAt K d.2.1
          ((tailMatC d.1)⁻¹ * archFlowMatrixComplex d.2.2 s * tailMatC d.1) :=
  flowChart_add_single_eq_mul_conj K L₀ j t s

/-- Higher-universe consumer. -/
private theorem exactSource_univ (K : Type 1) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (j : Fin L₀.length) (t : Fin L₀.length → ℝ) (s : ℝ) :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt K d.2.1 d.2.2 t)
        (fun d => archFlowAtComplex K d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun i => flow (L₀.get i) (t i)).prod
    let tailMatR : InfinitePlace K → GL (Fin 2) ℝ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inl d => if d.1 = w then archFlowMatrix d.2.2 (t i) else 1
        | Sum.inr _ => (1 : GL (Fin 2) ℝ)).drop (j.val + 1)).prod
    let tailMatC : InfinitePlace K → GL (Fin 2) ℂ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inr d => if d.1 = w then archFlowMatrixComplex d.2.2 (t i) else 1
        | Sum.inl _ => (1 : GL (Fin 2) ℂ)).drop (j.val + 1)).prod
    match L₀.get j with
    | Sum.inl d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archRealGLAt K d.2.1 ((tailMatR d.1)⁻¹ * archFlowMatrix d.2.2 s * tailMatR d.1)
    | Sum.inr d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archComplexGLAt K d.2.1
          ((tailMatC d.1)⁻¹ * archFlowMatrixComplex d.2.2 s * tailMatC d.1) :=
  flowChart_add_single_eq_mul_conj K L₀ j t s

/-- Boundary example: with a single real letter, the tail is empty, so the
increment is unconjugated. -/
example (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (d : ArchDir) (t s : ℝ) :
    archFlowAt K hw d (t + s) = archFlowAt K hw d t * archFlowAt K hw d s := by
  have h := flowChart_add_single_eq_mul_conj K
    [Sum.inl ⟨w, hw, d⟩] ⟨0, by simp⟩ (fun _ => t) s
  rw [show archFlowAt K hw d s = archRealGLAt K hw (archFlowMatrix d s) from rfl]
  simpa using h

/-! ### Explicit conjugates

Closed forms of the conjugated increments that the examples below expect. -/

/-- Conjugating `unipotentGL2 x` by the real split torus at `b` scales `x` by
`exp (-2b)`. -/
private theorem splitTorusGL2_conj_unipotentGL2 (b x : ℝ) :
    (splitTorusGL2 b)⁻¹ * unipotentGL2 x * splitTorusGL2 b
      = unipotentGL2 (x * Real.exp (-(2 * b))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  rw [show -(2 * b) = -b + -b by ring, Real.exp_add]
  ring

/-- Conjugating `unipotentGL2 x` by the complex split torus at `z` scales `x`
by `exp (-2z)`. -/
private theorem splitTorusGL2Complex_conj_unipotentGL2 (z x : ℂ) :
    (splitTorusGL2Complex z)⁻¹ * unipotentGL2 x * splitTorusGL2Complex z
      = unipotentGL2 (x * Complex.exp (-(2 * z))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2Complex, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.exp_add]
  rw [show -(2 * z) = -z + -z by ring, Complex.exp_add]
  ring

/-- Conjugating the real split torus at `s` by the ordered product
`unipotentGL2 c * splitTorusGL2 b`. -/
private theorem unipotent_splitTorusGL2_conj_splitTorusGL2 (c b s : ℝ) :
    (unipotentGL2 c * splitTorusGL2 b)⁻¹ * splitTorusGL2 s * (unipotentGL2 c * splitTorusGL2 b)
      = splitTorusGL2 s *
          unipotentGL2 (c * (1 - Real.exp (-(2 * s))) * Real.exp (-(2 * b))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  rw [show -(2 * s) = -s + -s by ring, show -(2 * b) = -b + -b by ring]
  simp only [Real.exp_add, Real.exp_neg]
  field_simp
  ring

/-- Conjugating the complex split torus at `s` by the ordered product
`unipotentGL2 c * splitTorusGL2Complex b`. -/
private theorem unipotent_splitTorusGL2Complex_conj_splitTorusGL2Complex (c b s : ℂ) :
    (unipotentGL2 c * splitTorusGL2Complex b)⁻¹ * splitTorusGL2Complex s *
        (unipotentGL2 c * splitTorusGL2Complex b)
      = splitTorusGL2Complex s *
          unipotentGL2 (c * (1 - Complex.exp (-(2 * s))) * Complex.exp (-(2 * b))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2Complex, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.exp_add]
  rw [show -(2 * s) = -s + -s by ring, show -(2 * b) = -b + -b by ring]
  simp only [Complex.exp_add, Complex.exp_neg]
  field_simp
  ring

/-! ### Non-empty tails

Each example below specializes `flowChart_add_single_eq_mul_conj` to a concrete
word and checks the conjugated increment against its closed form. -/

/-- Real place, one later factor at the same place: moving the first time of the
word `E · H` by `s` multiplies the chart by `unipotentGL2 (s * exp (-2b))`, the
increment conjugated by the later torus factor. -/
example (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (a b s : ℝ) :
    archFlowAt K hw .E (a + s) * archFlowAt K hw .H b
      = archFlowAt K hw .E a * archFlowAt K hw .H b *
          archRealGLAt K hw (unipotentGL2 (s * Real.exp (-(2 * b)))) := by
  have h := flowChart_add_single_eq_mul_conj K
    [Sum.inl ⟨w, hw, .E⟩, Sum.inl ⟨w, hw, .H⟩] ⟨0, by simp⟩ ![a, b] s
  rw [← splitTorusGL2_conj_unipotentGL2]
  simp [archFlowMatrix, mul_assoc] at h ⊢
  with_reducible exact h

/-- The same word over `ℚ`, whose only infinite place is real, at times `(1, 2)`
with increment `3`: the conjugated increment is `unipotentGL2 (3 * exp (-4))`. -/
example :
    archFlowAt ℚ Rat.isReal_infinitePlace .E (1 + 3) *
        archFlowAt ℚ Rat.isReal_infinitePlace .H 2
      = archFlowAt ℚ Rat.isReal_infinitePlace .E 1 *
          archFlowAt ℚ Rat.isReal_infinitePlace .H 2 *
          archRealGLAt ℚ Rat.isReal_infinitePlace (unipotentGL2 (3 * Real.exp (-4))) := by
  have h := flowChart_add_single_eq_mul_conj ℚ
    [Sum.inl ⟨Rat.infinitePlace, Rat.isReal_infinitePlace, .E⟩,
      Sum.inl ⟨Rat.infinitePlace, Rat.isReal_infinitePlace, .H⟩] ⟨0, by simp⟩ ![1, 2] 3
  rw [show (-4 : ℝ) = -(2 * 2) by norm_num, ← splitTorusGL2_conj_unipotentGL2]
  simp [archFlowMatrix, mul_assoc] at h ⊢
  with_reducible exact h

/-- Real place, filtering: only later factors at the incremented place
conjugate. The earlier torus factor at `w`, the later factor at another real
place `w'` and the later complex factor all drop out; the conjugated increment
depends on the last time `a₄` alone. -/
example (K : Type) [Field K] [NumberField K] (w w' v : InfinitePlace K)
    (hw : w.IsReal) (hw' : w'.IsReal) (hv : v.IsComplex) (hww : w' ≠ w)
    (a₀ a₁ a₂ a₃ a₄ s : ℝ) :
    archFlowAt K hw .H a₀ * archFlowAt K hw .E (a₁ + s) * archFlowAt K hw' .H a₂ *
        archFlowAtComplex K hv .iH a₃ * archFlowAt K hw .H a₄
      = archFlowAt K hw .H a₀ * archFlowAt K hw .E a₁ * archFlowAt K hw' .H a₂ *
          archFlowAtComplex K hv .iH a₃ * archFlowAt K hw .H a₄ *
          archRealGLAt K hw (unipotentGL2 (s * Real.exp (-(2 * a₄)))) := by
  have h := flowChart_add_single_eq_mul_conj K
    [Sum.inl ⟨w, hw, .H⟩, Sum.inl ⟨w, hw, .E⟩, Sum.inl ⟨w', hw', .H⟩,
      Sum.inr ⟨v, hv, .iH⟩, Sum.inl ⟨w, hw, .H⟩] ⟨1, by simp⟩ ![a₀, a₁, a₂, a₃, a₄] s
  rw [← splitTorusGL2_conj_unipotentGL2]
  simp [archFlowMatrix, hww, mul_assoc] at h ⊢
  with_reducible exact h

/-- Real place, order: with two later factors `E c` then `H b` at the same
place, the increment is conjugated by their product in word order. The reversed
product `H b · E c` would give `splitTorusGL2 s * unipotentGL2 (c * (1 - exp (-2s)))`,
without the factor `exp (-2b)`. -/
example (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (a c b s : ℝ) :
    archFlowAt K hw .H (a + s) * archFlowAt K hw .E c * archFlowAt K hw .H b
      = archFlowAt K hw .H a * archFlowAt K hw .E c * archFlowAt K hw .H b *
          archRealGLAt K hw (splitTorusGL2 s *
            unipotentGL2 (c * (1 - Real.exp (-(2 * s))) * Real.exp (-(2 * b)))) := by
  have h := flowChart_add_single_eq_mul_conj K
    [Sum.inl ⟨w, hw, .H⟩, Sum.inl ⟨w, hw, .E⟩, Sum.inl ⟨w, hw, .H⟩] ⟨0, by simp⟩
    ![a, c, b] s
  rw [← unipotent_splitTorusGL2_conj_splitTorusGL2]
  simp [archFlowMatrix, mul_assoc] at h ⊢
  with_reducible exact h

/-- Complex place, one later factor at the same place: the complex analogue of
the first real example, with increment `unipotentGL2 (s * exp (-2b))` over `ℂ`. -/
example (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex)
    (a b s : ℝ) :
    archFlowAtComplex K hv .E (a + s) * archFlowAtComplex K hv .H b
      = archFlowAtComplex K hv .E a * archFlowAtComplex K hv .H b *
          archComplexGLAt K hv (unipotentGL2 ((s : ℂ) * Complex.exp (-(2 * (b : ℂ))))) := by
  have h := flowChart_add_single_eq_mul_conj K
    [Sum.inr ⟨v, hv, .E⟩, Sum.inr ⟨v, hv, .H⟩] ⟨0, by simp⟩ ![a, b] s
  rw [← splitTorusGL2Complex_conj_unipotentGL2]
  simp [archFlowMatrixComplex, mul_assoc] at h ⊢
  with_reducible exact h

/-- Complex place, filtering, in the `I` directions: the earlier factor at `v`,
the later real factor and the later factor at another complex place `v'` drop
out; the last factor `iH a₄` at `v` conjugates the increment `iE s`. -/
example (K : Type) [Field K] [NumberField K] (v v' w : InfinitePlace K)
    (hv : v.IsComplex) (hv' : v'.IsComplex) (hw : w.IsReal) (hvv : v' ≠ v)
    (a₀ a₁ a₂ a₃ a₄ s : ℝ) :
    archFlowAtComplex K hv .H a₀ * archFlowAtComplex K hv .iE (a₁ + s) *
        archFlowAt K hw .H a₂ * archFlowAtComplex K hv' .H a₃ * archFlowAtComplex K hv .iH a₄
      = archFlowAtComplex K hv .H a₀ * archFlowAtComplex K hv .iE a₁ *
          archFlowAt K hw .H a₂ * archFlowAtComplex K hv' .H a₃ *
          archFlowAtComplex K hv .iH a₄ *
          archComplexGLAt K hv (unipotentGL2
            ((s : ℂ) * Complex.I * Complex.exp (-(2 * ((a₄ : ℂ) * Complex.I))))) := by
  have h := flowChart_add_single_eq_mul_conj K
    [Sum.inr ⟨v, hv, .H⟩, Sum.inr ⟨v, hv, .iE⟩, Sum.inl ⟨w, hw, .H⟩,
      Sum.inr ⟨v', hv', .H⟩, Sum.inr ⟨v, hv, .iH⟩] ⟨1, by simp⟩ ![a₀, a₁, a₂, a₃, a₄] s
  rw [← splitTorusGL2Complex_conj_unipotentGL2]
  simp [archFlowMatrixComplex, hvv, mul_assoc] at h ⊢
  with_reducible exact h

/-- Complex place, order: the complex analogue of the real order example. -/
example (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex)
    (a c b s : ℝ) :
    archFlowAtComplex K hv .H (a + s) * archFlowAtComplex K hv .E c *
        archFlowAtComplex K hv .H b
      = archFlowAtComplex K hv .H a * archFlowAtComplex K hv .E c *
          archFlowAtComplex K hv .H b *
          archComplexGLAt K hv (splitTorusGL2Complex (s : ℂ) *
            unipotentGL2 ((c : ℂ) * (1 - Complex.exp (-(2 * (s : ℂ)))) *
              Complex.exp (-(2 * (b : ℂ))))) := by
  have h := flowChart_add_single_eq_mul_conj K
    [Sum.inr ⟨v, hv, .H⟩, Sum.inr ⟨v, hv, .E⟩, Sum.inr ⟨v, hv, .H⟩] ⟨0, by simp⟩
    ![a, c, b] s
  rw [← unipotent_splitTorusGL2Complex_conj_splitTorusGL2Complex]
  simp [archFlowMatrixComplex, mul_assoc] at h ⊢
  with_reducible exact h

end AutomorphicFormArchFlowChartTest
