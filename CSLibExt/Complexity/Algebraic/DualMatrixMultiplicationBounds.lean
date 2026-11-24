/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
import Mathlib.Tactic.Linarith

/-!
# Upper bound on the dual matrix multiplication exponent

`upperBoundOne` bounds the dual exponent by counting the distinct matrix inputs read by the gates.
-/

set_option autoImplicit false

namespace Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted

open MatrixMultiplicationExponent Filter

universe u

private def operandAt {F A : Type*} {n : ℕ} : ArithmeticGate F A n → Bool → ArithmeticOperand F A n
  | .add a b | .sub a b | .mul a b => fun side => if side then b else a

private theorem gate_congr {F A : Type*} [Field F] {n : ℕ} (g : ArithmeticGate F A n)
    {x y : A → F} {v w : Fin n → F}
    (h : ∀ s, (operandAt g s).evaluate x v = (operandAt g s).evaluate y w) :
    g.evaluate x v = g.evaluate y w := by
  have hl := h false
  have hr := h true
  cases g <;> simp_all [operandAt, ArithmeticGate.evaluate]

-- Agreement on all inputs read by gates propagates through the circuit in gate order.
private theorem node_congr {F A B : Type*} [Field F] (c : ArithmeticCircuit F A B)
    {x y : A → F}
    (h : ∀ i s a, operandAt (c.gate i) s = .input a → x a = y a) (i : Fin c.size) :
    c.evaluateNode x i = c.evaluateNode y i := by
  rw [ArithmeticCircuit.evaluateNode, ArithmeticCircuit.evaluateNode]
  apply gate_congr
  intro s
  cases he : operandAt (c.gate i) s with
  | constant => rfl
  | input a => exact h i s a he
  | node j => exact node_congr c h ⟨j.val, j.isLt.trans i.isLt⟩
termination_by i.val
decreasing_by exact j.isLt

-- A single entry on the right makes any chosen entry on the left visible at an output.
private theorem left_input_read {F : Type*} [Field F] {m r n : ℕ}
    {c : MatrixArithmeticCircuit F m r n} (hc : IsMatrixMultiplication c)
    (j : Fin n) (p : Fin m × Fin r) :
    ∃ t : Fin c.size × Bool, operandAt (c.gate t.1) t.2 = .input (.inl p) := by
  classical
  by_contra h
  let A := Matrix.single p.1 p.2 (1 : F)
  let B := Matrix.single p.2 j (1 : F)
  have agree : ∀ i s a, operandAt (c.gate i) s = .input a →
      matrixInput A B a = matrixInput 0 B a := by
    intro i s a ha
    cases a with
    | inr => rfl
    | inl q =>
      have hpq : ¬ (p.1 = q.1 ∧ p.2 = q.2) := by
        intro he
        exact h ⟨(i, s), Prod.ext he.1 he.2 ▸ ha⟩
      simp [matrixInput, A, Matrix.single_apply, hpq]
  obtain ⟨i, hi⟩ := hc.output_is_node p.2 p.1 j
  have same : c.evaluate (matrixInput A B) (p.1, j) = c.evaluate (matrixInput 0 B) (p.1, j) := by
    simpa [ArithmeticCircuit.evaluate, hi, ArithmeticOperand.evaluate] using node_congr c agree i
  rw [hc A B, hc 0 B] at same
  simp [A, B] at same

private theorem left_input_cost_le {F : Type*} [Field F] {m r n : ℕ}
    {c : MatrixArithmeticCircuit F m r n} (hc : IsMatrixMultiplication c) (j : Fin n) :
    m * r ≤ c.size * 2 := by
  choose slot hslot using left_input_read hc j
  have hinj : Function.Injective slot := by
    intro p q he
    have hq := hslot q
    rw [← he] at hq
    exact Sum.inl.inj (ArithmeticOperand.input.inj ((hslot p).symm.trans hq))
  simpa using Fintype.card_le_of_injective slot hinj

/-- **Dual exponent at most one.** For every field $F$, the dual matrix multiplication
exponent $\alpha(F)$ of the arithmetic-circuit model satisfies $\alpha(F) \le 1$.

Source: C15b, CLLZ2025 Figure 2, the general upper bound, not a method-specific barrier. -/
public theorem upperBoundOne :
    ∀ (F : Type u) [Field F], dualCircuitExponent F ≤ 1 := by
  intro F _
  apply dualCircuitExponent_le
  intro k hk htwo
  suffices k ≤ 1 by simpa using ENNReal.ofReal_le_ofReal this
  by_contra! hlarge
  let ε := (k - 1) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hadm : HasRectangularCircuitExponent F k 2 :=
    (rectangularCircuitExponent_le_iff F hk (by norm_num)).mp (by simp [htwo])
  obtain ⟨C, _, N, hN, hb⟩ := hadm.2.2 ε hε
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hnC, hn⟩ :=
    ((ht.eventually (eventually_gt_atTop (2 * C))).and (eventually_ge_atTop N)).exists
  obtain ⟨c, hc, hs⟩ := hb n hn
  have hnpos : 0 < n := hN.trans hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hcost : (n : ℝ) * rectangularInnerDimension n k ≤ c.size * (2 : ℝ) := by
    exact_mod_cast left_input_cost_le hc ⟨0, hnpos⟩
  have hpow : (n : ℝ) ^ (2 + ε) * (n : ℝ) ^ ε ≤ c.size * (2 : ℝ) := calc
    _ = (n : ℝ) ^ (1 + k) := by
      rw [← Real.rpow_add hnreal]
      congr 1
      dsimp [ε]
      ring
    _ = (n : ℝ) * (n : ℝ) ^ k := by rw [Real.rpow_add hnreal, Real.rpow_one]
    _ ≤ (n : ℝ) * rectangularInnerDimension n k :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil _) hnreal.le
    _ ≤ _ := hcost
  have hlt := mul_lt_mul_of_pos_left hnC (Real.rpow_pos_of_pos hnreal (2 + ε))
  linarith

end Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted
