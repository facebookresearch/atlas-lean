/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
import CSLibExt.Complexity.Algebraic.CircuitComposition
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Naive upper bound for rectangular matrix multiplication

The private product circuit `naiveProducts` computes every entry product of an `m × r`
matrix by an `r × n` matrix with one multiplication gate each. Substituting it into the
private summation circuit `naiveSum` gives the private naive circuit `naiveCircuit`,
which multiplies an `m × r` matrix by an `r × n` matrix with
`(m * n) * r + (m * n) * (2 * r)` gates. Since the rounded inner dimension `⌈n ^ k⌉`
is at most twice `n ^ k` for `n ≥ 1` and `k ≥ 0`, this proves `rectangularNaiveUpper`:
over every field, the rectangular circuit exponent at aspect `k ≥ 0` is at most `2 + k`.

Reference: M. Christandl, F. Le Gall, V. Lysikov and J. Zuiddam, "Barriers for
rectangular matrix multiplication", _Computational Complexity_ 34 (2025), article 4;
arXiv:2003.03019.
-/

set_option autoImplicit false

namespace Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted

open Cslib.Complexity.Algebraic
open MatrixMultiplicationExponent

universe u

private def naiveProducts (F : Type u) (m r n : ℕ) :
    ArithmeticCircuit F ((Fin m × Fin r) ⊕ (Fin r × Fin n)) (Fin m × Fin n × Fin r) where
  size := (m * n) * r
  gate i :=
    .mul (.input (.inl ((finProdFinEquiv.symm (finProdFinEquiv.symm i).1).1,
      (finProdFinEquiv.symm i).2)))
      (.input (.inr ((finProdFinEquiv.symm i).2,
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).1).2)))
  output ijt := .node (finProdFinEquiv (finProdFinEquiv (ijt.1, ijt.2.1), ijt.2.2))

private theorem naiveProducts_size (F : Type u) (m r n : ℕ) :
    (naiveProducts F m r n).size = (m * n) * r := rfl

private theorem naiveProducts_evaluate (F : Type u) [Field F] (m r n : ℕ)
    (x : ((Fin m × Fin r) ⊕ (Fin r × Fin n)) → F)
    (i : Fin m) (j : Fin n) (t : Fin r) :
    (naiveProducts F m r n).evaluate x (i, j, t) =
      x (.inl (i, t)) * x (.inr (t, j)) := by
  simp [naiveProducts, ArithmeticCircuit.evaluate, ArithmeticCircuit.evaluateNode,
    ArithmeticGate.evaluate, ArithmeticOperand.evaluate]

private noncomputable def naiveSum (F : Type u) [Field F] (m r n : ℕ) :
    ArithmeticCircuit F (Fin m × Fin n × Fin r) (Fin m × Fin n) :=
  ArithmeticCircuit.linearCombination (fun _ _ => (1 : F)) (fun ij t => (ij.1, ij.2, t))

private noncomputable def naiveCircuit (F : Type u) [Field F] (m r n : ℕ) :
    MatrixArithmeticCircuit F m r n :=
  (naiveSum F m r n).subst (naiveProducts F m r n)

private theorem naiveCircuit_size (F : Type u) [Field F] (m r n : ℕ) :
    (naiveCircuit F m r n).size = (m * n) * r + (m * n) * (2 * r) := by
  simp only [naiveCircuit, naiveSum, ArithmeticCircuit.size_subst,
    ArithmeticCircuit.size_linearCombination, naiveProducts_size,
    Fintype.card_prod, Fintype.card_fin]

private theorem naiveCircuit_correct (F : Type u) [Field F] (m r n : ℕ) :
    IsMatrixMultiplication (naiveCircuit F m r n) := by
  intro A B i j
  simp only [naiveCircuit, naiveSum, ArithmeticCircuit.evaluate_subst,
    ArithmeticCircuit.evaluate_linearCombination, one_mul, naiveProducts_evaluate,
    matrixInput]
  exact Matrix.mul_apply.symm

private theorem innerDimension_le_two_rpow (n : ℕ) (k : ℝ) (hn : 1 ≤ n) (hk : 0 ≤ k) :
    (rectangularInnerDimension n k : ℝ) ≤ 2 * (n : ℝ) ^ k := by
  unfold rectangularInnerDimension
  exact Nat.ceil_le_two_mul ((by norm_num : (2⁻¹ : ℝ) ≤ 1).trans
    (Real.one_le_rpow (by exact_mod_cast hn) hk))

/-- **Naive bound for rectangular matrix multiplication.** For every field $F$ and every real
$k \ge 0$, the rectangular matrix multiplication exponent of the arithmetic-circuit model at
aspect $k$ is at most $2 + k$.

Source: CLLZ rectangular naive upper bound. -/
public theorem rectangularNaiveUpper :
    ∀ (F : Type u) [Field F] (k : ℝ), 0 ≤ k →
      rectangularCircuitExponent F k ≤ ENNReal.ofReal (2 + k)
    := by
  intro F _ k hk
  apply rectangularCircuitExponent_le_of_admissible
  refine ⟨hk, by linarith, ?_⟩
  intro ε hε
  refine ⟨6, by norm_num, 1, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveCircuit F n (rectangularInnerDimension n k) n,
    naiveCircuit_correct F n (rectangularInnerDimension n k) n, ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hr := innerDimension_le_two_rpow n k hn hk
  have hsize : ((naiveCircuit F n (rectangularInnerDimension n k) n).size : ℝ)
      = 3 * ((n : ℝ) * (n : ℝ) * (rectangularInnerDimension n k : ℝ)) := by
    rw [naiveCircuit_size]
    push_cast
    ring
  have hnn : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) := mul_nonneg hnpos.le hnpos.le
  have hle : 3 * ((n : ℝ) * (n : ℝ) * (rectangularInnerDimension n k : ℝ))
      ≤ 3 * ((n : ℝ) * (n : ℝ) * (2 * (n : ℝ) ^ k)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hnn) (by norm_num)
  have hexp : (3 : ℝ) * ((n : ℝ) * (n : ℝ) * (2 * (n : ℝ) ^ k)) = 6 * (n : ℝ) ^ (2 + k) := by
    rw [Real.rpow_add hnpos, Real.rpow_two]
    ring
  have hmono : (6 : ℝ) * (n : ℝ) ^ (2 + k) ≤ 6 * (n : ℝ) ^ ((2 + k) + ε) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by norm_num)
  rw [hsize]
  exact hle.trans (hexp.trans_le hmono)

end Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted
