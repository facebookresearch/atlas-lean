/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
import CSLibExt.Complexity.Algebraic.CircuitComposition

/-!
# Naive rectangular matrix multiplication

Accumulating one outer product for each inner index gives a circuit with two gates per
summand per output entry. This proves the exponent bound `rectangularNaiveUpper`.
-/

namespace Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted

universe u

private abbrev Entry (n : ℕ) := Fin n × Fin n

private abbrev Input (n r : ℕ) := (Fin n × Fin r) ⊕ (Fin r × Fin n)

-- A layer keeps selected inputs for free and computes one new gate per output entry.
private def layer {F : Type u} {I P : Type} {n : ℕ} (keep : P → I)
    (g : Entry n → (t : ℕ) → ArithmeticGate F I t) :
    ArithmeticCircuit F I (P ⊕ Entry n) where
  size := n * n
  gate i := g (finProdFinEquiv.symm i) i.val
  output := Sum.elim (fun p => .input (keep p)) (fun ij => .node (finProdFinEquiv ij))

-- Keep both input matrices available alongside the dot products accumulated over s.
private theorem partialCircuit (F : Type u) [Field F] (n r : ℕ) (s : Finset (Fin r)) :
    ∃ c : ArithmeticCircuit F (Input n r) (Input n r ⊕ Entry n),
      c.size = 2 * (n * n) * s.card ∧ ∀ x,
        (∀ a, c.evaluate x (.inl a) = x a) ∧
        ∀ ij, c.evaluate x (.inr ij) = ∑ t ∈ s, x (.inl (ij.1, t)) * x (.inr (t, ij.2)) := by
  induction s using Finset.induction_on with
  | empty =>
    let c : ArithmeticCircuit F (Input n r) (Input n r ⊕ Entry n) :=
      ⟨0, fun i => i.elim0, Sum.elim .input (fun _ => .constant 0)⟩
    exact ⟨c, by simp [c], fun x => ⟨fun _ => rfl, fun ij => by
      simp [c, ArithmeticCircuit.evaluate, ArithmeticOperand.evaluate]⟩⟩
  | @insert t s ht ih =>
    obtain ⟨c, hs, hc⟩ := ih
    let products : ArithmeticCircuit F (Input n r ⊕ Entry n) ((Input n r ⊕ Entry n) ⊕ Entry n) :=
      layer id fun ij _ => .mul (.input (.inl (.inl (ij.1, t)))) (.input (.inl (.inr (t, ij.2))))
    let sums : ArithmeticCircuit F ((Input n r ⊕ Entry n) ⊕ Entry n) (Input n r ⊕ Entry n) :=
      layer (Sum.inl ∘ Sum.inl) fun ij _ => .add (.input (.inr ij)) (.input (.inl (.inr ij)))
    have product_value x (ij : Entry n) : products.evaluate x (.inr ij) =
        x (.inl (.inl (ij.1, t))) * x (.inl (.inr (t, ij.2))) := by
      change products.evaluateNode x (finProdFinEquiv ij) = _
      rw [ArithmeticCircuit.evaluateNode.eq_1 products x (finProdFinEquiv ij)]
      simp [products, layer, ArithmeticGate.evaluate, ArithmeticOperand.evaluate]
    have sum_value x (ij : Entry n) : sums.evaluate x (.inr ij) =
        x (.inr ij) + x (.inl (.inr ij)) := by
      change sums.evaluateNode x (finProdFinEquiv ij) = _
      rw [ArithmeticCircuit.evaluateNode.eq_1 sums x (finProdFinEquiv ij)]
      simp [sums, layer, ArithmeticGate.evaluate, ArithmeticOperand.evaluate]
    refine ⟨sums.subst (products.subst c), ?_, fun x => ⟨?_, ?_⟩⟩
    · simp only [ArithmeticCircuit.size_subst, hs, products, sums, layer,
        Finset.card_insert_of_notMem ht]
      ring
    · intro a
      simp only [ArithmeticCircuit.evaluate_subst]
      exact (hc x).1 a
    · intro ij
      simp only [ArithmeticCircuit.evaluate_subst, sum_value, product_value]
      change c.evaluate x (.inl _) * c.evaluate x (.inl _) + c.evaluate x (.inr ij) = _
      simp [(hc x).1, (hc x).2, ht]

private theorem naiveCircuit (F : Type u) [Field F] (n r : ℕ) :
    ∃ c : MatrixArithmeticCircuit F n r n, IsMatrixMultiplication c ∧
      c.size = 2 * (n * n) * r := by
  obtain ⟨c, hs, hc⟩ := partialCircuit F n r Finset.univ
  let read : ArithmeticCircuit F (Input n r ⊕ Entry n) (Entry n) :=
    ⟨0, fun i => i.elim0, fun ij => .input (.inr ij)⟩
  refine ⟨read.subst c, ?_, by simpa [ArithmeticCircuit.size_subst, read] using hs⟩
  intro A B i j
  rw [ArithmeticCircuit.evaluate_subst]
  exact (hc (matrixInput A B)).2 (i, j)

/-- **Naive bound for rectangular matrix multiplication.** For every field $F$ and every real
$k \ge 0$, the rectangular matrix multiplication exponent of the arithmetic-circuit model at
aspect $k$ is at most $2 + k$.

Source: CLLZ rectangular naive upper bound; a general finite circuit construction is missing. -/
public theorem rectangularNaiveUpper :
    ∀ (F : Type u) [Field F] (k : ℝ), 0 ≤ k →
      rectangularCircuitExponent F k ≤ ENNReal.ofReal (2 + k) := by
  intro F _ k hk
  apply rectangularCircuitExponent_le_of_admissible
  refine ⟨hk, by linarith, fun ε hε => ⟨4, by norm_num, 1, by norm_num, ?_⟩⟩
  intro n hn
  obtain ⟨c, hc, hs⟩ :=
    naiveCircuit F n (MatrixMultiplicationExponent.rectangularInnerDimension n k)
  refine ⟨c, hc, ?_⟩
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow := Real.one_le_rpow hn' hk
  have hceil : (MatrixMultiplicationExponent.rectangularInnerDimension n k : ℝ) ≤
      2 * (n : ℝ) ^ k := by
    change (⌈(n : ℝ) ^ k⌉₊ : ℝ) ≤ _
    linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ k)]
  rw [hs]
  push_cast
  calc
    _ ≤ 2 * ((n : ℝ) * n) * (2 * (n : ℝ) ^ k) := by gcongr
    _ = 4 * (n : ℝ) ^ (2 + k) := by
      rw [Real.rpow_add (by linarith : 0 < (n : ℝ)), Real.rpow_two]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn' (by linarith)) (by norm_num)

end Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted
