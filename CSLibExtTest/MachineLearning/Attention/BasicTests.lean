/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Attention.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for softmax attention basics
-/

set_option autoImplicit false

open Cslib.MachineLearning
open Cslib.MachineLearning.Attention

namespace CSLibExtTest.MachineLearning.Attention.BasicTests

/-- Softmax weights are nonnegative, as an example. -/
example {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : 0 ≤ softmax x i :=
  softmax_nonneg x i

/-- Softmax weights over three indices sum to one. -/
example (x : Fin 3 → ℝ) : (∑ i, softmax x i) = 1 :=
  sum_softmax x

/-- Constant zero logits on two indices give uniform softmax weights. This
checks the definition directly, not only the normalization theorem. -/
example (i : Fin 2) : softmax (fun _ => (0 : ℝ)) i = 1 / 2 := by
  norm_num [softmax, Real.softmax, Finset.sum_const, Finset.card_univ]

/-- With zero query/key matrices, all logits are zero, so a two-token,
one-dimensional attention layer averages the two value rows `1` and `2`. -/
example : attn (![![1], ![2]] : Fin 2 → Fin 1 → ℝ)
    (0 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) = fun _ => ![3 / 2] := by
  funext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [attn, attentionWeights, softmax, Real.softmax, Matrix.vecMul, dotProduct,
      Finset.sum_const, Finset.card_univ]

/-- A nonzero query/key example with `dk = 4`: for token rows `1` and `2`, and
query/key matrices selecting the first key coordinate, the scaled logits for
query token `0` are `1 / 2` and `1`, giving the displayed nonuniform weight
on token `1`. -/
example : attentionWeights (![![1], ![2]] : Fin 2 → Fin 1 → ℝ)
    (fun _ (j : Fin 4) => if j = 0 then (1 : ℝ) else 0)
    (fun _ (j : Fin 4) => if j = 0 then (1 : ℝ) else 0) 0 1
    = Real.exp 1 / (Real.exp (1 / 2) + Real.exp 1) := by
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [attentionWeights, softmax, Real.softmax, Matrix.vecMul, dotProduct, hsqrt,
    Fin.sum_univ_two]

/-- Permutation equivariance instantiated for three tokens. -/
example (X : Fin 3 → Fin 2 → ℝ) (WQ WK : Matrix (Fin 2) (Fin 2) ℝ)
    (WV : Matrix (Fin 2) (Fin 2) ℝ) (σ : Equiv.Perm (Fin 3)) :
    attn (fun i => X (σ i)) WQ WK WV = fun i => attn X WQ WK WV (σ i) :=
  attn_perm X WQ WK WV σ

/-- Every three-token attention output row is in the value-row convex hull. -/
example (X : Fin 3 → Fin 2 → ℝ) (WQ WK : Matrix (Fin 2) (Fin 2) ℝ)
    (WV : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 3) :
    attn X WQ WK WV i ∈
      convexHull ℝ (Set.range fun j => Matrix.vecMul (X j) WV) :=
  attn_mem_convexHull X WQ WK WV i

end CSLibExtTest.MachineLearning.Attention.BasicTests
