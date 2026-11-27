/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Logic.Equiv.Basic
public import MathlibExt.Analysis.SpecialFunctions.LogSumExp

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Softmax attention basics

This file defines finite softmax and single-head scaled dot-product attention
without positional encoding or a mask. The key dimension is required to be
nonzero in the attention definitions, matching the usual `1 / √dk` scaling.
The main facts are that softmax weights are nonnegative and sum to one on a
nonempty index set, attention is permutation-equivariant in the token index,
and every output row is a convex combination of the value rows.

## Main declarations

* `softmax`: normalized exponential weights (the shared `Real.softmax` API).
* `softmax_nonneg`, `sum_softmax`: basic softmax weight facts.
* `Attention.attentionWeights`, `Attention.attn`: attention weights and output.
* `Attention.attn_perm`: permutation equivariance.
* `Attention.attn_mem_convexHull`: outputs lie in the convex hull of value rows.

## References

* Ashish Vaswani et al., "Attention Is All You Need" (2017), section 3.2.1,
  for scaled dot-product attention `softmax(QKᵀ / √dₖ)V`. This file formalizes
  the single-head, unmasked, position-free special case with rows of `X`
  projected by `WQ`, `WK`, and `WV`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning

/-- Softmax over a finite index set: the shared `Real.softmax` API.

If the index set is empty this uses Lean's totalized division; the
normalization theorem below is stated for a nonempty index set. -/
noncomputable def softmax {ι : Type*} [Fintype ι] (x : ι → ℝ) : ι → ℝ :=
  Real.softmax x

/-- Softmax weights are nonnegative. -/
theorem softmax_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    0 ≤ softmax x i := by
  unfold softmax Real.softmax
  exact div_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

/-- Softmax weights sum to one over a nonempty finite index set. -/
theorem sum_softmax {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    (∑ i, softmax x i) = 1 :=
  Real.sum_softmax x

namespace Attention

/-- Scaled dot-product attention weights for query token `i`.

Rows of `X` are token vectors. `WQ` and `WK` are the query and key matrices.
There is no positional encoding and no mask. The key dimension `dk` is
nonzero, as required by the usual scaling factor `1 / √dk`. -/
noncomputable def attentionWeights {n d dk : ℕ} [NeZero dk]
    (X : Fin n → Fin d → ℝ) (WQ WK : Matrix (Fin d) (Fin dk) ℝ)
    (i : Fin n) : Fin n → ℝ :=
  softmax fun j =>
    dotProduct (Matrix.vecMul (X i) WQ) (Matrix.vecMul (X j) WK) /
      Real.sqrt (dk : ℝ)

/-- Single-head scaled dot-product attention.

The output row for token `i` is the softmax-weighted sum of the value rows
`Matrix.vecMul (X j) WV`. The key dimension `dk` is nonzero. -/
noncomputable def attn {n d dk dv : ℕ} [NeZero dk]
    (X : Fin n → Fin d → ℝ) (WQ WK : Matrix (Fin d) (Fin dk) ℝ)
    (WV : Matrix (Fin d) (Fin dv) ℝ) : Fin n → (Fin dv → ℝ) :=
  fun i => ∑ j, attentionWeights X WQ WK i j • Matrix.vecMul (X j) WV

/-- Softmax self-attention without positional encoding or a mask is
permutation-equivariant in the token index. -/
theorem attn_perm {n d dk dv : ℕ} [NeZero dk]
    (X : Fin n → Fin d → ℝ) (WQ WK : Matrix (Fin d) (Fin dk) ℝ)
    (WV : Matrix (Fin d) (Fin dv) ℝ) (σ : Equiv.Perm (Fin n)) :
    attn (fun i => X (σ i)) WQ WK WV = fun i => attn X WQ WK WV (σ i) := by
  funext i
  have hw : ∀ j, attentionWeights (fun i => X (σ i)) WQ WK i j
      = attentionWeights X WQ WK (σ i) (σ j) := by
    intro j
    unfold attentionWeights softmax Real.softmax
    congr 1
    exact Equiv.sum_comp σ (fun k => Real.exp
      (dotProduct (Matrix.vecMul (X (σ i)) WQ) (Matrix.vecMul (X k) WK) /
        Real.sqrt (↑dk : ℝ)))
  simp only [attn]
  rw [← Equiv.sum_comp σ
    (fun j => attentionWeights X WQ WK (σ i) j • Matrix.vecMul (X j) WV)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hw j]

/-- Each attention output row lies in the convex hull of the value rows. -/
theorem attn_mem_convexHull {n d dk dv : ℕ} [NeZero dk]
    (X : Fin n → Fin d → ℝ) (WQ WK : Matrix (Fin d) (Fin dk) ℝ)
    (WV : Matrix (Fin d) (Fin dv) ℝ) (i : Fin n) :
    attn X WQ WK WV i ∈
      convexHull ℝ (Set.range fun j => Matrix.vecMul (X j) WV) := by
  have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ attentionWeights X WQ WK i j :=
    fun j _ => softmax_nonneg _ j
  have hsum : ∑ j, attentionWeights X WQ WK i j = 1 :=
    @sum_softmax (Fin n) _ ⟨i⟩ _
  have hpos : 0 < ∑ j, attentionWeights X WQ WK i j := by
    rw [hsum]
    exact one_pos
  have hz : ∀ j ∈ Finset.univ,
      Matrix.vecMul (X j) WV ∈ Set.range (fun j => Matrix.vecMul (X j) WV) :=
    fun j _ => Set.mem_range_self j
  have hmem := Finset.centerMass_mem_convexHull Finset.univ hnonneg hpos hz
  rw [Finset.centerMass_eq_of_sum_1 Finset.univ _ hsum] at hmem
  simpa [attn] using hmem

end Attention

end Cslib.MachineLearning
