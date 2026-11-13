/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteMarkovChainConvergence
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Topology.Basic

import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Constructions

/-!
# DeGroot opinion dynamics and consensus

This module formalizes the DeGroot model of naive social learning: agents hold
real-valued beliefs and repeatedly replace their belief by a weighted average of their
neighbors' beliefs, `p(t) = T p(t-1)`, where `T` is a row-stochastic influence matrix.
For a primitive `T`, opinions converge to a consensus: every agent's belief tends to the
same stationary weighted average of the initial beliefs.

The stationary weights `π` are ASSUMED (supplied as a hypothesis), not proved here.
For primitive `T`, existence already follows at base from Atlas's
`Matrix.IsIrreducible.perron_frobenius` applied to `Tᵀ`. Existence of `π` is residual
scope only for general row-stochastic matrices, not for the primitive case here.

## Main results

- `degrootOpinion`: belief vector after `t` rounds, `(T ^ t) *ᵥ x₀`.
- `tendsto_degrootOpinion`: each agent's opinion tends to `π ⬝ᵥ x₀`.
- `tendsto_degrootOpinion_consensus`: opinion vectors tend to the constant consensus.
- `tendsto_degrootOpinion_of_mem_doublyStochastic`: doubly-stochastic case tends to
  the arithmetic mean.

## References

- B. Golub and M. O. Jackson, "Naive Learning in Social Networks and the Wisdom of
  Crowds", American Economic Journal: Microeconomics 2(1) (2010), 112-149. Lemma
  numbers cited here follow the authors' manuscript.
-/

@[expose] public section

namespace MathlibExt.Probability.Networks

open scoped Matrix
open MathlibExt.Probability.FiniteMarkovChainConvergence

/-- DeGroot opinion dynamics (Golub-Jackson equation (1)): the belief vector after `t`
rounds of updating, `(T ^ t) *ᵥ x₀`. No hypotheses on `T` are needed to define it. -/
public def degrootOpinion {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (x₀ : n → ℝ) (t : ℕ) : n → ℝ :=
  (T ^ t) *ᵥ x₀

/-- At time `0` opinions are the initial beliefs. -/
@[simp]
public theorem degrootOpinion_zero {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℝ} {x₀ : n → ℝ} : degrootOpinion T x₀ 0 = x₀ := by
  simp [degrootOpinion, Matrix.one_mulVec]

/-- The DeGroot updating rule `p(t) = T p(t-1)`. -/
@[simp]
public theorem degrootOpinion_succ {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℝ} {x₀ : n → ℝ} (t : ℕ) :
    degrootOpinion T x₀ (t + 1) = T *ᵥ degrootOpinion T x₀ t := by
  simp [degrootOpinion, pow_succ', Matrix.mulVec_mulVec]

/-- Golub-Jackson Lemma 3 (convergence clause): for a primitive stochastic influence
matrix with stationary weights `π`, every agent's opinion tends to the stationary
weighted average `∑ j, π j * x₀ j`, which is the same for every agent. The vector `π`
is ASSUMED (supplied as a hypothesis), not proved here; for primitive `T`, existence
already follows at base from Atlas's `Matrix.IsIrreducible.perron_frobenius` applied
to `Tᵀ`. Positivity and uniqueness of `π` are `stationary_pos` and `stationary_unique`
in `MathlibExt.Probability.FiniteMarkovChainConvergence`. -/
public theorem tendsto_degrootOpinion {n : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℝ} (hT : T ∈ Matrix.rowStochastic ℝ n) (hprim : T.IsPrimitive)
    {π : n → ℝ} (hπ0 : ∀ j, 0 ≤ π j) (hπ1 : ∑ j, π j = 1) (hstat : π ᵥ* T = π)
    (x₀ : n → ℝ) (i : n) :
    Filter.Tendsto (fun t => degrootOpinion T x₀ t i) Filter.atTop
      (nhds (π ⬝ᵥ x₀)) := by
  have hterm : ∀ j : n, Filter.Tendsto (fun t => (T ^ t) i j * x₀ j) Filter.atTop
      (nhds (π j * x₀ j)) :=
    fun j => Filter.Tendsto.mul_const (x₀ j)
      (tendsto_pow_apply hT hprim hπ0 hπ1 hstat i j)
  change Filter.Tendsto (fun t => ∑ j, (T ^ t) i j * x₀ j) Filter.atTop
    (nhds (∑ j, π j * x₀ j))
  simpa using tendsto_finsetSum (Finset.univ : Finset n) (fun j _ => hterm j)

/-- Golub-Jackson Lemma 3 ("all entries of the limit are the same"): the opinion vectors
converge in the product topology on `n → ℝ` to the constant consensus vector. -/
public theorem tendsto_degrootOpinion_consensus {n : Type*} [Fintype n]
    [DecidableEq n] {T : Matrix n n ℝ} (hT : T ∈ Matrix.rowStochastic ℝ n)
    (hprim : T.IsPrimitive) {π : n → ℝ} (hπ0 : ∀ j, 0 ≤ π j) (hπ1 : ∑ j, π j = 1)
    (hstat : π ᵥ* T = π) (x₀ : n → ℝ) :
    Filter.Tendsto (degrootOpinion T x₀) Filter.atTop (nhds (fun _ => π ⬝ᵥ x₀)) := by
  rw [tendsto_pi_nhds]
  exact fun i => tendsto_degrootOpinion hT hprim hπ0 hπ1 hstat x₀ i

/-- A derived application (not a source clause): for a doubly-stochastic primitive
influence matrix, every agent's opinion tends to the arithmetic mean of the initial
beliefs. The uniform weights are stationary because the columns sum to 1. -/
public theorem tendsto_degrootOpinion_of_mem_doublyStochastic {n : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n] {T : Matrix n n ℝ}
    (hT : T ∈ doublyStochastic ℝ n) (hprim : T.IsPrimitive) (x₀ : n → ℝ)
    (i : n) :
    Filter.Tendsto (fun t => degrootOpinion T x₀ t i) Filter.atTop
      (nhds ((∑ j, x₀ j) / Fintype.card n)) := by
  have hcard : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hrow : T ∈ Matrix.rowStochastic ℝ n :=
    (mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic.mp
      hT).1
  have hstat : (fun _ => (Fintype.card n : ℝ)⁻¹) ᵥ* T =
      fun _ => (Fintype.card n : ℝ)⁻¹ := by
    funext j
    change ∑ k, (Fintype.card n : ℝ)⁻¹ * T k j = (Fintype.card n : ℝ)⁻¹
    rw [← Finset.mul_sum, sum_col_of_mem_doublyStochastic hT j, mul_one]
  have h1 : ∑ _ : n, (Fintype.card n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (ne_of_gt hcard)]
  have hlim :=
    tendsto_degrootOpinion hrow hprim (π := fun _ => (Fintype.card n : ℝ)⁻¹)
      (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) h1 hstat x₀ i
  have hdot : (fun _ => (Fintype.card n : ℝ)⁻¹) ⬝ᵥ x₀ =
      (∑ j, x₀ j) / Fintype.card n := by
    change (∑ j, (Fintype.card n : ℝ)⁻¹ * x₀ j) = _
    rw [← Finset.mul_sum, inv_mul_eq_div]
  rw [hdot] at hlim
  exact hlim

end MathlibExt.Probability.Networks
