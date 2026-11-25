/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Matrix mutation and seed mutation

Coefficient-free cluster algebras in the sense of Fomin and Zelevinsky: matrix mutation
(Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*,
arXiv:1608.05735v5, Lemma 2.7.3 and Definition 2.7.6), skew-symmetrizable matrices
(Definition 2.7.4), seed mutation (Definition 3.1.3, with no frozen variables, i.e. `m = n`),
iterated mutation along a word of directions, and the set of cluster variables of the seed
pattern through a seed.

Main result: `matrixMutation_matrixMutation`, matrix mutation is an involution
(Exercise 2.7.7(2)).
-/

@[expose] public section

namespace MathlibExt.RingTheory.ClusterAlgebra

variable {n : Type*} [DecidableEq n]

/-- **Matrix mutation.** The mutation of an integer square matrix `B` in direction `k` is the
matrix `B'` with `b'ᵢⱼ = -bᵢⱼ` if `i = k` or `j = k`, `b'ᵢⱼ = bᵢⱼ + bᵢₖ bₖⱼ` if `bᵢₖ > 0` and
`bₖⱼ > 0`, `b'ᵢⱼ = bᵢⱼ - bᵢₖ bₖⱼ` if `bᵢₖ < 0` and `bₖⱼ < 0`, and `b'ᵢⱼ = bᵢⱼ` otherwise
(Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*,
arXiv:1608.05735v5, Lemma 2.7.3, equation (2.7.1), and Definition 2.7.6, square case
`m = n`). -/
def matrixMutation (k : n) (B : Matrix n n ℤ) : Matrix n n ℤ :=
  Matrix.of fun i j =>
    if i = k ∨ j = k then -B i j
    else if 0 < B i k ∧ 0 < B k j then B i j + B i k * B k j
    else if B i k < 0 ∧ B k j < 0 then B i j - B i k * B k j
    else B i j

/-- **Skew-symmetrizable integer matrix.** An integer square matrix `B` is skew-symmetrizable
if there are positive integers `dᵢ` with `dᵢ bᵢⱼ = -dⱼ bⱼᵢ` for all `i, j` (Fomin, Williams and
Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5,
Definition 2.7.4). -/
def IsSkewSymmetrizable (B : Matrix n n ℤ) : Prop :=
  ∃ d : n → ℤ, (∀ i, 0 < d i) ∧ ∀ i j, d i * B i j = -(d j * B j i)

/-- **Matrix mutation is an involution.** Mutating twice in the same direction `k` returns the
original matrix, `μₖ (μₖ B) = B` (Fomin, Williams and Zelevinsky, *Introduction to cluster
algebras, Chapters 1–3*, arXiv:1608.05735v5, Exercise 2.7.7(2)). The proof uses only
formula (2.7.1), so it holds for every integer square matrix, skew-symmetrizable or not. -/
theorem matrixMutation_matrixMutation (k : n) (B : Matrix n n ℤ) :
    matrixMutation k (matrixMutation k B) = B := by
  ext i j
  by_cases hik : i = k
  · subst hik; simp [matrixMutation]
  by_cases hjk : j = k
  · subst hjk; simp [matrixMutation]
  simp only [matrixMutation, Matrix.of_apply, hik, hjk, or_self, ite_false, true_or, or_true,
    ite_true]
  set a := B i k
  set b := B k j
  rcases lt_trichotomy a 0 with ha | ha | ha <;> rcases lt_trichotomy b 0 with hb | hb | hb <;>
    simp [ha, hb, ha.le, hb.le, not_lt.mpr, mul_comm]

/-- **Matrix mutation preserves skew-symmetrizability.** If positive integers `dᵢ` satisfy
`dᵢ bᵢⱼ = -dⱼ bⱼᵢ`, then they also skew-symmetrize `μₖ B` (Fomin, Williams and Zelevinsky,
*Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Exercise 2.7.7(1), square
case). -/
theorem IsSkewSymmetrizable.matrixMutation {B : Matrix n n ℤ} (hB : IsSkewSymmetrizable B)
    (k : n) : IsSkewSymmetrizable (matrixMutation k B) := by
  obtain ⟨d, hd, hdB⟩ := hB
  refine ⟨d, hd, fun i j => ?_⟩
  have hij := hdB i j
  have hik := hdB i k
  have hkj := hdB k j
  have hdi := hd i
  have hdj := hd j
  have hdk := hd k
  by_cases hi : i = k
  · subst hi; simp [ClusterAlgebra.matrixMutation, hij]
  by_cases hj : j = k
  · subst hj; simp [ClusterAlgebra.matrixMutation, hij]
  have hkey : d i * (B i k * B k j) = d j * (B j k * B k i) := by
    refine mul_left_cancel₀ hdk.ne' ?_
    linear_combination (d k * B k j) * hik - (d k * B k i) * hkj
  have s1 : 0 < B i k ↔ B k i < 0 := by constructor <;> intro h <;> nlinarith
  have s2 : B i k < 0 ↔ 0 < B k i := by constructor <;> intro h <;> nlinarith
  have s3 : 0 < B k j ↔ B j k < 0 := by constructor <;> intro h <;> nlinarith
  have s4 : B k j < 0 ↔ 0 < B j k := by constructor <;> intro h <;> nlinarith
  simp only [ClusterAlgebra.matrixMutation, Matrix.of_apply, hi, hj, or_self, ite_false]
  split_ifs <;>
    first
    | linear_combination hij + hkey
    | linear_combination hij - hkey
    | linear_combination hij
    | (exfalso; simp only [s1, s2, s3, s4] at *; omega)

/-- **Seed mutation without frozen variables.** For a cluster `x : n → K` in a field `K` and an
exchange matrix `B`, the mutation in direction `k` replaces `xₖ` by
`xₖ' = (∏_{bᵢₖ > 0} xᵢ^{bᵢₖ} + ∏_{bᵢₖ < 0} xᵢ^{-bᵢₖ}) / xₖ` and keeps the other cluster
variables, while `B` becomes `μₖ B` (Fomin, Williams and Zelevinsky, *Introduction to cluster
algebras, Chapters 1–3*, arXiv:1608.05735v5, Definition 3.1.3, exchange relation (3.1.2), in the
coefficient-free case `m = n`). -/
def seedMutation {K : Type*} [Field K] [Fintype n] (k : n) (s : (n → K) × Matrix n n ℤ) :
    (n → K) × Matrix n n ℤ :=
  (Function.update s.1 k
      ((∏ i, (if 0 < s.2 i k then s.1 i ^ (s.2 i k).toNat else 1) +
          ∏ i, (if s.2 i k < 0 then s.1 i ^ (-s.2 i k).toNat else 1)) / s.1 k),
    matrixMutation k s.2)

/-- **Iterated seed mutation.** `mutateSeq w s` applies the seed mutations in the directions
listed in `w`, from left to right (Fomin, Williams and Zelevinsky, *Introduction to cluster
algebras, Chapters 1–3*, arXiv:1608.05735v5, Definitions 3.1.7–3.1.8: every seed of the seed
pattern through `s` is reached this way). -/
def mutateSeq {K : Type*} [Field K] [Fintype n] (w : List n) (s : (n → K) × Matrix n n ℤ) :
    (n → K) × Matrix n n ℤ :=
  w.foldl (fun t k => seedMutation k t) s

/-- **Cluster variables of a seed pattern.** The set of all cluster variables in all seeds
obtained from `s` by iterated mutation (Fomin, Williams and Zelevinsky, *Introduction to cluster
algebras, Chapters 1–3*, arXiv:1608.05735v5, Definition 3.1.9, the set `𝒳`). -/
def clusterVariables {K : Type*} [Field K] [Fintype n] (s : (n → K) × Matrix n n ℤ) : Set K :=
  {z | ∃ (w : List n) (i : n), (mutateSeq w s).1 i = z}

end MathlibExt.RingTheory.ClusterAlgebra
