/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Cast.Defs
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst
import Mathlib.Data.Matrix.Basic
import MathlibExt.Combinatorics.Enumerative.StirlingMatrices

/-!
# Stirling inversion

The signed first-kind and second-kind Stirling transforms on rational sequences are inverse to
one another, by applying the finite Stirling matrix identities to each initial segment.
-/

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

open MetaMathlibExt
open scoped Matrix

private def truncate (N : ℕ) (a : ℕ → ℕ → ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => a i j

-- Only the terms above the row index vanish; the constant term at index zero is retained.
private theorem mulVec_eq_sum_range (a : ℕ → ℕ → ℚ) (w : ℕ → ℚ)
    (ha : ∀ i j, i < j → a i j = 0) {N : ℕ} (i : Fin N) :
    (truncate N a *ᵥ fun j : Fin N => w j) i =
      ∑ j ∈ Finset.range (i.val + 1), a i j * w j := by
  simp only [truncate, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_eq_sum_range (fun j => a i j * w j)]
  symm
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt i.isLt)) ?_
  intro j _ hj
  rw [ha _ _ (by simpa only [Finset.mem_range, Nat.not_lt, Nat.succ_le_iff] using hj), zero_mul]

private theorem inverse_transform {a b : ℕ → ℕ → ℚ}
    (ha : ∀ i j, i < j → a i j = 0) (hb : ∀ i j, i < j → b i j = 0)
    (hab : ∀ N, truncate N b * truncate N a = 1)
    {x y : ℕ → ℚ} (h : ∀ i, x i = ∑ j ∈ Finset.range (i + 1), a i j * y j) :
    ∀ n, y n = ∑ j ∈ Finset.range (n + 1), b n j * x j := by
  intro n
  have hx : (fun i : Fin (n + 1) => x i) =
      truncate (n + 1) a *ᵥ fun j : Fin (n + 1) => y j := by
    funext i
    rw [mulVec_eq_sum_range a y ha]
    exact h i
  have hy : truncate (n + 1) b *ᵥ (fun j : Fin (n + 1) => x j) =
      fun j : Fin (n + 1) => y j := by
    rw [hx, Matrix.mulVec_mulVec, hab, Matrix.one_mulVec]
  simpa only [mulVec_eq_sum_range b x hb, Fin.val_last] using
    (congrFun hy (Fin.last n)).symm

/-- **Stirling inversion.** Let $s(m, j)$ be the signed Stirling numbers of the first kind and
$S(m, j)$ the Stirling numbers of the second kind. For all sequences $(u_n)_{n \ge 0}$ and
$(v_n)_{n \ge 0}$ of rational numbers, $u_n = \sum_{k=0}^{n} s(n, k) \, v_k$ for every natural
number $n$ if and only if $v_n = \sum_{k=0}^{n} S(n, k) \, u_k$ for every natural number $n$.

The paper states this for sequences of complex numbers.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Lemma 3. -/
public theorem stirling_inversion_iff (u v : ℕ → ℚ) :
    (∀ n, u n = ∑ k ∈ Finset.range (n + 1),
      (MetaMathlibExt.signedStirlingFirst n k : ℚ) * v k) ↔
    (∀ n, v n = ∑ k ∈ Finset.range (n + 1),
      (Nat.stirlingSecond n k : ℚ) * u k) := by
  let s (i j : ℕ) : ℚ := signedStirlingFirst i j
  let S (i j : ℕ) : ℚ := Nat.stirlingSecond i j
  have hs (i j : ℕ) (h : i < j) : s i j = 0 := by
    simp [s, signedStirlingFirst_eq_zero_of_lt h]
  have hS (i j : ℕ) (h : i < j) : S i j = 0 := by
    simp [S, Nat.stirlingSecond_eq_zero_of_lt h]
  have hinv (N : ℕ) : truncate N s * truncate N S = 1 ∧ truncate N S * truncate N s = 1 := by
    let A : Matrix (Fin N) (Fin N) ℤ := fun i j => signedStirlingFirst i j
    let B : Matrix (Fin N) (Fin N) ℤ := fun i j => Nat.stirlingSecond i j
    have h := stirlingMatrices_mutualInverse_and_lowerTriangular N
    change A * B = 1 ∧ B * A = 1 ∧ _ at h
    let f : Matrix (Fin N) (Fin N) ℤ →+* Matrix (Fin N) (Fin N) ℚ :=
      (Int.castRingHom ℚ).mapMatrix
    have hA : f A = truncate N s := rfl
    have hB : f B = truncate N S := by
      funext i j
      exact Int.cast_natCast (Nat.stirlingSecond i j)
    rw [← hA, ← hB, ← map_mul, ← map_mul, h.1, h.2.1, map_one]
    exact ⟨rfl, rfl⟩
  exact ⟨inverse_transform hs hS (fun N => (hinv N).2),
    inverse_transform hS hs (fun N => (hinv N).1)⟩

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
