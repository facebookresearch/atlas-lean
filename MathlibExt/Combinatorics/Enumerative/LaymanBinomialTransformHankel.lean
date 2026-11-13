/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FallingKBinomialTransform
public import MathlibExt.NumberTheory.HankelTransform
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section
/-- Binomial lower-triangular matrix with `(i, j)` entry `C(i, j)`. -/
private def laymanBinomMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j => (Nat.choose i.val j.val : ℤ)

/-- The binomial matrix is lower triangular. -/
private theorem laymanBinomMatrix_lower (n : ℕ) :
    (laymanBinomMatrix n).IsLowerTriangular := by
  intro i j h
  simp only [laymanBinomMatrix, Matrix.of_apply]
  have hij : i < j := by simpa using h
  have hval : i.val < j.val := by exact_mod_cast hij
  rw [Nat.choose_eq_zero_of_lt hval, Nat.cast_zero]

/-- Diagonal entries are `1`. -/
private theorem laymanBinomMatrix_diag (n : ℕ) (i : Fin (n + 1)) :
    laymanBinomMatrix n i i = 1 := by
  simp [laymanBinomMatrix, Nat.choose_self]

/-- Its determinant is `1`. -/
private theorem laymanBinomMatrix_det (n : ℕ) : (laymanBinomMatrix n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (laymanBinomMatrix_lower n)]
  simp [laymanBinomMatrix_diag]

/-- Reindexed Vandermonde sum: double binomial sum equals the binomial
transform sum. -/
private theorem layman_entry_sum (a : ℕ → ℤ) (u v : ℕ) :
    ∑ l ∈ Finset.range (u + 1), ∑ m ∈ Finset.range (v + 1),
        ((Nat.choose u l : ℤ) * (Nat.choose v m : ℤ) * a (l + m))
      = ∑ k ∈ Finset.range (u + v + 1), (Nat.choose (u + v) k : ℤ) * a k := by
  classical
  let e : ℕ × ℕ → Sigma (fun _ : ℕ => ℕ × ℕ) := fun p => ⟨p.1 + p.2, p⟩
  let G : Sigma (fun _ : ℕ => ℕ × ℕ) → ℤ :=
    fun x => (Nat.choose u x.2.1 : ℤ) * (Nat.choose v x.2.2 : ℤ) * a (x.2.1 + x.2.2)
  let S : Finset (ℕ × ℕ) := Finset.range (u + 1) ×ˢ Finset.range (v + 1)
  let T : Finset (Sigma fun _ : ℕ => ℕ × ℕ) :=
    Finset.sigma (Finset.range (u + v + 1)) fun k =>
      Finset.HasAntidiagonal.antidiagonal k
  have he_inj : Set.InjOn e S := by
    intro x1 _ x2 _ h
    have h2 : x1 = x2 := congrArg Sigma.snd h
    simpa [e] using h2
  have hLHS : ∑ x ∈ S.image e, G x
      = ∑ l ∈ Finset.range (u + 1), ∑ m ∈ Finset.range (v + 1),
        ((Nat.choose u l : ℤ) * (Nat.choose v m : ℤ) * a (l + m)) := by
    rw [Finset.sum_image he_inj]
    simp only [S, Finset.sum_product]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    simp [G, e]
  have hsub : S.image e ⊆ T := by
    intro x hx
    simp only [S, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨⟨l, m⟩, ⟨hl, hm⟩, rfl⟩ := hx
    change (⟨l + m, (l, m)⟩ : Sigma fun _ : ℕ => ℕ × ℕ) ∈ T
    simp only [T, Finset.mem_sigma, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  have hT : ∑ x ∈ T, G x = ∑ x ∈ S.image e, G x := by
    apply Eq.symm
    apply Finset.sum_subset hsub
    intro x hxT hx0
    obtain ⟨k, p⟩ := x
    obtain ⟨l, m⟩ := p
    have hsig : k ∈ Finset.range (u + v + 1) ∧
        (l, m) ∈ Finset.HasAntidiagonal.antidiagonal k :=
      Finset.mem_sigma.mp hxT
    have hkk : l + m = k :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hsig.2
    have hmemS : (l, m) ∉ S := by
      intro hS
      apply hx0
      rw [Finset.mem_image]
      refine ⟨(l, m), hS, ?_⟩
      simp only [e]
      rw [hkk]
    change (Nat.choose u l : ℤ) * (Nat.choose v m : ℤ) * a (l + m) = 0
    simp only [S, Finset.mem_product, Finset.mem_range, not_and_or] at hmemS
    rcases hmemS with h | h
    · have hu : u < l := by omega
      rw [Nat.choose_eq_zero_of_lt hu, Nat.cast_zero, zero_mul, zero_mul]
    · have hv : v < m := by omega
      rw [Nat.choose_eq_zero_of_lt hv, Nat.cast_zero, mul_zero, zero_mul]
  have hTsum : ∑ x ∈ T, G x
      = ∑ k ∈ Finset.range (u + v + 1),
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          ((Nat.choose u p.1 : ℤ) * (Nat.choose v p.2 : ℤ) * a (p.1 + p.2)) := by
    simp [T, G, Finset.sum_sigma]
  have hV : ∀ k ∈ Finset.range (u + v + 1),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          ((Nat.choose u p.1 : ℤ) * (Nat.choose v p.2 : ℤ) * a (p.1 + p.2))
        = (Nat.choose (u + v) k : ℤ) * a k := by
    intro k hk
    have hsub2 : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        (Nat.choose u p.1 : ℤ) * (Nat.choose v p.2 : ℤ) * a (p.1 + p.2)
          = ((Nat.choose u p.1 * Nat.choose v p.2 : ℕ) : ℤ) * a k := by
      intro p hp
      have hkk : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [hkk, Nat.cast_mul]
    rw [Finset.sum_congr rfl hsub2, ← Finset.sum_mul]
    congr 1
    have hnat : (u + v).choose k
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, u.choose ij.1 * v.choose ij.2 :=
      Nat.add_choose_eq u v k
    rw [hnat, Nat.cast_sum]
  rw [← hLHS, ← hT, hTsum]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact hV k hk

/-- Matrix entry identity: `(L * H(a) * Lᵀ) p q = b (p + q)`. -/
private theorem layman_hankel_entry (a : ℕ → ℤ) (n : ℕ) (p q : Fin (n + 1)) :
    (laymanBinomMatrix n *
      (Matrix.of fun i j : Fin (n + 1) ↦ a (i.val + j.val)) *
      (laymanBinomMatrix n).transpose) p q
      = binomialTransform a (p.val + q.val) := by
  have hpn : p.val ≤ n := by have h := p.isLt; omega
  have hqn : q.val ≤ n := by have h := q.isLt; omega
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    laymanBinomMatrix]
  have hinner : ∀ x : Fin (n + 1),
      (∑ l : Fin (n + 1), (Nat.choose p.val l.val : ℤ) * a (l.val + x.val))
      = ∑ l ∈ Finset.range (p.val + 1),
        (Nat.choose p.val l : ℤ) * a (l + x.val) := by
    intro x
    rw [Fin.sum_univ_eq_sum_range
      (fun m => (Nat.choose p.val m : ℤ) * a (m + x.val)) (n + 1)]
    apply Eq.symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro l hl1 hl2
    simp only [Finset.mem_range] at hl1 hl2
    have hpl : p.val < l := by omega
    rw [Nat.choose_eq_zero_of_lt hpl, Nat.cast_zero, zero_mul]
  simp only [hinner]
  have houter : (∑ x : Fin (n + 1),
        (∑ l ∈ Finset.range (p.val + 1), (Nat.choose p.val l : ℤ) * a (l + x.val)) *
        (Nat.choose q.val x.val : ℤ))
      = ∑ x ∈ Finset.range (q.val + 1),
        (∑ l ∈ Finset.range (p.val + 1), (Nat.choose p.val l : ℤ) * a (l + x)) *
        (Nat.choose q.val x : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun m =>
      (∑ l ∈ Finset.range (p.val + 1), (Nat.choose p.val l : ℤ) * a (l + m)) *
        (Nat.choose q.val m : ℤ)) (n + 1)]
    apply Eq.symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro x hx1 hx2
    simp only [Finset.mem_range] at hx1 hx2
    have hqx : q.val < x := by omega
    rw [Nat.choose_eq_zero_of_lt hqx, Nat.cast_zero, mul_zero]
  rw [houter, binomialTransform_eq_sum]
  have hform : (∑ x ∈ Finset.range (q.val + 1),
        (∑ l ∈ Finset.range (p.val + 1), (Nat.choose p.val l : ℤ) * a (l + x)) *
        (Nat.choose q.val x : ℤ))
      = ∑ l ∈ Finset.range (p.val + 1), ∑ m ∈ Finset.range (q.val + 1),
        (Nat.choose p.val l : ℤ) * (Nat.choose q.val m : ℤ) * a (l + m) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hform]
  exact layman_entry_sum a p.val q.val

/-- **Layman's theorem: the binomial transform preserves the Hankel transform.** For every
sequence of integers $(a_n)_{n \ge 0}$, the Hankel transform of the binomial transform of $a$
equals the Hankel transform of $a$. Here the binomial transform of $a$ is the sequence
$b_n = \sum_{i=0}^{n} \binom{n}{i} a_i$, and the Hankel transform of a sequence $c$ is the
sequence whose $n$-th term, for $n \ge 0$, is the determinant of the $(n+1) \times (n+1)$
matrix $(c_{i+j})_{0 \le i, j \le n}$.

Proves `Wanted` entry `layman_binomial_transform_hankel_invariant`.

Source: John W. Layman, *The Hankel Transform and Some of its
Properties*, Journal of Integer Sequences 4 (2001), Theorem 1,
<https://cs.uwaterloo.ca/journals/JIS/VOL4/LAYMAN/hankel.pdf>,
live PDF SHA-256
`dfc5e07f9efc257c41e2ac947926d2aed38b97ab8f15ae8a10ec36c35cf79210`.
Campaign source passage: Mahid M. Mangontarum,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Mangontarum/mango4.tex>,
lines 535-557, full-source SHA-256
`3e6c2cf946c933cf36388d5da99293ed8f39d50de0024290beb39f94ccaa5c5d`,
exact frozen text SHA-256
`cfc84bacd9f2ebabc59e8927c0b5b898ae7bd19d88fd795c2eca2df0fd6ad710`,
grounded task `jis_grounded_16fbee6379089c6cf50650f2`.
Retained Lean authored by Muse Spark 1.3.
-/
theorem layman_binomial_transform_hankel_invariant
    (a : ℕ → ℤ) :
    hankelTransform (binomialTransform a) = hankelTransform a := by
  funext n
  simp only [hankelTransform]
  have hmat : (Matrix.of fun i j : Fin (n + 1) ↦ binomialTransform a (i.val + j.val))
      = laymanBinomMatrix n *
        (Matrix.of fun i j : Fin (n + 1) ↦ a (i.val + j.val)) *
        (laymanBinomMatrix n).transpose := by
    ext i j
    simp only [Matrix.of_apply]
    exact (layman_hankel_entry a n i j).symm
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    laymanBinomMatrix_det, one_mul, mul_one]

end

end MetaMathlibExt
