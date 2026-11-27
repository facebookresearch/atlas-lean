/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HankelTransform
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section
open scoped BigOperators

-- Helpers for Heilermann's formula (production-matrix factorisation).
private noncomputable def motzkinE {K : Type*} [CommRing K] (alpha beta : ℕ → K) : ℕ → ℕ → K
  | 0 => fun k => if k = 0 then 1 else 0
  | (j + 1) => fun k =>
      motzkinE alpha beta j (k + 1) + alpha k * motzkinE alpha beta j k +
        (if k = 0 then 0 else beta k * motzkinE alpha beta j (k - 1))

private theorem motzkinE_vanish_aux {K : Type*} [CommRing K] (alpha beta : ℕ → K) :
    ∀ (j k : ℕ), j < k → motzkinE alpha beta j k = 0 := by
  intro j
  induction j with
  | zero =>
    intro k hk
    show (if k = 0 then (1 : K) else 0) = 0
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    simp [hk0]
  | succ j ih =>
    intro k hk
    have hkj : motzkinE alpha beta (j + 1) k =
        motzkinE alpha beta j (k + 1) + alpha k * motzkinE alpha beta j k +
          (if k = 0 then (0 : K) else beta k * motzkinE alpha beta j (k - 1)) := rfl
    rw [hkj]
    have hk0 : k ≠ 0 := by omega
    simp only [hk0, ↓reduceIte]
    have h1 : motzkinE alpha beta j (k + 1) = 0 := ih _ (by omega)
    have h2 : motzkinE alpha beta j k = 0 := ih _ (by omega)
    have h3 : motzkinE alpha beta j (k - 1) = 0 := ih _ (by omega)
    simp [h1, h2, h3]

private theorem motzkinE_diag {K : Type*} [CommRing K] (alpha beta : ℕ → K) :
    ∀ (j : ℕ), motzkinE alpha beta j j = ∏ t ∈ Finset.range j, beta (t + 1) := by
  intro j
  induction j with
  | zero => simp [motzkinE]
  | succ j ih =>
    have hrfl : motzkinE alpha beta (j + 1) (j + 1) =
        motzkinE alpha beta j (j + 1 + 1) + alpha (j + 1) * motzkinE alpha beta j (j + 1) +
          (if j + 1 = 0 then (0 : K) else beta (j + 1) * motzkinE alpha beta j (j + 1 - 1)) := rfl
    have hne : (j + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero j
    simp only [hne, ↓reduceIte] at hrfl
    have h1 : motzkinE alpha beta j (j + 1 + 1) = 0 :=
      motzkinE_vanish_aux alpha beta j (j + 1 + 1) (by omega)
    have h2 : motzkinE alpha beta j (j + 1) = 0 :=
      motzkinE_vanish_aux alpha beta j (j + 1) (by omega)
    have h3 : j + 1 - 1 = j := by omega
    rw [h1, h2, h3, ih] at hrfl
    have hrr : (0 : K) + alpha (j + 1) * 0 + beta (j + 1) * ∏ t ∈ Finset.range j, beta (t + 1)
        = ∏ t ∈ Finset.range (j + 1), beta (t + 1) := by
      simp [Finset.prod_range_succ, mul_comm]
    rw [hrr] at hrfl
    exact hrfl

private theorem motzkinM_vanish_aux {K : Type*} [CommRing K]
    {alpha beta : ℕ → K} {M : ℕ → ℕ → K}
    (hzero_succ : ∀ j : ℕ, M 0 (j + 1) = 0)
    (hstep : ∀ n j : ℕ, M (n + 1) (j + 1) =
      M n j + alpha (j + 1) * M n (j + 1) + beta (j + 2) * M n (j + 2)) :
    ∀ (n k : ℕ), n < k → M n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact hzero_succ _
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ j =>
      rw [hstep]
      have h1 : M n j = 0 := ih _ (by omega)
      have h2 : M n (j + 1) = 0 := ih _ (by omega)
      have h3 : M n (j + 2) = 0 := ih _ (by omega)
      simp [h1, h2, h3]

private theorem motzkinM_diag_aux {K : Type*} [CommRing K]
    {alpha beta : ℕ → K} {M : ℕ → ℕ → K} {mu0 : K}
    (hzero : M 0 0 = mu0)
    (hstep : ∀ n j : ℕ, M (n + 1) (j + 1) =
      M n j + alpha (j + 1) * M n (j + 1) + beta (j + 2) * M n (j + 2))
    (hvan : ∀ (n k : ℕ), n < k → M n k = 0) :
    ∀ (n : ℕ), M n n = mu0 := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have h := hstep n n
    have h1 : M n (n + 1) = 0 := hvan _ _ (by omega)
    have h2 : M n (n + 2) = 0 := hvan _ _ (by omega)
    rw [h1, h2] at h
    simp at h
    rw [h, ih]

private theorem motzkinM_expand_aux {K : Type*} [CommRing K]
    {alpha beta : ℕ → K} {M : ℕ → ℕ → K}
    (hbase : ∀ n : ℕ, M (n + 1) 0 = alpha 0 * M n 0 + beta 1 * M n 1)
    (hstep : ∀ n j : ℕ, M (n + 1) (j + 1) =
      M n j + alpha (j + 1) * M n (j + 1) + beta (j + 2) * M n (j + 2)) :
    ∀ (j i : ℕ), M (i + j) 0 = ∑ k ∈ Finset.range (j + 1), M i k * motzkinE alpha beta j k := by
  intro j
  induction j with
  | zero =>
    intro i
    simp [motzkinE]
  | succ j ih =>
    intro i
    have hij : i + (j + 1) = (i + 1) + j := by omega
    rw [hij, ih (i + 1)]
    symm
    have hexpand : ∀ k : ℕ, M i k * motzkinE alpha beta (j + 1) k =
        M i k * motzkinE alpha beta j (k + 1) +
        M i k * (alpha k * motzkinE alpha beta j k) +
        M i k * (if k = 0 then (0 : K) else beta k * motzkinE alpha beta j (k - 1)) := by
      intro k
      have hrfl : motzkinE alpha beta (j + 1) k =
          motzkinE alpha beta j (k + 1) + alpha k * motzkinE alpha beta j k +
            (if k = 0 then (0 : K) else beta k * motzkinE alpha beta j (k - 1)) := rfl
      rw [hrfl, mul_add, mul_add]
    have hLHS : ∑ k ∈ Finset.range (j + 1 + 1), M i k * motzkinE alpha beta (j + 1) k =
        (∑ k ∈ Finset.range (j + 1 + 1), M i k * motzkinE alpha beta j (k + 1)) +
        (∑ k ∈ Finset.range (j + 1 + 1), M i k * (alpha k * motzkinE alpha beta j k)) +
        (∑ k ∈ Finset.range (j + 1 + 1), M i k * (if k = 0 then (0 : K) else beta k * motzkinE alpha beta j (k - 1))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      exact hexpand k
    rw [hLHS]
    have hvan := motzkinE_vanish_aux alpha beta
    have hSb : ∑ k ∈ Finset.range (j + 1 + 1), M i k * (alpha k * motzkinE alpha beta j k) =
        ∑ t ∈ Finset.range (j + 1), M i t * (alpha t * motzkinE alpha beta j t) := by
      rw [Finset.sum_range_succ]
      have hlast : M i (j + 1) * (alpha (j + 1) * motzkinE alpha beta j (j + 1)) = 0 := by
        have : motzkinE alpha beta j (j + 1) = 0 := hvan j (j + 1) (by omega)
        simp [this]
      rw [hlast, add_zero]
    have hSa : ∑ k ∈ Finset.range (j + 1 + 1), M i k * motzkinE alpha beta j (k + 1) =
        ∑ k ∈ Finset.range (j + 1), M i k * motzkinE alpha beta j (k + 1) := by
      rw [Finset.sum_range_succ]
      have hlast : M i (j + 1) * motzkinE alpha beta j (j + 1 + 1) = 0 := by
        have : motzkinE alpha beta j (j + 1 + 1) = 0 := hvan j (j + 1 + 1) (by omega)
        simp [this]
      rw [hlast, add_zero]
    have hSa' : ∑ k ∈ Finset.range (j + 1), M i k * motzkinE alpha beta j (k + 1) =
        ∑ t ∈ Finset.range (j + 1), ((if t = 0 then (0 : K) else M i (t - 1)) * motzkinE alpha beta j t) := by
      have h1 : ∑ k ∈ Finset.range (j + 1), M i k * motzkinE alpha beta j (k + 1) =
          ∑ k ∈ Finset.range j, M i k * motzkinE alpha beta j (k + 1) := by
        rw [Finset.sum_range_succ]
        have hlast : M i j * motzkinE alpha beta j (j + 1) = 0 := by
          have : motzkinE alpha beta j (j + 1) = 0 := hvan j (j + 1) (by omega)
          simp [this]
        rw [hlast, add_zero]
      have h2 : ∑ t ∈ Finset.range (j + 1), ((if t = 0 then (0 : K) else M i (t - 1)) * motzkinE alpha beta j t) =
          ∑ t ∈ Finset.range j, M i t * motzkinE alpha beta j (t + 1) := by
        rw [Finset.sum_range_succ']
        simp only [↓reduceIte, zero_mul]
        rw [add_zero]
        apply Finset.sum_congr rfl
        intro t _
        have ht : t + 1 ≠ 0 := Nat.succ_ne_zero t
        simp only [ht, ↓reduceIte]
        have htt : t + 1 - 1 = t := by omega
        rw [htt]
      rw [h1, h2]
    have hSc : ∑ k ∈ Finset.range (j + 1 + 1), M i k * (if k = 0 then (0 : K) else beta k * motzkinE alpha beta j (k - 1)) =
        ∑ t ∈ Finset.range (j + 1), M i (t + 1) * (beta (t + 1) * motzkinE alpha beta j t) := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, mul_zero]
      rw [add_zero]
      apply Finset.sum_congr rfl
      intro t _
      have ht : t + 1 ≠ 0 := Nat.succ_ne_zero t
      simp only [ht, ↓reduceIte]
      have htt : t + 1 - 1 = t := by omega
      rw [htt]
    rw [hSa, hSa', hSb, hSc]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    cases t with
    | zero =>
      simp only [↓reduceIte, zero_mul, zero_add]
      have hb := hbase i
      have : M i 0 * (alpha 0 * motzkinE alpha beta j 0) +
          M i (0 + 1) * (beta (0 + 1) * motzkinE alpha beta j 0) =
          (alpha 0 * M i 0 + beta 1 * M i 1) * motzkinE alpha beta j 0 := by ring
      simpa using this.trans (by rw [hb])
    | succ s =>
      have hs : s + 1 ≠ 0 := Nat.succ_ne_zero s
      simp only [hs, ↓reduceIte]
      have hss : s + 1 - 1 = s := by omega
      rw [hss]
      have hst := hstep i s
      have : M i s * motzkinE alpha beta j (s + 1) +
          M i (s + 1) * (alpha (s + 1) * motzkinE alpha beta j (s + 1)) +
          M i (s + 1 + 1) * (beta (s + 1 + 1) * motzkinE alpha beta j (s + 1))
          = (M i s + alpha (s + 1) * M i (s + 1) + beta (s + 1 + 1) * M i (s + 1 + 1)) *
            motzkinE alpha beta j (s + 1) := by ring
      have hbeta : s + 1 + 1 = s + 2 := by omega
      rw [hbeta] at this
      rw [this, ← hst]

private theorem prod_diag_eq_aux {K : Type*} [CommRing K] (beta : ℕ → K) :
    ∀ (n : ℕ), (∏ j ∈ Finset.range (n + 1), ∏ t ∈ Finset.range j, beta (t + 1)) =
      ∏ j ∈ Finset.range n, beta (j + 1) ^ (n - j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ (fun j => ∏ t ∈ Finset.range j, beta (t + 1)) (n + 1)]
    rw [ih]
    have hRHS : ∏ j ∈ Finset.range (n + 1), beta (j + 1) ^ (n + 1 - j) =
        (∏ j ∈ Finset.range n, beta (j + 1) ^ (n - j)) * (∏ j ∈ Finset.range (n + 1), beta (j + 1)) := by
      have hps : ∏ j ∈ Finset.range (n + 1), beta (j + 1) ^ (n + 1 - j) =
          (∏ j ∈ Finset.range n, beta (j + 1) ^ (n + 1 - j)) * beta (n + 1) ^ (n + 1 - n) :=
        Finset.prod_range_succ _ n
      rw [hps]
      have hterm : beta (n + 1) ^ (n + 1 - n) = beta (n + 1) := by
        have hlast : n + 1 - n = 1 := by omega
        rw [hlast, pow_one]
      rw [hterm]
      have h1 : ∀ j ∈ Finset.range n, beta (j + 1) ^ (n + 1 - j) =
          (beta (j + 1) ^ (n - j)) * beta (j + 1) := by
        intro j hj
        have hjl : j < n := Finset.mem_range.mp hj
        have hexp : n + 1 - j = (n - j) + 1 := by omega
        rw [hexp, pow_succ]
      rw [Finset.prod_congr rfl h1]
      rw [Finset.prod_mul_distrib]
      have hps2 : ∏ j ∈ Finset.range (n + 1), beta (j + 1) =
          (∏ j ∈ Finset.range n, beta (j + 1)) * beta (n + 1) :=
        Finset.prod_range_succ _ n
      rw [hps2]
      ring
    rw [hRHS]

/-- **Heilermann's formula for weighted Motzkin arrays.** Let $K$ be a commutative ring, let
$\alpha$, $\beta$ be sequences in $K$, let $\mu_0 \in K$, and let $(M_{n,j})_{n, j \ge 0}$ be an
array in $K$ with $M_{0,0} = \mu_0$ and, for all $n, j \ge 0$, $M_{0,j+1} = 0$,
$M_{n+1,0} = \alpha_0 M_{n,0} + \beta_1 M_{n,1}$ and
$M_{n+1,j+1} = M_{n,j} + \alpha_{j+1} M_{n,j+1} + \beta_{j+2} M_{n,j+2}$. Then for every
$n \ge 0$ the Hankel transform of the column $(M_{m,0})_{m \ge 0}$ at $n$, the determinant of the
$(n+1) \times (n+1)$ matrix $(M_{i+j,0})_{0 \le i, j \le n}$, equals
$$\mu_0^{n+1} \prod_{j=0}^{n-1} \beta_{j+1}^{\,n-j},$$
that is, $\mu_0^{n+1} \beta_1^n \beta_2^{n-1} \cdots \beta_n$, which is $\mu_0$ for $n = 0$.

No hypothesis that the $\beta_i$ are nonzero is needed.

Source: Paul Barry, *From Fibonacci to Robbins: Series Reversion and Hankel
Transforms*, Journal of Integer Sequences 24 (2021), Article 21.10.2,
lines 110–117,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex;
source SHA-256
`9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`;
normalized line-span SHA-256
`a838e5996f223ba9e45347f17ad864912efc392f5c3d56ea749bcf62d3289825`;
concept `jis_dep_heilermann_049f63eb`;
grounded ID `jis_grounded_049f63eb8aadf7377777a597`.

Proves `Wanted` entry `hankelTransform_eq_prod_of_weightedMotzkin`.
-/
theorem hankelTransform_eq_prod_of_weightedMotzkin
    {K : Type*} [CommRing K]
    {alpha beta : ℕ → K} {M : ℕ → ℕ → K} {mu0 : K}
    (hzero : M 0 0 = mu0)
    (hzero_succ : ∀ j : ℕ, M 0 (j + 1) = 0)
    (hbase : ∀ n : ℕ, M (n + 1) 0 = alpha 0 * M n 0 + beta 1 * M n 1)
    (hstep : ∀ n j : ℕ, M (n + 1) (j + 1) =
      M n j + alpha (j + 1) * M n (j + 1) + beta (j + 2) * M n (j + 2))
    (n : ℕ) :
    hankelTransform (fun m => M m 0) n =
      mu0 ^ (n + 1) * ∏ j ∈ Finset.range n, beta (j + 1) ^ (n - j) := by
  have hMvan : ∀ (a k : ℕ), a < k → M a k = 0 :=
    motzkinM_vanish_aux hzero_succ hstep
  have hMdiag : ∀ (a : ℕ), M a a = mu0 :=
    motzkinM_diag_aux hzero hstep hMvan
  have hEvan := motzkinE_vanish_aux alpha beta
  have hEdiag := motzkinE_diag alpha beta
  have hexpand := motzkinM_expand_aux hbase hstep
  set L : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    Matrix.of fun i j => M i.val j.val with hLdef
  set C : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    Matrix.of fun i j => motzkinE alpha beta j.val i.val with hCdef
  set H : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    Matrix.of fun i j => M (i.val + j.val) 0 with hHdef
  have hHC : H = L * C := by
    ext i j
    simp only [hHdef, hLdef, hCdef, Matrix.of_apply, Matrix.mul_apply]
    have hexp := hexpand j.val i.val
    have hFin : ∑ k : Fin (n + 1), M i.val k.val * motzkinE alpha beta j.val k.val =
        ∑ k ∈ Finset.range (n + 1), M i.val k * motzkinE alpha beta j.val k := by
      have hfu := Fin.sum_univ_eq_sum_range (fun k => M i.val k * motzkinE alpha beta j.val k) (n + 1)
      simpa using hfu
    rw [hFin]
    have hjle : j.val + 1 ≤ n + 1 := by
      have := j.isLt
      omega
    have hsub : Finset.range (j.val + 1) ⊆ Finset.range (n + 1) :=
      Finset.range_subset_range.mpr hjle
    have hsum : ∑ k ∈ Finset.range (j.val + 1), M i.val k * motzkinE alpha beta j.val k =
        ∑ k ∈ Finset.range (n + 1), M i.val k * motzkinE alpha beta j.val k := by
      apply Finset.sum_subset hsub
      intro x hx1 hx2
      have hx : j.val < x := by
        have : x ∈ Finset.range (n + 1) := hx1
        simp at hx2 ⊢
        omega
      have hE0 : motzkinE alpha beta j.val x = 0 := hEvan _ _ hx
      simp [hE0]
    exact hexp.trans hsum
  have hdetH : H.det = L.det * C.det := by
    rw [hHC, Matrix.det_mul]
  have hLtri : L.IsLowerTriangular := by
    intro i j hij
    simp only [hLdef, Matrix.of_apply]
    have hval : i.val < j.val := Fin.lt_def.mp hij
    exact hMvan _ _ hval
  have hCtri : C.IsUpperTriangular := by
    intro i j hij
    simp only [hCdef, Matrix.of_apply]
    have hval : j.val < i.val := Fin.lt_def.mp hij
    exact hEvan _ _ hval
  have hdetL : L.det = mu0 ^ (n + 1) := by
    have h := Matrix.det_of_isLowerTriangular L hLtri
    have hdiag : ∀ i : Fin (n + 1), L i i = mu0 := by
      intro i
      simp only [hLdef, Matrix.of_apply]
      exact hMdiag _
    rw [h]
    simp [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdetC : C.det = ∏ j ∈ Finset.range n, beta (j + 1) ^ (n - j) := by
    have h := Matrix.det_of_isUpperTriangular hCtri
    have hdiag : ∀ i : Fin (n + 1), C i i = ∏ t ∈ Finset.range i.val, beta (t + 1) := by
      intro i
      simp only [hCdef, Matrix.of_apply]
      exact hEdiag _
    have hprod : C.det = ∏ j ∈ Finset.range (n + 1), ∏ t ∈ Finset.range j, beta (t + 1) := by
      rw [h]
      have := Fin.prod_univ_eq_prod_range (fun j => ∏ t ∈ Finset.range j, beta (t + 1)) (n + 1)
      have hcongr : ∏ i : Fin (n + 1), C i i =
          ∏ i : Fin (n + 1), (fun j => ∏ t ∈ Finset.range j, beta (t + 1)) i.val := by
        apply Finset.prod_congr rfl
        intro i _
        exact hdiag i
      rw [hcongr]
      exact this
    rw [hprod]
    exact prod_diag_eq_aux beta n
  have hHdet : hankelTransform (fun m => M m 0) n = H.det := rfl
  rw [hHdet, hdetH, hdetL, hdetC]

end

end MetaMathlibExt
