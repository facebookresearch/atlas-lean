/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.FieldTheory.Minpoly.IsConjRoot
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ramanujan graphs give Weil numbers

This file proves that a root `α` of a quadratic `X ^ 2 - μ X + q` whose
coefficient `μ` is a non-trivial root of the characteristic polynomial of a
symmetric integer matrix satisfying the Ramanujan bound is an algebraic
integer whose rational conjugates all have absolute value `√q`.

## Main results

* `MetaMathlibExt.isWeilNumber_of_ramanujan`: such an `α` is integral over `ℤ`
  and every complex root of its minimal polynomial over `ℚ` has absolute
  value `√q`.
-/

@[expose] public section

open Polynomial Matrix Finset

namespace MetaMathlibExt

namespace isWeilNumber_of_ramanujan

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

/-- The integer matrix `A` viewed as a complex matrix. -/
private noncomputable def hermitianMatrix : Matrix (Fin n) (Fin n) ℂ :=
  A.map (Int.castRingHom ℂ)

/-- The complex matrix obtained from a symmetric integer matrix is Hermitian. -/
private lemma isHermitian_hermitianMatrix (hA : A.IsSymm) :
    (hermitianMatrix A).IsHermitian := by
  ext i j
  simp [hermitianMatrix, Matrix.conjTranspose, hA.apply i j]

/-- A complex root of the characteristic polynomial of a symmetric integer
matrix is one of the (real) eigenvalues of the associated Hermitian matrix. -/
private lemma exists_eigenvalue_of_mem_aroots (hA : A.IsSymm) {μ : ℂ}
    (hμ : μ ∈ A.charpoly.aroots ℂ) :
    ∃ i : Fin n, μ = ((isHermitian_hermitianMatrix A hA).eigenvalues i : ℂ) := by
  have hB : (hermitianMatrix A).charpoly = A.charpoly.map (Int.castRingHom ℂ) :=
    Matrix.charpoly_map A (Int.castRingHom ℂ)
  have heval : (hermitianMatrix A).charpoly.eval μ = 0 := by
    rw [hB, Polynomial.eval_map]
    rw [Polynomial.mem_aroots] at hμ
    rw [Polynomial.aeval_def] at hμ
    exact hμ.2
  rw [(isHermitian_hermitianMatrix A hA).charpoly_eq] at heval
  rw [Polynomial.eval_prod] at heval
  rw [Finset.prod_eq_zero_iff] at heval
  obtain ⟨i, _, hi⟩ := heval
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hi
  exact ⟨i, sub_eq_zero.mp hi⟩

/-- The polynomial `∑ i, coeffᵢ(charpoly A) * (X ^ 2 + q) ^ i * X ^ (n - i)`.
Its roots are the solutions of `X ^ 2 - μ X + q = 0` as `μ` ranges over the
roots of the characteristic polynomial of `A`; in particular it is a monic
integer polynomial vanishing at any such solution. -/
private noncomputable def auxPoly (q : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (n + 1),
    C (A.charpoly.coeff i) * (X ^ 2 + C (q : ℤ)) ^ i * X ^ (n - i)

/-- Evaluating the auxiliary polynomial at a solution of the quadratic
recovers the characteristic polynomial evaluated at the coefficient `μ`. -/
private lemma aeval_auxPoly (q : ℕ) {α μ : ℂ} (h : α ^ 2 - μ * α + q = 0) :
    aeval α (auxPoly A q) = α ^ n * aeval μ A.charpoly := by
  have hcast : (algebraMap ℤ ℂ) (q : ℤ) = (q : ℂ) := by simp
  have hrel : α ^ 2 + (algebraMap ℤ ℂ) (q : ℤ) = μ * α := by
    rw [hcast]; linear_combination h
  have hdeg : A.charpoly.natDegree < n + 1 := by
    simp [Matrix.charpoly_natDegree_eq_dim]
  rw [Polynomial.aeval_eq_sum_range' hdeg]
  unfold auxPoly
  rw [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [map_mul, map_pow, aeval_X, map_add, aeval_C, Algebra.smul_def]
  rw [hrel, mul_pow]
  have hpow : α ^ i * α ^ (n - i) = α ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt_succ hi)]
  have hregroup : (algebraMap ℤ ℂ) (A.charpoly.coeff i) * (μ ^ i * α ^ i) * α ^ (n - i)
      = ((algebraMap ℤ ℂ) (A.charpoly.coeff i) * μ ^ i) * (α ^ i * α ^ (n - i)) := by ring
  rw [hregroup, hpow]
  ring

private lemma auxPoly_natDegree_le (q : ℕ) : (auxPoly A q).natDegree ≤ 2 * n := by
  have h2 : (X ^ 2 + C (q : ℤ) : ℤ[X]).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    simp
  unfold auxPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro i hi
  rw [Finset.mem_range] at hi
  calc (C (A.charpoly.coeff i) * (X ^ 2 + C (q : ℤ)) ^ i * X ^ (n - i)).natDegree
      ≤ (C (A.charpoly.coeff i)).natDegree + ((X ^ 2 + C (q : ℤ)) ^ i).natDegree +
          (X ^ (n - i)).natDegree := by
        refine (Polynomial.natDegree_mul_le).trans ?_
        refine Nat.add_le_add_right Polynomial.natDegree_mul_le _
    _ ≤ 0 + 2 * i + (n - i) := by
        gcongr
        · simp
        · exact (Polynomial.natDegree_pow_le).trans
            ((Nat.mul_le_mul_left i h2).trans_eq (Nat.mul_comm i 2))
        · simp
    _ ≤ 2 * n := by omega

/-- The auxiliary polynomial is monic. -/
private lemma auxPoly_monic (q : ℕ) : (auxPoly A q).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (2 * n) (auxPoly_natDegree_le A q)
  unfold auxPoly
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · have hnd : A.charpoly.natDegree = n := by
      simp [Matrix.charpoly_natDegree_eq_dim]
    have hcoeff : A.charpoly.coeff n = 1 := by
      have h := A.charpoly_monic.coeff_natDegree
      rwa [hnd] at h
    have hbase : (X ^ 2 + C (q : ℤ) : ℤ[X]).Monic :=
      Polynomial.monic_X_pow_add_C (q : ℤ) two_ne_zero
    have hmonic : ((X ^ 2 + C (q : ℤ) : ℤ[X]) ^ n).Monic := hbase.pow n
    have hdeg : ((X ^ 2 + C (q : ℤ) : ℤ[X]) ^ n).natDegree = 2 * n := by
      rw [hbase.natDegree_pow, Polynomial.natDegree_X_pow_add_C, Nat.mul_comm]
    have hterm : C (A.charpoly.coeff n) * (X ^ 2 + C (q : ℤ)) ^ n * X ^ (n - n)
        = (X ^ 2 + C (q : ℤ)) ^ n := by simp [hcoeff]
    rw [hterm, ← hdeg]
    exact hmonic.coeff_natDegree
  · intro i hi hin
    rw [Finset.mem_range] at hi
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have h2 : (X ^ 2 + C (q : ℤ) : ℤ[X]).natDegree ≤ 2 := by
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      simp
    calc (C (A.charpoly.coeff i) * (X ^ 2 + C (q : ℤ)) ^ i * X ^ (n - i)).natDegree
        ≤ (C (A.charpoly.coeff i)).natDegree + ((X ^ 2 + C (q : ℤ)) ^ i).natDegree +
            (X ^ (n - i)).natDegree := by
          refine (Polynomial.natDegree_mul_le).trans ?_
          refine Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ ≤ 0 + 2 * i + (n - i) := by
          gcongr
          · simp
          · exact (Polynomial.natDegree_pow_le).trans
              ((Nat.mul_le_mul_left i h2).trans_eq (Nat.mul_comm i 2))
          · simp
      _ < 2 * n := by omega
  · intro hcon
    simp at hcon

/-- The auxiliary polynomial evaluated at `0` is `q ^ n`. -/
private lemma aeval_zero_auxPoly (q : ℕ) :
    aeval (0 : ℂ) (auxPoly A q) = (q : ℂ) ^ n := by
  unfold auxPoly
  rw [map_sum]
  rw [Finset.sum_eq_single n]
  · have hcoeff : A.charpoly.coeff n = 1 := by
      have hnd : A.charpoly.natDegree = n := by
        simp [Matrix.charpoly_natDegree_eq_dim]
      have h := A.charpoly_monic.coeff_natDegree
      rwa [hnd] at h
    simp [hcoeff]
  · intro i hi hin
    rw [Finset.mem_range] at hi
    simp only [map_mul, map_pow, aeval_X, map_add, aeval_C]
    have hne : n - i ≠ 0 := by omega
    simp [zero_pow hne]
  · intro hcon
    simp at hcon

/-- Evaluating the auxiliary polynomial over `ℚ` agrees with evaluating it
over `ℤ`. -/
private lemma aeval_map_auxPoly (q : ℕ) (x : ℂ) :
    aeval x ((auxPoly A q).map (algebraMap ℤ ℚ)) = aeval x (auxPoly A q) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def,
    ← IsScalarTower.algebraMap_eq ℤ ℚ ℂ]

/-- A complex solution of a real quadratic with discriminant at most `0` has
absolute value `√q`. -/
private lemma norm_eq_sqrt_of_quadratic {q : ℕ} {μ β : ℂ} (hμ : ∃ r : ℝ, μ = (r : ℂ))
    (hbound : ‖μ‖ ≤ 2 * Real.sqrt q) (hβ : β ^ 2 - μ * β + q = 0) :
    ‖β‖ = Real.sqrt q := by
  obtain ⟨r, hr⟩ := hμ
  subst hr
  have hβc : (star β) ^ 2 - (r : ℂ) * star β + (q : ℂ) = 0 := by
    have h := congrArg star hβ
    simpa using h
  have hprod : (β - star β) * (β + star β - (r : ℂ)) = 0 := by
    linear_combination hβ - hβc
  have hfinish : Complex.normSq β = (q : ℝ) → ‖β‖ = Real.sqrt q := by
    intro hns
    have hnorm : ‖β‖ = Real.sqrt (Complex.normSq β) :=
      (RCLike.sqrt_normSq_eq_norm (z := β)).symm
    rw [hnorm, hns]
  rcases mul_eq_zero.mp hprod with hcase | hcase
  · have hβeq : β = star β := sub_eq_zero.mp hcase
    have him : β.im = 0 := by
      have h := congrArg Complex.im hβeq
      simp at h
      linarith
    have hβreal : β = (β.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him]
    have hβr : β ^ 2 - (r : ℂ) * β + (q : ℂ) = 0 := hβ
    rw [hβreal] at hβr
    have hs : β.re ^ 2 - r * β.re + (q : ℝ) = 0 := by
      have h2 : ((β.re ^ 2 - r * β.re + (q : ℝ) : ℝ) : ℂ) = 0 := by
        push_cast
        exact hβr
      exact_mod_cast h2
    have hrbound : |r| ≤ 2 * Real.sqrt q := by
      have hnormr : ‖(r : ℂ)‖ = |r| := by simp
      rwa [hnormr] at hbound
    have hr2 : r ^ 2 ≤ 4 * (q : ℝ) := by
      have hsq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith [Real.sqrt_nonneg (q : ℝ), abs_nonneg r, sq_nonneg (|r| - 2 * Real.sqrt q),
        sq_abs r]
    have hsq : (β.re - r / 2) ^ 2 = r ^ 2 / 4 - (q : ℝ) := by linear_combination hs
    have h0 : (β.re - r / 2) ^ 2 = 0 :=
      le_antisymm (by linarith [hsq, hr2, sq_nonneg (β.re - r / 2)]) (sq_nonneg _)
    have hsr : β.re = r / 2 := by
      have h := pow_eq_zero_iff (two_ne_zero) |>.mp h0
      linarith
    have hsq2 : β.re ^ 2 = (q : ℝ) := by nlinarith [hs, hsr, hsq, h0]
    apply hfinish
    rw [Complex.normSq_apply, him]
    simp only [mul_zero, add_zero]
    linear_combination hsq2
  · have hstar_eq : star β = (r : ℂ) - β := by linear_combination hcase
    have hprodq : β * star β = (q : ℂ) := by
      rw [hstar_eq]
      linear_combination -hβ
    apply hfinish
    have h : ((Complex.normSq β : ℝ) : ℂ) = (q : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
      exact hprodq
    exact_mod_cast h

end isWeilNumber_of_ramanujan

/-- **Ramanujan graphs give Weil numbers.** Let $q$ be a natural number and let $A$ be a symmetric
$n \times n$ matrix with integer entries such that every complex root $\mu \ne q + 1$ of its
characteristic polynomial satisfies $|\mu| \le 2\sqrt{q}$. Let $\mu \ne q + 1$ be a complex root
of the characteristic polynomial of $A$ and let $\alpha \in \mathbb{C}$ satisfy
$\alpha^2 - \mu\alpha + q = 0$. Then $\alpha$ is an algebraic integer, and every complex root of
the minimal polynomial of $\alpha$ over $\mathbb{Q}$ has absolute value $\sqrt{q}$; that is,
$\alpha$ is a Weil $q$-number.

When $A$ is the adjacency matrix of a $(q + 1)$-regular graph $X$, the hypothesis says that $X$ is
Ramanujan, and the numbers $\alpha$ are the inverse roots of
$P_X(u) = \prod_{\mu \ne q + 1} (1 - \mu u + q u^2)$. The paper takes $q = p^a$ and $X$
connected; neither assumption is needed.

Source: Daniel Vallières, *Elliptic Curves over Finite Fields and Ramanujan Graphs on Two
Vertices*, INTEGERS 24 (2024), Article A8, Proposition 1 (`integers-2024-A8-prop-1`). -/
theorem isWeilNumber_of_ramanujan {n q : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.IsSymm)
    (hram : ∀ μ ∈ A.charpoly.aroots ℂ, μ ≠ (q : ℂ) + 1 → ‖μ‖ ≤ 2 * Real.sqrt q)
    {μ α : ℂ} (hμ : μ ∈ A.charpoly.aroots ℂ) (hμq : μ ≠ (q : ℂ) + 1)
    (hα : α ^ 2 - μ * α + q = 0) :
    IsIntegral ℤ α ∧ ∀ β ∈ (minpoly ℚ α).aroots ℂ, ‖β‖ = Real.sqrt q := by
  have hQeval : aeval α (isWeilNumber_of_ramanujan.auxPoly A q) = 0 := by
    rw [isWeilNumber_of_ramanujan.aeval_auxPoly A q hα]
    have hμeval : aeval μ A.charpoly = 0 := (Polynomial.mem_aroots.mp hμ).2
    rw [hμeval]
    simp
  have hIntZ : IsIntegral ℤ α :=
    ⟨isWeilNumber_of_ramanujan.auxPoly A q,
      isWeilNumber_of_ramanujan.auxPoly_monic A q, hQeval⟩
  have hIntQ : IsIntegral ℚ α :=
    ⟨(isWeilNumber_of_ramanujan.auxPoly A q).map (algebraMap ℤ ℚ),
      (isWeilNumber_of_ramanujan.auxPoly_monic A q).map _,
      by
        change aeval α ((isWeilNumber_of_ramanujan.auxPoly A q).map (algebraMap ℤ ℚ)) = 0
        rw [isWeilNumber_of_ramanujan.aeval_map_auxPoly A q α]
        exact hQeval⟩
  refine ⟨hIntZ, ?_⟩
  intro β hβ
  rw [Polynomial.mem_aroots] at hβ
  have hβaeval : aeval β (minpoly ℚ α) = 0 := hβ.2
  have hβQ : aeval β (isWeilNumber_of_ramanujan.auxPoly A q) = 0 := by
    have hdvd : minpoly ℚ α ∣ (isWeilNumber_of_ramanujan.auxPoly A q).map (algebraMap ℤ ℚ) :=
      minpoly.dvd ℚ α (by rw [isWeilNumber_of_ramanujan.aeval_map_auxPoly A q α]; exact hQeval)
    obtain ⟨s, hs⟩ := hdvd
    have h0 : aeval β ((isWeilNumber_of_ramanujan.auxPoly A q).map (algebraMap ℤ ℚ)) = 0 := by
      rw [hs, map_mul, hβaeval, zero_mul]
    rwa [isWeilNumber_of_ramanujan.aeval_map_auxPoly A q β] at h0
  by_cases hβ0 : β = 0
  · subst hβ0
    rw [isWeilNumber_of_ramanujan.aeval_zero_auxPoly A q] at hβQ
    obtain ⟨i, hi⟩ := isWeilNumber_of_ramanujan.exists_eigenvalue_of_mem_aroots A hA hμ
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        exact Fin.elim0 i
      · exact h
    have hq : (q : ℂ) = 0 := by
      have h := (pow_eq_zero_iff hn.ne').mp hβQ
      exact h
    have hq0 : q = 0 := by exact_mod_cast hq
    rw [hq0]
    simp
  · set μ' : ℂ := (β ^ 2 + (q : ℂ)) / β with hμ'def
    have hβ' : β ^ 2 - μ' * β + (q : ℂ) = 0 := by
      rw [hμ'def, div_mul_cancel₀ _ hβ0]
      ring
    have haevalμ' : aeval μ' A.charpoly = 0 := by
      have h := isWeilNumber_of_ramanujan.aeval_auxPoly A q hβ'
      rw [hβQ] at h
      have hβn : β ^ n ≠ 0 := pow_ne_zero n hβ0
      exact (mul_eq_zero.mp h.symm).resolve_left hβn
    have hμ' : μ' ∈ A.charpoly.aroots ℂ := by
      rw [Polynomial.mem_aroots]
      exact ⟨A.charpoly_monic.ne_zero, haevalμ'⟩
    have hμ'ne : μ' ≠ (q : ℂ) + 1 := by
      intro hEq
      have hβ'' : β ^ 2 - ((q : ℂ) + 1) * β + (q : ℂ) = 0 := by rwa [hEq] at hβ'
      have hfac : (β - 1) * (β - (q : ℂ)) = 0 := by linear_combination hβ''
      rcases mul_eq_zero.mp hfac with h1 | hq1
      · have hβ1 : β = (1 : ℂ) := by linear_combination h1
        have hαβ : α = β := by
          have hconj : IsConjRoot ℚ α β :=
            isConjRoot_of_aeval_eq_zero hIntQ hβaeval
          have hβalg : β = algebraMap ℚ ℂ (1 : ℚ) := by simp [hβ1]
          have hminβ : minpoly ℚ β = X - C (1 : ℚ) := by
            rw [hβalg]
            exact minpoly.eq_X_sub_C_of_algebraMap_inj (1 : ℚ)
              (RingHom.injective (algebraMap ℚ ℂ))
          have hminα : minpoly ℚ α = X - C (1 : ℚ) := by
            rw [isConjRoot_def] at hconj
            rw [hconj, hminβ]
          have hα1 : α = (1 : ℂ) := by
            have h := minpoly.aeval ℚ α
            rw [hminα] at h
            have hsub : α - (1 : ℂ) = 0 := by
              have h' := h
              rw [map_sub, aeval_X, aeval_C] at h'
              simpa using h'
            exact sub_eq_zero.mp hsub
          rw [hα1, hβ1]
        rw [hαβ] at hα
        have hcontra : (μ' - μ) * β = 0 := by linear_combination hα - hβ'
        rcases mul_eq_zero.mp hcontra with hdiff | hβz
        · have : μ' = μ := by linear_combination hdiff
          rw [hEq] at this
          exact hμq this.symm
        · exact hβ0 hβz
      · have hβq : β = (q : ℂ) := by linear_combination hq1
        have hαβ : α = β := by
          have hconj : IsConjRoot ℚ α β :=
            isConjRoot_of_aeval_eq_zero hIntQ hβaeval
          have hβalg : β = algebraMap ℚ ℂ (q : ℚ) := by simp [hβq]
          have hminβ : minpoly ℚ β = X - C (q : ℚ) := by
            rw [hβalg]
            exact minpoly.eq_X_sub_C_of_algebraMap_inj (q : ℚ)
              (RingHom.injective (algebraMap ℚ ℂ))
          have hminα : minpoly ℚ α = X - C (q : ℚ) := by
            rw [isConjRoot_def] at hconj
            rw [hconj, hminβ]
          have hαq : α = (q : ℂ) := by
            have h := minpoly.aeval ℚ α
            rw [hminα] at h
            have hsub : α - (q : ℂ) = 0 := by
              have h' := h
              rw [map_sub, aeval_X, aeval_C] at h'
              simpa using h'
            exact sub_eq_zero.mp hsub
          rw [hαq, hβq]
        rw [hαβ] at hα
        have hcontra : (μ' - μ) * β = 0 := by linear_combination hα - hβ'
        rcases mul_eq_zero.mp hcontra with hdiff | hβz
        · have : μ' = μ := by linear_combination hdiff
          rw [hEq] at this
          exact hμq this.symm
        · exact hβ0 hβz
    obtain ⟨i, hi⟩ := isWeilNumber_of_ramanujan.exists_eigenvalue_of_mem_aroots A hA hμ'
    exact isWeilNumber_of_ramanujan.norm_eq_sqrt_of_quadratic
      ⟨(isWeilNumber_of_ramanujan.isHermitian_hermitianMatrix A hA).eigenvalues i, hi⟩
      (hram μ' hμ' hμ'ne) hβ'

end MetaMathlibExt
