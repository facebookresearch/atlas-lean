/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private theorem S_diag_aux
    (K : Type*) [RCLike K]
    (S : ℝ → ℝ → ℝ → ℕ → ℕ → K)
    (hS : ∀ (a b c : ℝ) (y : K) (n : ℕ),
      (∏ j ∈ Finset.range n, (y - (j : K) * RCLike.ofReal a)) =
        ∑ k ∈ Finset.range (n + 1),
          S a b c n k * ∏ j ∈ Finset.range k,
            ((y - RCLike.ofReal c) - (j : K) * RCLike.ofReal b))
    (a b c : ℝ) (n : ℕ) : S a b c n n = 1 := by
  classical
  have : Infinite K := CharZero.infinite K
  set P : Polynomial K :=
    ∏ j ∈ Finset.range n, (Polynomial.X - Polynomial.C ((j : K) * RCLike.ofReal a)) with hP
  set Q : ℕ → Polynomial K := fun k =>
    ∏ j ∈ Finset.range k,
      ((Polynomial.X - Polynomial.C (RCLike.ofReal c)) - Polynomial.C ((j : K) * RCLike.ofReal b))
    with hQ
  have hPmonic : P.Monic := by
    rw [hP]
    apply Polynomial.monic_prod_of_monic
    intro i _
    exact Polynomial.monic_X_sub_C _
  have hQmonic : ∀ k, (Q k).Monic := by
    intro k
    rw [hQ]
    apply Polynomial.monic_prod_of_monic
    intro i _
    have heq : ((Polynomial.X - Polynomial.C (RCLike.ofReal c : K)) -
        Polynomial.C ((i : K) * RCLike.ofReal b) : Polynomial K)
      = Polynomial.X - Polynomial.C ((RCLike.ofReal c : K) + (i : K) * RCLike.ofReal b) := by
      simp only [map_add]
      ring
    rw [heq]
    exact Polynomial.monic_X_sub_C _
  have hPdeg : P.natDegree = n := by
    rw [hP, Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
    have h1 : ∀ i ∈ Finset.range n,
        ((Polynomial.X - Polynomial.C ((i : K) * RCLike.ofReal a) : Polynomial K)).natDegree = 1 :=
      fun i _ => Polynomial.natDegree_X_sub_C _
    rw [Finset.sum_congr rfl h1]
    simp
  have hQdeg : ∀ k, (Q k).natDegree = k := by
    intro k
    rw [hQ, Polynomial.natDegree_prod_of_monic]
    · have h1 : ∀ i ∈ Finset.range k,
        (((Polynomial.X - Polynomial.C (RCLike.ofReal c : K)) -
          Polynomial.C ((i : K) * RCLike.ofReal b) : Polynomial K)).natDegree = 1 := by
        intro i _
        have heq : ((Polynomial.X - Polynomial.C (RCLike.ofReal c : K)) -
            Polynomial.C ((i : K) * RCLike.ofReal b) : Polynomial K)
          = Polynomial.X - Polynomial.C ((RCLike.ofReal c : K) + (i : K) * RCLike.ofReal b) := by
          simp only [map_add]
          ring
        rw [heq]
        exact Polynomial.natDegree_X_sub_C _
      rw [Finset.sum_congr rfl h1]
      simp
    · intro i _
      have heq : ((Polynomial.X - Polynomial.C (RCLike.ofReal c : K)) -
          Polynomial.C ((i : K) * RCLike.ofReal b) : Polynomial K)
        = Polynomial.X - Polynomial.C ((RCLike.ofReal c : K) + (i : K) * RCLike.ofReal b) := by
        simp only [map_add]
        ring
      rw [heq]
      exact Polynomial.monic_X_sub_C _
  have hPeval : ∀ y : K, P.eval y = ∏ j ∈ Finset.range n, (y - (j : K) * RCLike.ofReal a) := by
    intro y
    rw [hP, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp
  have hQeval : ∀ (k : ℕ) (y : K), (Q k).eval y =
      ∏ j ∈ Finset.range k, ((y - RCLike.ofReal c) - (j : K) * RCLike.ofReal b) := by
    intro k y
    rw [hQ, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp [Polynomial.eval_sub]
  have hPoly : P = ∑ k ∈ Finset.range (n + 1), Polynomial.C (S a b c n k) * Q k := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hset : {x | Polynomial.eval x P =
        Polynomial.eval x (∑ k ∈ Finset.range (n + 1), Polynomial.C (S a b c n k) * Q k)}
        = Set.univ := by
      ext y
      simp only [Set.mem_univ, iff_true]
      change Polynomial.eval y P =
        Polynomial.eval y (∑ k ∈ Finset.range (n + 1), Polynomial.C (S a b c n k) * Q k)
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      rw [hPeval y]
      rw [hS a b c y n]
      apply Finset.sum_congr rfl
      intro k _
      rw [hQeval k y]
    rw [hset]
    exact Set.infinite_univ
  have hcoeff : P.coeff n =
      (∑ k ∈ Finset.range (n + 1), Polynomial.C (S a b c n k) * Q k).coeff n := by
    rw [hPoly]
  rw [Polynomial.finsetSum_coeff] at hcoeff
  simp only [Polynomial.coeff_C_mul] at hcoeff
  have hPcoeff : P.coeff n = 1 := by
    have h := Polynomial.Monic.coeff_natDegree hPmonic
    rw [hPdeg] at h
    exact h
  rw [hPcoeff] at hcoeff
  have hQn : (Q n).coeff n = 1 := by
    have h := Polynomial.Monic.coeff_natDegree (hQmonic n)
    rw [hQdeg n] at h
    exact h
  have hsum : (∑ k ∈ Finset.range (n + 1), S a b c n k * (Q k).coeff n) = S a b c n n := by
    rw [Finset.sum_eq_single n]
    · rw [hQn, mul_one]
    · intro k hk hkn
      have hkn' : k < n := by
        have hkle : k ≤ n := by
          have := Finset.mem_range.mp hk
          omega
        omega
      have hQc : (Q k).coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQdeg k]; exact hkn')
      rw [hQc, mul_zero]
    · intro habs
      simp at habs
  rw [hsum] at hcoeff
  exact hcoeff.symm

private theorem mat_decomp_aux
    (p : ℕ) (K : Type*) [RCLike K]
    (y : Fin p → K) (A B C : ℝ)
    (S : ℝ → ℝ → ℝ → ℕ → ℕ → K)
    (hS : ∀ (a b c : ℝ) (y : K) (n : ℕ),
      (∏ j ∈ Finset.range n, (y - (j : K) * RCLike.ofReal a)) =
        ∑ k ∈ Finset.range (n + 1),
          S a b c n k * ∏ j ∈ Finset.range k,
            ((y - RCLike.ofReal c) - (j : K) * RCLike.ofReal b))
    (hSvan : ∀ (a b c : ℝ) (n k : ℕ), n < k → S a b c n k = 0) :
    Matrix.of (fun (r s : Fin p) => ∏ j ∈ Finset.range r.val, (y s - (j : K) * RCLike.ofReal A)) =
    Matrix.of (fun (r s : Fin p) => S A B C r.val s.val) *
      Matrix.of (fun (r s : Fin p) =>
        ∏ j ∈ Finset.range r.val, ((y s - RCLike.ofReal C) - (j : K) * RCLike.ofReal B)) := by
  ext r s
  simp only [Matrix.of_apply, Matrix.mul_apply]
  have h1 := hS A B C (y s) r.val
  have hLHS : (∑ t : Fin p, S A B C r.val t.val *
      ∏ j ∈ Finset.range t.val, ((y s - RCLike.ofReal C) - (j : K) * RCLike.ofReal B))
      = ∑ k ∈ Finset.range p, (S A B C r.val k *
      ∏ j ∈ Finset.range k, ((y s - RCLike.ofReal C) - (j : K) * RCLike.ofReal B)) := by
    exact Fin.sum_univ_eq_sum_range
      (fun k => S A B C r.val k *
        ∏ j ∈ Finset.range k, ((y s - RCLike.ofReal C) - (j : K) * RCLike.ofReal B)) p
  rw [hLHS, h1]
  have hsub : Finset.range (r.val + 1) ⊆ Finset.range p := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  apply Finset.sum_subset hsub
  intro k hk hkn
  simp only [Finset.mem_range] at hk hkn
  push Not at hkn
  have hSk : S A B C r.val k = 0 := hSvan A B C r.val k (by omega)
  rw [hSk, zero_mul]

private theorem S_det_one
    (p : ℕ) (K : Type*) [RCLike K]
    (A B C : ℝ)
    (S : ℝ → ℝ → ℝ → ℕ → ℕ → K)
    (hS : ∀ (a b c : ℝ) (y : K) (n : ℕ),
      (∏ j ∈ Finset.range n, (y - (j : K) * RCLike.ofReal a)) =
        ∑ k ∈ Finset.range (n + 1),
          S a b c n k * ∏ j ∈ Finset.range k,
            ((y - RCLike.ofReal c) - (j : K) * RCLike.ofReal b))
    (hSvan : ∀ (a b c : ℝ) (n k : ℕ), n < k → S a b c n k = 0) :
    Matrix.det (Matrix.of (fun (r s : Fin p) => S A B C r.val s.val)) = 1 := by
  have hTri : (Matrix.of (fun (r s : Fin p) => S A B C r.val s.val)).IsLowerTriangular := by
    intro i j hij
    simp only [Matrix.of_apply]
    have hij' : i < j := hij
    have hval : i.val < j.val := Fin.lt_def.mp hij'
    exact hSvan A B C i.val j.val hval
  rw [Matrix.det_of_isLowerTriangular _ hTri]
  simp only [Matrix.of_apply]
  apply Finset.prod_eq_one
  intro i _
  exact S_diag_aux K S hS A B C i.val

/-- **Generalized factorial matrices: decomposition, determinant and inverse.** Let $K$ be
$\mathbb{R}$ or $\mathbb{C}$, let $p$ be a natural number, let $x_0, \dots, x_{p-1} \in K$ be
pairwise distinct, and let $\alpha, \beta, \gamma \in \mathbb{R}$. For $y \in K$,
$a \in \mathbb{R}$ and $n \in \mathbb{N}$ write $(y \mid a)_n = \prod_{j=0}^{n-1} (y - ja)$.
Let numbers $S(a, b, c; n, k) \in K$, for $a, b, c \in \mathbb{R}$ and $n, k \in \mathbb{N}$,
satisfy $S(a, b, c; n, k) = 0$ whenever $k > n$, and
$(y \mid a)_n = \sum_{k=0}^{n} S(a, b, c; n, k)\,(y - c \mid b)_k$ for all
$a, b, c \in \mathbb{R}$, $y \in K$ and $n \in \mathbb{N}$. For $a, b, c \in \mathbb{R}$ let
$\mathbf{S}(a, b, c)$ be the $p \times p$ matrix with entries $S(a, b, c; i, k)$, let $G_a$
be the $p \times p$ matrix with entries $(x_k \mid a)_i$, and let $H$ be the $p \times p$
matrix with entries $(x_k - \gamma \mid \beta)_i$, where $0 \le i, k < p$. Then
$G_\alpha = \mathbf{S}(\alpha, \beta, \gamma)\, H$; $\det G_\alpha = \det G_0$;
$\det G_0 = \prod_{0 \le i < k < p} (x_k - x_i)$; $G_\alpha$ is invertible; and
$G_\alpha^{-1} = G_0^{-1}\, \mathbf{S}(0, \alpha, 0)$.

This holds for every $p$, including $p = 0$. -/
theorem pan_vandermonde_general
    (p : ℕ)
    (K : Type*) [RCLike K]
    (x : Fin p → K)
    (α β γ : ℝ)
    (S : ℝ → ℝ → ℝ → ℕ → ℕ → K)
    (hS : ∀ (a b c : ℝ) (y : K) (n : ℕ),
      (∏ j ∈ Finset.range n, (y - (j : K) * RCLike.ofReal a)) =
        ∑ k ∈ Finset.range (n + 1),
          S a b c n k * ∏ j ∈ Finset.range k,
            ((y - RCLike.ofReal c) - (j : K) * RCLike.ofReal b))
    (hSvan : ∀ (a b c : ℝ) (n k : ℕ), n < k → S a b c n k = 0)
    (hdist : Function.Injective x) :
    (Matrix.of (fun (r c : Fin p) => ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)) =
      Matrix.of (fun (r c : Fin p) => S α β γ r.val c.val) *
        Matrix.of (fun (r c : Fin p) =>
          ∏ j ∈ Finset.range r.val, ((x c - RCLike.ofReal γ) - (j : K) * RCLike.ofReal β)))
    ∧ Matrix.det (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α))) =
      Matrix.det (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0)))
    ∧ Matrix.det (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0))) =
      ∏ ij ∈ Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2), (x ij.2 - x ij.1)
    ∧ IsUnit (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))
    ∧ (Matrix.of (fun (r c : Fin p) =>
          ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))⁻¹ =
      (Matrix.of (fun (r c : Fin p) =>
            ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0)))⁻¹ *
        Matrix.of (fun (r c : Fin p) => S 0 α 0 r.val c.val) := by
  classical
  -- First decomposition and determinant-one facts
  have hDecomp1 := mat_decomp_aux p K x α β γ S hS hSvan
  have hDetB : Matrix.det (Matrix.of (fun (r s : Fin p) => S α β γ r.val s.val)) = 1 :=
    S_det_one p K α β γ S hS hSvan
  have hDetD2 : Matrix.det (Matrix.of (fun (r s : Fin p) => S 0 β γ r.val s.val)) = 1 :=
    S_det_one p K 0 β γ S hS hSvan
  have hV2 := mat_decomp_aux p K x 0 β γ S hS hSvan
  -- det A = det V
  have hDetA_eq : Matrix.det (Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))
      = Matrix.det (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0))) := by
    rw [hDecomp1, hV2, Matrix.det_mul, Matrix.det_mul, hDetB, hDetD2]
  -- V equals transpose of vandermonde
  have hVtrans : Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal (0 : ℝ)))
      = (Matrix.vandermonde x).transpose := by
    ext r c
    simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    simp
  have hDetV : Matrix.det (Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal (0 : ℝ))))
      = (Matrix.vandermonde x).det := by
    rw [hVtrans, Matrix.det_transpose]
  have hDetVan := Matrix.det_vandermonde x
  have hConv : (∏ i, ∏ j > (i : Fin p), (x j - x i)) =
      ∏ ij ∈ Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2), (x ij.2 - x ij.1) := by
    have hIoi : ∀ i : Fin p, Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
      intro i
      ext j
      simp
    conv_rhs => rw [← Finset.univ_product_univ]
    rw [Finset.prod_filter]
    rw [Finset.prod_product]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    rw [hIoi i]
  have hVander : Matrix.det (Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal (0 : ℝ))))
      = ∏ ij ∈ Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2), (x ij.2 - x ij.1) := by
    rw [hDetV, hDetVan, hConv]
  -- nonzero product from injectivity
  have hProdNe :
      ∏ ij ∈ Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2), (x ij.2 - x ij.1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    have hne : ij.1 ≠ ij.2 := ne_of_lt hij
    have hne2 : ij.2 ≠ ij.1 := Ne.symm hne
    have hxne : x ij.2 ≠ x ij.1 := by
      intro hEq
      apply hne2
      apply hdist
      exact hEq
    exact sub_ne_zero.mpr hxne
  have hIsUnitA : IsUnit (Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α))) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [hDetA_eq, hVander]
    exact isUnit_iff_ne_zero.mpr hProdNe
  -- V = D * A for the inverse formula
  have hRaw := mat_decomp_aux p K x 0 α 0 S hS hSvan
  have hSecond : Matrix.of (fun (r s : Fin p) =>
      ∏ j ∈ Finset.range r.val, ((x s - RCLike.ofReal (0 : ℝ)) - (j : K) * RCLike.ofReal α))
      = Matrix.of (fun (r s : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x s - (j : K) * RCLike.ofReal α)) := by
    ext r s
    simp only [Matrix.of_apply]
    apply Finset.prod_congr rfl
    intro j _
    simp
  have hVA : Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal (0 : ℝ)))
      = Matrix.of (fun (r c : Fin p) => S 0 α 0 r.val c.val) *
        Matrix.of (fun (r c : Fin p) =>
          ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)) := by
    rw [hSecond] at hRaw
    exact hRaw
  have hDetADet : Matrix.det (Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α))) ≠ 0 := by
    rw [hDetA_eq, hVander]
    exact hProdNe
  have hIsUnitDetA : IsUnit (Matrix.det (Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))) :=
    isUnit_iff_ne_zero.mpr hDetADet
  have hIsUnitDetV : IsUnit (Matrix.det (Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal (0 : ℝ))))) := by
    rw [← hDetA_eq]
    exact hIsUnitDetA
  have hInv : (Matrix.of (fun (r c : Fin p) =>
      ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))⁻¹
      = (Matrix.of (fun (r c : Fin p) =>
          ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal (0 : ℝ))))⁻¹ *
        Matrix.of (fun (r c : Fin p) => S 0 α 0 r.val c.val) := by
    apply Matrix.inv_eq_left_inv
    have h1 : ((Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal (0 : ℝ))))⁻¹ *
      Matrix.of (fun (r c : Fin p) => S 0 α 0 r.val c.val)) *
      Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)) = 1 := by
      rw [Matrix.mul_assoc, ← hVA]
      exact Matrix.nonsing_inv_mul _ hIsUnitDetV
    exact h1
  exact ⟨hDecomp1, hDetA_eq, hVander, hIsUnitA, hInv⟩

set_option linter.unusedVariables false in
/--
**Pan's theorem on generalized factorial matrices.** Let $K$ be $\mathbb{R}$ or $\mathbb{C}$,
let $p$ be a positive integer, let $x_0, \dots, x_{p-1} \in K$ be pairwise distinct, and let
$\alpha, \beta, \gamma \in \mathbb{R}$. For $y \in K$, $a \in \mathbb{R}$ and $n \in \mathbb{N}$
write $(y \mid a)_n = \prod_{j=0}^{n-1} (y - ja)$. Let numbers $S(a, b, c; n, k) \in K$, for
$a, b, c \in \mathbb{R}$ and $n, k \in \mathbb{N}$, satisfy $S(a, b, c; n, k) = 0$ whenever
$k > n$, and $(y \mid a)_n = \sum_{k=0}^{n} S(a, b, c; n, k)\,(y - c \mid b)_k$ for all
$a, b, c \in \mathbb{R}$, $y \in K$ and $n \in \mathbb{N}$. For $a, b, c \in \mathbb{R}$ let
$\mathbf{S}(a, b, c)$ be the $p \times p$ matrix with entries $S(a, b, c; i, k)$, let $G_a$
be the $p \times p$ matrix with entries $(x_k \mid a)_i$, and let $H$ be the $p \times p$
matrix with entries $(x_k - \gamma \mid \beta)_i$, where $0 \le i, k < p$. Then
$G_\alpha = \mathbf{S}(\alpha, \beta, \gamma)\, H$; $\det G_\alpha = \det G_0$;
$\det G_0 = \prod_{0 \le i < k < p} (x_k - x_i)$; $G_\alpha$ is invertible; and
$G_\alpha^{-1} = G_0^{-1}\, \mathbf{S}(0, \alpha, 0)$.

Source: Jiaqiang Pan, "Matrix Decomposition of the Unified Generalized Stirling
Numbers and Inversion of the Generalized Factorial Matrices," Journal of Integer
Sequences 15 (2012), Article 12.6.6, Theorem (label t:Vandermonde), lines 428–460,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Pan/pan19.tex.
It follows from `pan_vandermonde_general`; the hypothesis `hp` is unused and keeps the
source's shape.
Proves `Wanted` entry `pan_vandermonde`.
-/
theorem pan_vandermonde :
  ∀ (p : ℕ)
    (hp : 0 < p)
    (K : Type*) [RCLike K]
    (x : Fin p → K)
    (α β γ : ℝ)
    (S : ℝ → ℝ → ℝ → ℕ → ℕ → K)
    (hS : ∀ (a b c : ℝ) (y : K) (n : ℕ),
      (∏ j ∈ Finset.range n, (y - (j : K) * RCLike.ofReal a)) =
        ∑ k ∈ Finset.range (n + 1),
          S a b c n k * ∏ j ∈ Finset.range k,
            ((y - RCLike.ofReal c) - (j : K) * RCLike.ofReal b))
    (hSvan : ∀ (a b c : ℝ) (n k : ℕ), n < k → S a b c n k = 0)
    (hdist : Function.Injective x),
    (Matrix.of (fun (r c : Fin p) => ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)) =
      Matrix.of (fun (r c : Fin p) => S α β γ r.val c.val) *
        Matrix.of (fun (r c : Fin p) =>
          ∏ j ∈ Finset.range r.val, ((x c - RCLike.ofReal γ) - (j : K) * RCLike.ofReal β)))
    ∧ Matrix.det (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α))) =
      Matrix.det (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0)))
    ∧ Matrix.det (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0))) =
      ∏ ij ∈ Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2), (x ij.2 - x ij.1)
    ∧ IsUnit (Matrix.of (fun (r c : Fin p) =>
        ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))
    ∧ (Matrix.of (fun (r c : Fin p) =>
          ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))⁻¹ =
      (Matrix.of (fun (r c : Fin p) =>
            ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0)))⁻¹ *
        Matrix.of (fun (r c : Fin p) => S 0 α 0 r.val c.val) := by
  intro p _ K _ x α β γ S hS hSvan hdist
  exact pan_vandermonde_general p K x α β γ S hS hSvan hdist

end MetaMathlibExt
