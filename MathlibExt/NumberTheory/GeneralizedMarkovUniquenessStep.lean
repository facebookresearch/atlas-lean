/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathlibExt.NumberTheory.GeneralizedMarkovCharacteristic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.GeneralizedMarkovVietaEq

/-!
# Children of generalized Cohn triples

This module defines generalized Markov numbers, the matrix `S` of the generalized Cohn
triple relation, generalized Cohn matrices and generalized Cohn triples. Its main result is
that both children of a generalized Cohn triple are generalized Cohn triples over the Vieta
jumpings of its generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.5.
-/

namespace MetaMathlibExt

private theorem vieta_jump {k x y z : ℕ} (h : IsGenMarkovTriple k x y z) :
    (x ^ 2 + k * x * y + y ^ 2) / z * z = x ^ 2 + k * x * y + y ^ 2 ∧
      IsGenMarkovTriple k x ((x ^ 2 + k * x * y + y ^ 2) / z) y := by
  obtain ⟨hx, hy, hz, he⟩ := h
  have hsum : x ^ 2 + k * x * y + y ^ 2 + (z + k * (x + y)) * z =
      (3 + 3 * k) * x * y * z := by
    linarith only [he]
  have hdiv : z ∣ x ^ 2 + k * x * y + y ^ 2 := by
    apply (Nat.dvd_add_iff_left (dvd_mul_left z (z + k * (x + y)))).mpr
    rw [hsum]
    exact dvd_mul_left ..
  have hprod : (x ^ 2 + k * x * y + y ^ 2) / z * z = x ^ 2 + k * x * y + y ^ 2 :=
    Nat.div_mul_cancel hdiv
  have hroots : (x ^ 2 + k * x * y + y ^ 2) / z + z + k * (x + y) =
      (3 + 3 * k) * x * y := by
    apply mul_right_cancel₀ hz.ne'
    linarith only [hprod, hsum]
  refine ⟨hprod, hx, ?_, hy, ?_⟩
  · apply Nat.pos_of_mul_pos_right (b := z)
    rw [hprod]
    positivity
  · linarith only [congrArg (((x ^ 2 + k * x * y + y ^ 2) / z) * ·) hroots, hprod]

private theorem cyc {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    IsGenMarkovTriple k b c a := by
  obtain ⟨ha, hb, hc, he⟩ := h
  refine ⟨hb, hc, ha, ?_⟩
  linear_combination he

@[expose] public section

/-- **Generalized Markov number.** Let $k$ be a natural number. A natural number $b$ is a
$k$-generalized Markov number when there are natural numbers $a$ and $c$ such that
$(a, b, c)$ is a $k$-generalized Markov triple.

Since the $k$-generalized Markov equation is symmetric in its three variables, this is the same
as $b$ being an entry, in any position, of some $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public def IsGenMarkovNumber (k b : ℕ) : Prop :=
  ∃ a c, IsGenMarkovTriple k a b c

/-- **The matrix $S$ of the generalized Cohn triple relation.** For a natural number $k$, $S$
is the $2 \times 2$ integer matrix

$$S = \begin{pmatrix} k & 0 \\ 3k^2 + 3k & k \end{pmatrix}.$$

It is the matrix in the relation $Q = PR - S$ that defines $k$-generalized Cohn triples.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public def genCohnS (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(k : ℤ), 0; 3 * (k : ℤ) ^ 2 + 3 * k, k]

/-- **Generalized Cohn matrices.** Let $k$ be a natural number. An integer $2 \times 2$ matrix
$P = (p_{ij})$ is a $k$-generalized Cohn matrix if $\det P = 1$, its entry $p_{12}$ is a
$k$-generalized Markov number, and its trace equals $(3 + 3k) p_{12} - k$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.1. -/
public def IsGenCohnMatrix (k : ℕ) (P : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  P.det = 1 ∧ ∃ n : ℕ, P 0 1 = n ∧ IsGenMarkovNumber k n ∧ P.trace = (3 + 3 * k) * n - k

/-- **Generalized Cohn triple.** Let $k$ be a natural number and let $S$ be the integer matrix
with rows $(k, 0)$ and $(3k^2 + 3k, k)$. A triple $(P, Q, R)$ of integer $2 \times 2$ matrices is
a $k$-generalized Cohn triple associated with natural numbers $(a, b, c)$ when $P$, $Q$ and $R$
are $k$-generalized Cohn matrices, $Q = PR - S$, the $(1, 2)$-entries of $P$, $Q$ and $R$ are
$a$, $b$ and $c$ respectively, and $(a, b, c)$ is a $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public def IsGenCohnTriple (k : ℕ) (P Q R : Matrix (Fin 2) (Fin 2) ℤ) (a b c : ℕ) : Prop :=
  IsGenCohnMatrix k P ∧ IsGenCohnMatrix k Q ∧ IsGenCohnMatrix k R ∧ Q = P * R - genCohnS k ∧
    P 0 1 = a ∧ Q 0 1 = b ∧ R 0 1 = c ∧ IsGenMarkovTriple k a b c

/-- **Children of a generalized Cohn triple.** Let $k$ be a natural number, let $S$ be the integer
matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$, and let $(P, Q, R)$ be a $k$-generalized Cohn
triple associated with $(a, b, c)$. Then $(P, PQ - S, Q)$ is a $k$-generalized Cohn triple
associated with $(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$, and $(Q, QR - S, R)$ is a
$k$-generalized Cohn triple associated with $(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.5. -/
public theorem IsGenCohnTriple.step {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k P (P * Q - genCohnS k) Q a ((a ^ 2 + k * a * b + b ^ 2) / c) b ∧
      IsGenCohnTriple k Q (Q * R - genCohnS k) R b ((b ^ 2 + k * b * c + c ^ 2) / a) c := by
  obtain ⟨hP, hQm, hRm, hQeq, hP01, hQ01, hR01, hMark⟩ := h
  have hPc := hP
  obtain ⟨hPdet, nP, hP01w, _, hPt⟩ := hPc
  have hnP : nP = a := Nat.cast_injective (hP01w.symm.trans hP01)
  subst nP
  have hQc := hQm
  obtain ⟨hQdet, nQ, hQ01w, _, hQt⟩ := hQc
  have hnQ : nQ = b := Nat.cast_injective (hQ01w.symm.trans hQ01)
  subst nQ
  have hRc := hRm
  obtain ⟨hRdet, nR, hR01w, _, hRt⟩ := hRc
  have hnR : nR = c := Nat.cast_injective (hR01w.symm.trans hR01)
  subst nR
  have s00 : genCohnS k 0 0 = (k : ℤ) := by simp [genCohnS]
  have s01 : genCohnS k 0 1 = 0 := by simp [genCohnS]
  have s10 : genCohnS k 1 0 = 3 * (k : ℤ) ^ 2 + 3 * k := by simp [genCohnS]
  have s11 : genCohnS k 1 1 = (k : ℤ) := by simp [genCohnS]
  have eQ00 : Q 0 0 = P 0 0 * R 0 0 + (a : ℤ) * R 1 0 - (k : ℤ) := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hQeq
    simpa only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hP01, s00] using h
  have eQ01 : (b : ℤ) = P 0 0 * (c : ℤ) + (a : ℤ) * R 1 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hQeq
    simpa only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hQ01, hR01, hP01, s01,
      sub_zero] using h
  have eQ10 : Q 1 0 = P 1 0 * R 0 0 + P 1 1 * R 1 0 - (3 * (k : ℤ) ^ 2 + 3 * k) := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hQeq
    simpa only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, s10] using h
  have eQ11 : Q 1 1 = P 1 0 * (c : ℤ) + P 1 1 * R 1 1 - (k : ℤ) := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hQeq
    simpa only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hR01, s11] using h
  have eDp : P 0 0 * P 1 1 - (a : ℤ) * P 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hP01] using hPdet
  have eDr : R 0 0 * R 1 1 - (c : ℤ) * R 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hR01] using hRdet
  have eTp : P 0 0 + P 1 1 = (3 + 3 * (k : ℤ)) * (a : ℤ) - k := by
    simpa only [Matrix.trace_fin_two] using hPt
  have eTq : Q 0 0 + Q 1 1 = (3 + 3 * (k : ℤ)) * (b : ℤ) - k := by
    simpa only [Matrix.trace_fin_two] using hQt
  have eTr : R 0 0 + R 1 1 = (3 + 3 * (k : ℤ)) * (c : ℤ) - k := by
    simpa only [Matrix.trace_fin_two] using hRt
  have ePQ00 : (P * Q) 0 0 = P 0 0 * Q 0 0 + (a : ℤ) * Q 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP01]
  have ePQ01 : (P * Q) 0 1 = P 0 0 * (b : ℤ) + (a : ℤ) * Q 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hP01, hQ01]
  have ePQ11 : (P * Q) 1 1 = P 1 0 * (b : ℤ) + P 1 1 * Q 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hQ01]
  have eQR00 : (Q * R) 0 0 = Q 0 0 * R 0 0 + (b : ℤ) * R 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hQ01]
  have eQR01 : (Q * R) 0 1 = Q 0 0 * (c : ℤ) + (b : ℤ) * R 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hQ01, hR01]
  have eQR11 : (Q * R) 1 1 = Q 1 0 * (c : ℤ) + Q 1 1 * R 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR01]
  have eM101 : (P * Q - genCohnS k) 0 1 = P 0 0 * (b : ℤ) + (a : ℤ) * Q 1 1 := by
    simp only [Matrix.sub_apply, s01, sub_zero, ePQ01]
  have eM201 : (Q * R - genCohnS k) 0 1 = Q 0 0 * (c : ℤ) + (b : ℤ) * R 1 1 := by
    simp only [Matrix.sub_apply, s01, sub_zero, eQR01]
  have hE1 : (P * Q - genCohnS k) 0 1 =
      (3 + 3 * (k : ℤ)) * (a : ℤ) * (b : ℤ) - (c : ℤ) - (k : ℤ) * ((a : ℤ) + (b : ℤ)) := by
    rw [eM101]
    linear_combination (b : ℤ) * eTp + (a : ℤ) * eQ11 - P 1 1 * eQ01 - (c : ℤ) * eDp
  have hE2 : (Q * R - genCohnS k) 0 1 =
      (3 + 3 * (k : ℤ)) * (b : ℤ) * (c : ℤ) - (a : ℤ) - (k : ℤ) * ((b : ℤ) + (c : ℤ)) := by
    rw [eM201]
    linear_combination (c : ℤ) * eQ00 - R 0 0 * eQ01 - (a : ℤ) * eDr + (b : ℤ) * eTr
  have eTsum1 : (P * Q) 0 0 + (P * Q) 1 1 =
      (3 + 3 * (k : ℤ)) * ((3 + 3 * (k : ℤ)) * (a : ℤ) * (b : ℤ) - (c : ℤ) -
        (k : ℤ) * ((a : ℤ) + (b : ℤ))) + k := by
    rw [ePQ00, ePQ11]
    linear_combination (P 0 0 - ((3 + 3 * (k : ℤ)) * (a : ℤ) - k)) * eQ00 +
      (a : ℤ) * eQ10 + (P 1 1 - ((3 + 3 * (k : ℤ)) * (a : ℤ) - k)) * eQ11 -
      (R 0 0 + R 1 1) * eDp +
      (P 0 0 * R 0 0 + (a : ℤ) * R 1 0 - k + R 1 1 * P 1 1 + (c : ℤ) * P 1 0) * eTp +
      P 1 0 * eQ01 + ((3 + 3 * (k : ℤ)) * (a : ℤ) - k) * eTq - eTr
  have eTsum2 : (Q * R) 0 0 + (Q * R) 1 1 =
      (3 + 3 * (k : ℤ)) * ((3 + 3 * (k : ℤ)) * (b : ℤ) * (c : ℤ) - (a : ℤ) -
        (k : ℤ) * ((b : ℤ) + (c : ℤ))) + k := by
    rw [eQR00, eQR11]
    linear_combination (R 0 0 - ((3 + 3 * (k : ℤ)) * (c : ℤ) - k)) * eQ00 +
      (c : ℤ) * eQ10 + (R 1 1 - ((3 + 3 * (k : ℤ)) * (c : ℤ) - k)) * eQ11 -
      (P 0 0 + P 1 1) * eDr +
      ((c : ℤ) * P 1 0 + P 1 1 * R 1 1 - k + P 0 0 * R 0 0 + (a : ℤ) * R 1 0) * eTr +
      R 1 0 * eQ01 + ((3 + 3 * (k : ℤ)) * (c : ℤ) - k) * eTq - eTp
  have hT1 : (P * Q - genCohnS k).trace =
      (3 + 3 * (k : ℤ)) * ((3 + 3 * (k : ℤ)) * (a : ℤ) * (b : ℤ) - (c : ℤ) -
        (k : ℤ) * ((a : ℤ) + (b : ℤ))) - k := by
    have htr : (P * Q - genCohnS k).trace = (P * Q) 0 0 + (P * Q) 1 1 - 2 * (k : ℤ) := by
      rw [Matrix.trace_fin_two]
      simp only [Matrix.sub_apply, s00, s11]
      ring
    rw [htr]
    linear_combination eTsum1
  have hT2 : (Q * R - genCohnS k).trace =
      (3 + 3 * (k : ℤ)) * ((3 + 3 * (k : ℤ)) * (b : ℤ) * (c : ℤ) - (a : ℤ) -
        (k : ℤ) * ((b : ℤ) + (c : ℤ))) - k := by
    have htr : (Q * R - genCohnS k).trace = (Q * R) 0 0 + (Q * R) 1 1 - 2 * (k : ℤ) := by
      rw [Matrix.trace_fin_two]
      simp only [Matrix.sub_apply, s00, s11]
      ring
    rw [htr]
    linear_combination eTsum2
  have eDetPQ : (P * Q) 0 0 * (P * Q) 1 1 - (P * Q) 0 1 * (P * Q) 1 0 = 1 := by
    have h : (P * Q).det = 1 := by rw [Matrix.det_mul, hPdet, hQdet, mul_one]
    simpa only [Matrix.det_fin_two] using h
  have eDetQR : (Q * R) 0 0 * (Q * R) 1 1 - (Q * R) 0 1 * (Q * R) 1 0 = 1 := by
    have h : (Q * R).det = 1 := by rw [Matrix.det_mul, hQdet, hRdet, mul_one]
    simpa only [Matrix.det_fin_two] using h
  have eEntry1 : (P * Q) 0 1 =
      (3 + 3 * (k : ℤ)) * (a : ℤ) * (b : ℤ) - (c : ℤ) - (k : ℤ) * ((a : ℤ) + (b : ℤ)) := by
    have h := hE1
    rwa [Matrix.sub_apply, s01, sub_zero] at h
  have eEntry2 : (Q * R) 0 1 =
      (3 + 3 * (k : ℤ)) * (b : ℤ) * (c : ℤ) - (a : ℤ) - (k : ℤ) * ((b : ℤ) + (c : ℤ)) := by
    have h := hE2
    rwa [Matrix.sub_apply, s01, sub_zero] at h
  have hD1 : (P * Q - genCohnS k).det = 1 := by
    have hdet : (P * Q - genCohnS k).det =
        ((P * Q) 0 0 - (k : ℤ)) * ((P * Q) 1 1 - (k : ℤ)) -
          (P * Q) 0 1 * ((P * Q) 1 0 - (3 * (k : ℤ) ^ 2 + 3 * k)) := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, s00, s01, s10, s11, sub_zero]
    rw [hdet]
    linear_combination eDetPQ - (k : ℤ) * eTsum1 +
      (3 * (k : ℤ) ^ 2 + 3 * k) * eEntry1
  have hD2 : (Q * R - genCohnS k).det = 1 := by
    have hdet : (Q * R - genCohnS k).det =
        ((Q * R) 0 0 - (k : ℤ)) * ((Q * R) 1 1 - (k : ℤ)) -
          (Q * R) 0 1 * ((Q * R) 1 0 - (3 * (k : ℤ) ^ 2 + 3 * k)) := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, s00, s01, s10, s11, sub_zero]
    rw [hdet]
    linear_combination eDetQR - (k : ℤ) * eTsum2 +
      (3 * (k : ℤ) ^ 2 + 3 * k) * eEntry2
  have hJ1 := vieta_jump hMark
  have hJ2 := vieta_jump (cyc hMark)
  have hV := IsGenMarkovTriple.vieta_eq hMark
  obtain ⟨hJ1prod, hJ1mark⟩ := hJ1
  obtain ⟨hJ2prod, hJ2mark⟩ := hJ2
  have hB1 : (P * Q - genCohnS k) 0 1 =
      (((a ^ 2 + k * a * b + b ^ 2) / c : ℕ) : ℤ) := by
    have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast hMark.2.2.1.ne'
    apply mul_left_cancel₀ hc0
    have h1 : (c : ℤ) * (((a ^ 2 + k * a * b + b ^ 2) / c : ℕ) : ℤ) =
        (a : ℤ) ^ 2 + (k : ℤ) * (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2 := by
      have hc1 := congrArg (Nat.cast : ℕ → ℤ) hJ1prod
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] at hc1
      linear_combination hc1
    rw [hE1, h1]
    linear_combination -hV.1
  have hB2 : (Q * R - genCohnS k) 0 1 =
      (((b ^ 2 + k * b * c + c ^ 2) / a : ℕ) : ℤ) := by
    have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast hMark.1.ne'
    apply mul_left_cancel₀ ha0
    have h1 : (a : ℤ) * (((b ^ 2 + k * b * c + c ^ 2) / a : ℕ) : ℤ) =
        (b : ℤ) ^ 2 + (k : ℤ) * (b : ℤ) * (c : ℤ) + (c : ℤ) ^ 2 := by
      have hc1 := congrArg (Nat.cast : ℕ → ℤ) hJ2prod
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] at hc1
      linear_combination hc1
    rw [hE2, h1]
    linear_combination -hV.2
  have hVn1 : (3 + 3 * (k : ℤ)) * (a : ℤ) * (b : ℤ) - (c : ℤ) -
      (k : ℤ) * ((a : ℤ) + (b : ℤ)) = (((a ^ 2 + k * a * b + b ^ 2) / c : ℕ) : ℤ) := by
    linear_combination hB1 - hE1
  have hVn2 : (3 + 3 * (k : ℤ)) * (b : ℤ) * (c : ℤ) - (a : ℤ) -
      (k : ℤ) * ((b : ℤ) + (c : ℤ)) = (((b ^ 2 + k * b * c + c ^ 2) / a : ℕ) : ℤ) := by
    linear_combination hB2 - hE2
  have hT1' : (P * Q - genCohnS k).trace =
      (3 + 3 * (k : ℤ)) * (((a ^ 2 + k * a * b + b ^ 2) / c : ℕ) : ℤ) - k := by
    rw [hT1, hVn1]
  have hT2' : (Q * R - genCohnS k).trace =
      (3 + 3 * (k : ℤ)) * (((b ^ 2 + k * b * c + c ^ 2) / a : ℕ) : ℤ) - k := by
    rw [hT2, hVn2]
  have hM1 : IsGenCohnMatrix k (P * Q - genCohnS k) :=
    ⟨hD1, (a ^ 2 + k * a * b + b ^ 2) / c, hB1, ⟨a, b, hJ1mark⟩, hT1'⟩
  have hM2 : IsGenCohnMatrix k (Q * R - genCohnS k) :=
    ⟨hD2, (b ^ 2 + k * b * c + c ^ 2) / a, hB2, ⟨b, c, hJ2mark⟩, hT2'⟩
  exact ⟨⟨hP, hM1, hQm, rfl, hP01, hB1, hQ01, hJ1mark⟩,
    ⟨hQm, hM2, hRm, rfl, hQ01, hB2, hR01, hJ2mark⟩⟩

end

end MetaMathlibExt
