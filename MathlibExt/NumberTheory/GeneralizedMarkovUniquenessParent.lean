/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import MathlibExt.NumberTheory.GeneralizedMarkovCharacteristic
public import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessMulEMul
public import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessExistsUniqueMemGenCohnTree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parent triples of generalized Cohn triples

Using the generalized Markov numbers and Cohn matrices of
`MathlibExt.NumberTheory.GeneralizedMarkovUniquenessMulEMul`, and the matrix `genCohnS` and
generalized Cohn triples of
`MathlibExt.NumberTheory.GeneralizedMarkovUniquenessExistsUniqueMemGenCohnTree`, this module
proves that both parent constructions preserve generalized Cohn triples.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.11.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem parent_markov {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    let d := (a ^ 2 + k * a * c + c ^ 2) / b
    IsGenMarkovTriple k a d c ∧ d + b + k * (a + c) = (3 + 3 * k) * a * c := by
  obtain ⟨ha, hb, hc, he⟩ := h
  intro d
  have hsum : a ^ 2 + k * a * c + c ^ 2 + (b + k * (a + c)) * b =
      (3 + 3 * k) * a * c * b := by linarith only [he]
  have hdiv : b ∣ a ^ 2 + k * a * c + c ^ 2 := by
    apply (Nat.dvd_add_iff_left (dvd_mul_left b (b + k * (a + c)))).mpr
    rw [hsum]
    exact dvd_mul_left ..
  have hprod : d * b = a ^ 2 + k * a * c + c ^ 2 := Nat.div_mul_cancel hdiv
  have hroots : d + b + k * (a + c) = (3 + 3 * k) * a * c := by
    apply mul_right_cancel₀ hb.ne'
    linarith only [hprod, hsum]
  refine ⟨⟨ha, ?_, hc, ?_⟩, hroots⟩
  · apply Nat.pos_of_mul_pos_right (b := b)
    rw [hprod]
    positivity
  · linarith only [congrArg (d * ·) hroots, hprod]

private theorem cohn_trace {k n : ℕ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnMatrix k A) (hn : A 0 1 = n) :
    A.trace = (3 + 3 * k) * n - k := by
  obtain ⟨m, hm, _, ht⟩ := h.2
  have hmn : m = n := Nat.cast_injective (hm.symm.trans hn)
  simpa only [hmn] using ht

private theorem cohn_add_det {k n : ℕ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnMatrix k A) (hn : A 0 1 = n) : (A + genCohnS k).det = 1 := by
  have ht := cohn_trace h hn
  have hd := h.1
  simp only [Matrix.trace_fin_two] at ht
  simp only [Matrix.det_fin_two, hn] at hd
  simp [Matrix.det_fin_two, genCohnS, hn]
  linear_combination hd + (k : ℤ) * ht

private theorem cohn_inv {A : Matrix (Fin 2) (Fin 2) ℤ} (hd : A.det = 1) :
    A⁻¹ = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  simp [Matrix.inv_def, hd, Matrix.adjugate_fin_two]

private theorem parent_matrices {k a b c d : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (hP : IsGenCohnMatrix k P) (hQ : IsGenCohnMatrix k Q) (hR : IsGenCohnMatrix k R)
    (hrel : Q = P * R - genCohnS k) (ha : P 0 1 = a) (hb : Q 0 1 = b)
    (hc : R 0 1 = c) (hd : (d : ℤ) = (3 + 3 * k) * a * c - b - k * (a + c))
    (hm : IsGenMarkovNumber k d) :
    IsGenCohnMatrix k (P⁻¹ * (R + genCohnS k)) ∧
      (P⁻¹ * (R + genCohnS k)) 0 1 = d ∧
      IsGenCohnMatrix k ((P + genCohnS k) * R⁻¹) ∧
      ((P + genCohnS k) * R⁻¹) 0 1 = d := by
  have htP := cohn_trace hP ha
  have htQ := cohn_trace hQ hb
  have htR := cohn_trace hR hc
  simp only [Matrix.trace_fin_two] at htP htR
  have hentry : P 0 0 * (c : ℤ) + (a : ℤ) * R 1 1 = b := by
    simpa [hrel, Matrix.mul_apply, Fin.sum_univ_two, genCohnS, ha, hc] using hb
  have htrace : P 0 0 * R 0 0 + (a : ℤ) * R 1 0 + P 1 0 * (c : ℤ) +
      P 1 1 * R 1 1 = (3 + 3 * k) * b + k := by
    simp [hrel, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, genCohnS,
      ha, hc] at htQ
    linarith only [htQ]
  have hleft_entry : (P⁻¹ * (R + genCohnS k)) 0 1 = d := by
    simp [cohn_inv hP.1, Matrix.mul_apply, Fin.sum_univ_two, genCohnS, ha, hc]
    linear_combination (c : ℤ) * htP - hentry - hd
  have hright_entry : ((P + genCohnS k) * R⁻¹) 0 1 = d := by
    simp [cohn_inv hR.1, Matrix.mul_apply, Fin.sum_univ_two, genCohnS, ha, hc]
    linear_combination (a : ℤ) * htR - hentry - hd
  have hleft_trace : (P⁻¹ * (R + genCohnS k)).trace = (3 + 3 * k) * d - k := by
    simp only [cohn_inv hP.1, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, genCohnS, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, ha, hc]
    linear_combination (R 0 0 + R 1 1 + (k : ℤ)) * htP +
      ((3 + 3 * (k : ℤ)) * a - k) * htR - htrace - (3 + 3 * (k : ℤ)) * hd
  have hright_trace : ((P + genCohnS k) * R⁻¹).trace = (3 + 3 * k) * d - k := by
    simp [cohn_inv hR.1, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      genCohnS, ha, hc]
    linear_combination (R 0 0 + R 1 1) * htP +
      ((3 + 3 * (k : ℤ)) * a) * htR - htrace - (3 + 3 * (k : ℤ)) * hd
  refine ⟨⟨?_, d, hleft_entry, hm, hleft_trace⟩, hleft_entry,
    ⟨?_, d, hright_entry, hm, hright_trace⟩, hright_entry⟩
  · simp [Matrix.det_mul, Matrix.det_nonsing_inv, hP.1, cohn_add_det hR hc]
  · simp [Matrix.det_mul, Matrix.det_nonsing_inv, hR.1, cohn_add_det hP ha]

/-- **Parent triples of a generalized Cohn triple.** Let $k$ be a natural number and let $S$ be
the integer matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$. Let $(P, Q, R)$ be a $k$-generalized
Cohn triple associated with $(a, b, c)$, and let $b' = \lfloor (a^2 + kac + c^2)/b \rfloor$. Then
$(P, R, P^{-1}(R + S))$ is a $k$-generalized Cohn triple associated with $(a, c, b')$, and
$((P + S)R^{-1}, P, R)$ is a $k$-generalized Cohn triple associated with $(b', a, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.11. -/
public theorem IsGenCohnTriple.parent {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k P R (P⁻¹ * (R + genCohnS k)) a c ((a ^ 2 + k * a * c + c ^ 2) / b) ∧
      IsGenCohnTriple k ((P + genCohnS k) * R⁻¹) P R ((a ^ 2 + k * a * c + c ^ 2) / b) a c := by
  obtain ⟨hP, hQ, hR, hrel, ha, hb, hc, hm⟩ := h
  obtain ⟨hmarkov, hroots⟩ := parent_markov hm
  let d := (a ^ 2 + k * a * c + c ^ 2) / b
  have hd : (d : ℤ) = (3 + 3 * k) * a * c - b - k * (a + c) := by
    have hz : (d : ℤ) + b + k * (a + c) = (3 + 3 * k) * a * c := by
      exact_mod_cast hroots
    linarith only [hz]
  obtain ⟨hL, hLe, hV, hVe⟩ := parent_matrices hP hQ hR hrel ha hb hc hd ⟨a, c, hmarkov⟩
  refine ⟨⟨hP, hR, hL, ?_, ha, hc, hLe, ?_⟩,
    ⟨hV, hP, hR, ?_, hVe, ha, hc, ?_⟩⟩
  · rw [Matrix.mul_nonsing_inv_cancel_left P _ (by simp [hP.1]), add_sub_cancel_right]
  · exact ⟨hmarkov.1, hmarkov.2.2.1, hmarkov.2.1, by linarith only [hmarkov.2.2.2]⟩
  · rw [Matrix.nonsing_inv_mul_cancel_right R _ (by simp [hR.1]), add_sub_cancel_right]
  · exact ⟨hmarkov.2.1, hmarkov.1, hmarkov.2.2.1, by linarith only [hmarkov.2.2.2]⟩

end

end MetaMathlibExt
