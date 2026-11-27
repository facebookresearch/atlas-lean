/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The polynomials of the algebraic part of Belyi's theorem

This file proves the two polynomial lemmas behind the "only if" direction of Belyi's theorem in
B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265,
Theorem 3.3, p. 262.

* `Polynomial.exists_natDegree_pos_aeval_mem_range_algebraicClosure`: Köck's Lemma 3.5,
  pp. 262–263, in algebraic form. For a finite set `S` of elements of an algebraic closure of
  `ℚ` there is a nonconstant `p ∈ ℚ[X]` that takes rational values on `S` and at every zero of
  its derivative. `Polynomial.exists_natDegree_pos_aeval_mem_range_of_isAlgebraic` is the same
  statement in any field `K` with an algebra structure over `ℚ`, for a finite set of elements
  algebraic over `ℚ`.
* `Polynomial.belyiPolynomial` and `Polynomial.belyiPolynomial_spec`: the polynomial
  `q₁ = c z ^ m (1 - z) ^ n` with `c = (m + n) ^ (m + n) / (m ^ m n ^ n)` from the proof of Köck's
  Lemma 3.6, p. 263, its values at `0`, `1` and `m / (m + n)`, and its derivative
  `-c z ^ (m - 1) (1 - z) ^ (n - 1) ((m + n) z - m)`, which Köck gives up to a constant.

## Proof of Lemma 3.5

Köck takes `S` closed under conjugation, lets `p₁` be the product of the minimal polynomials of
its elements, and applies induction to the set `S₁` of values of `p₁` at the zeros of `p₁'`. Here
the induction runs on the degree of a nonzero `f ∈ ℚ[X]` vanishing on `S`, and `S₁` is replaced
by the roots of the minimal polynomial `g` of the class of `f` in `ℚ[X] ⧸ (f')`. That `g` has
degree at most `deg f - 1`, and `g (f r) = 0` whenever `f' r = 0`; this avoids conjugation.
-/

@[expose] public section

open Polynomial

namespace Polynomial

section RationalCriticalValues

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **Critical values of a rational polynomial are roots of a rational polynomial of smaller
degree.** For `f ∈ ℚ[X]` with `f' ≠ 0` there is a nonzero `g ∈ ℚ[X]` with
`deg g ≤ deg f'` and `g (f r) = 0` for every `r ∈ K` with `f' r = 0`.

This is the degree count of the proof of Lemma 3.5 in B. Köck, *Belyi's theorem revisited*,
Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, pp. 262–263: there the set `S₁` of values of
`p₁` at the zeros of `p₁'` has at most `n - 1` elements. Here `g` is the minimal polynomial of
the class of `f` in `ℚ[X] ⧸ (f')`. -/
theorem exists_ne_zero_aeval_eq_zero_of_aeval_derivative_eq_zero (f : ℚ[X])
    (hf : derivative f ≠ 0) :
    ∃ g : ℚ[X], g ≠ 0 ∧ g.natDegree ≤ (derivative f).natDegree ∧
      ∀ r : K, aeval r (derivative f) = 0 → aeval (aeval r f) g = 0 := by
  set h := derivative f
  let pb := AdjoinRoot.powerBasis hf
  have : Module.Finite ℚ (AdjoinRoot h) := pb.finite
  have : Module.Free ℚ (AdjoinRoot h) := Module.Free.of_basis pb.basis
  refine ⟨minpoly ℚ (AdjoinRoot.mk h f), minpoly.ne_zero (IsIntegral.of_finite ℚ _), ?_, ?_⟩
  · refine (minpoly.natDegree_le _).trans ?_
    rw [pb.finrank, AdjoinRoot.powerBasis_dim]
  · intro r hr
    have hmk :
        AdjoinRoot.liftAlgHom h (Algebra.ofId ℚ K) r hr (AdjoinRoot.mk h f) = aeval r f := by
      simp [AdjoinRoot.liftAlgHom, aeval_def]
    rw [← hmk, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

/-- **Köck's Lemma 3.5 for the roots of a rational polynomial.** For every nonzero `f ∈ ℚ[X]`
there is a nonconstant `p ∈ ℚ[X]` such that `p s ∈ ℚ` for every root `s ∈ K` of `f`, and
`p r ∈ ℚ` for every `r ∈ K` with `p' r = 0`.

This is the induction in the proof of Lemma 3.5 in B. Köck, *Belyi's theorem revisited*,
Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, pp. 262–263, run on the degree of `f`. -/
theorem exists_natDegree_pos_aeval_mem_range_of_aeval_eq_zero (f : ℚ[X]) (hf : f ≠ 0) :
    ∃ p : ℚ[X], 0 < p.natDegree ∧
      (∀ s : K, aeval s f = 0 → aeval s p ∈ Set.range (algebraMap ℚ K)) ∧
      ∀ r : K, aeval r (derivative p) = 0 → aeval r p ∈ Set.range (algebraMap ℚ K) := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hn1 : n ≤ 1
  · refine ⟨X, by simp, ?_, ?_⟩
    · intro s hs
      rw [aeval_X]
      rw [eq_X_add_C_of_natDegree_le_one (hn ▸ hn1 : f.natDegree ≤ 1)] at hs hf
      simp only [map_add, map_mul, aeval_C, aeval_X] at hs
      by_cases ha : f.coeff 1 = 0
      · simp only [ha, map_zero, zero_mul, zero_add, FaithfulSMul.algebraMap_eq_zero_iff] at hs
        simp [ha, hs] at hf
      · refine ⟨-f.coeff 0 / f.coeff 1, ?_⟩
        have ha' : algebraMap ℚ K (f.coeff 1) ≠ 0 :=
          (FaithfulSMul.algebraMap_eq_zero_iff ℚ K).not.mpr ha
        rw [map_div₀, map_neg, div_eq_iff ha']
        linear_combination -hs
    · intro r hr
      simp at hr
  · have hd : derivative f ≠ 0 := fun h0 => by
      have := derivative_eq_zero.mp h0
      omega
    obtain ⟨g, hg0, hgdeg, hg⟩ :=
      exists_ne_zero_aeval_eq_zero_of_aeval_derivative_eq_zero (K := K) f hd
    have hlt : g.natDegree < n :=
      hgdeg.trans_lt (hn ▸ natDegree_derivative_lt (by omega))
    obtain ⟨p₂, hp₂deg, hp₂S, hp₂C⟩ := ih _ hlt g hg0 rfl
    refine ⟨p₂.comp f, ?_, ?_, ?_⟩
    · rw [natDegree_comp]
      exact Nat.mul_pos hp₂deg (by omega)
    · intro s hs
      rw [aeval_comp, hs]
      exact ⟨p₂.coeff 0, by rw [aeval_def, eval₂_at_zero]⟩
    · intro r hr
      rw [derivative_comp, map_mul, aeval_comp, mul_eq_zero] at hr
      rw [aeval_comp]
      rcases hr with hr | hr
      · exact hp₂S _ (hg r hr)
      · exact hp₂C _ hr

/-- **Köck's Lemma 3.5, in any field over `ℚ`.** Let `K` be a field with an algebra structure
over `ℚ` and `S ⊆ K` a finite set of elements algebraic over `ℚ`. Then there is a nonconstant
polynomial `p ∈ ℚ[X]` such that `p s ∈ ℚ` for every `s ∈ S` and `p r ∈ ℚ` for every `r ∈ K` with
`p' r = 0`.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265,
Lemma 3.5 and its proof, pp. 262–263: "Let S be a finite subset of Q̄. Then there is a
non-constant polynomial p ∈ Q[z] such that p(S) and the critical values of p : P¹_C → P¹_C lie
in Q ∪ {∞}." With `K = ℂ` the zeros of `p'` in `K` are Köck's critical points other than `∞`;
`exists_natDegree_pos_aeval_mem_range_algebraicClosure` is the case `K = Q̄`. -/
theorem exists_natDegree_pos_aeval_mem_range_of_isAlgebraic (S : Set K) (hS : S.Finite)
    (halg : ∀ s ∈ S, IsAlgebraic ℚ s) :
    ∃ p : ℚ[X], 0 < p.natDegree ∧
      (∀ s ∈ S, aeval s p ∈ Set.range (algebraMap ℚ K)) ∧
      ∀ r : K, aeval r (derivative p) = 0 → aeval r p ∈ Set.range (algebraMap ℚ K) := by
  classical
  let f : ℚ[X] := ∏ s ∈ hS.toFinset, minpoly ℚ s
  have hf : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s hs =>
    minpoly.ne_zero (halg s (hS.mem_toFinset.mp hs)).isIntegral
  obtain ⟨p, hpdeg, hpS, hpC⟩ :=
    exists_natDegree_pos_aeval_mem_range_of_aeval_eq_zero (K := K) f hf
  refine ⟨p, hpdeg, fun s hs => hpS s ?_, hpC⟩
  rw [map_prod]
  exact Finset.prod_eq_zero (hS.mem_toFinset.mpr hs) (minpoly.aeval ℚ s)

/-- **Köck's Lemma 3.5, polynomial with rational critical values.** Let `Q̄` be an algebraic
closure of `ℚ` and `S ⊆ Q̄` a finite set. Then there is a nonconstant polynomial `p ∈ ℚ[X]` such
that `p s ∈ ℚ` for every `s ∈ S` and `p r ∈ ℚ` for every `r ∈ Q̄` with `p' r = 0`.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265,
Lemma 3.5 and its proof, pp. 262–263. Köck states that `p(S)` and the critical values of
`p : P¹ → P¹` lie in `Q ∪ {∞}`; the critical values other than `∞` are the values of `p` at the
zeros of `p'`, as in his proof ("S₁ ∪ {∞} is the set of critical values of p₁"). -/
theorem exists_natDegree_pos_aeval_mem_range_algebraicClosure
    (S : Set (AlgebraicClosure ℚ)) (hS : S.Finite) :
    ∃ p : ℚ[X], 0 < p.natDegree ∧
      (∀ s ∈ S, aeval s p ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ))) ∧
      ∀ r : AlgebraicClosure ℚ, aeval r (derivative p) = 0 →
        aeval r p ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) :=
  exists_natDegree_pos_aeval_mem_range_of_isAlgebraic S hS fun s _ =>
    Algebra.IsAlgebraic.isAlgebraic s

end RationalCriticalValues

section BelyiPolynomial

/-- **The polynomial `c z ^ m (1 - z) ^ n` of Köck's Lemma 3.6.** For natural numbers `m` and `n`,
`belyiPolynomial m n = c X ^ m (1 - X) ^ n ∈ ℚ[X]` with
`c = (m + n) ^ (m + n) / (m ^ m n ^ n)`.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof of
Lemma 3.6, p. 263, where it is `q₁` and `m, n` are positive. -/
noncomputable def belyiPolynomial (m n : ℕ) : ℚ[X] :=
  C (((m + n : ℚ) ^ (m + n)) / ((m : ℚ) ^ m * (n : ℚ) ^ n)) * X ^ m * (1 - X) ^ n

variable (m n : ℕ)

/-- `q₁ (0) = 0` for `m > 0`, where `q₁ = c z ^ m (1 - z) ^ n`
(B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), proof of Lemma 3.6,
p. 263). -/
theorem belyiPolynomial_eval_zero (hm : 0 < m) : (belyiPolynomial m n).eval 0 = 0 := by
  simp [belyiPolynomial, hm.ne']

/-- `q₁ (1) = 0` for `n > 0`, where `q₁ = c z ^ m (1 - z) ^ n`
(B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), proof of Lemma 3.6,
p. 263). -/
theorem belyiPolynomial_eval_one (hn : 0 < n) : (belyiPolynomial m n).eval 1 = 0 := by
  simp [belyiPolynomial, hn.ne']

/-- `q₁ (m / (m + n)) = 1` for positive `m` and `n`, where `q₁ = c z ^ m (1 - z) ^ n` and
`c = (m + n) ^ (m + n) / (m ^ m n ^ n)`
(B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), proof of Lemma 3.6,
p. 263). -/
theorem belyiPolynomial_eval_div (hm : 0 < m) (hn : 0 < n) :
    (belyiPolynomial m n).eval ((m : ℚ) / (m + n)) = 1 := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmn : (m + n : ℚ) ≠ 0 := by positivity
  have h1 : 1 - (m : ℚ) / (m + n) = n / (m + n) := by field_simp; ring
  simp only [belyiPolynomial, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, h1,
    div_pow]
  field_simp
  ring

/-- For positive `m` and `n` and any `c ∈ ℚ`,
`(c z ^ m (1 - z) ^ n)' = -c z ^ (m - 1) (1 - z) ^ (n - 1) ((m + n) z - m)`. -/
theorem derivative_C_mul_X_pow_mul_one_sub_X_pow (c : ℚ) (hm : 0 < m) (hn : 0 < n) :
    derivative (C c * X ^ m * (1 - X) ^ n) =
      -C c * X ^ (m - 1) * (1 - X) ^ (n - 1) * (C ((m : ℚ) + n) * X - C (m : ℚ)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm.ne'
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  simp only [derivative_mul, derivative_C, derivative_pow, derivative_sub, derivative_one,
    derivative_X, Nat.add_sub_cancel, map_add, map_natCast]
  push_cast
  ring

/-- **The derivative of `q₁ = c z ^ m (1 - z) ^ n`.** For positive `m` and `n`,
`q₁' = -c z ^ (m - 1) (1 - z) ^ (n - 1) ((m + n) z - m)` with
`c = (m + n) ^ (m + n) / (m ^ m n ^ n)`.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof of
Lemma 3.6, p. 263, which says that `q₁'` "equals z^{m-1} (1 - z)^{n-1} ((m + n) z - m) up to a
constant"; the constant is `-c`. -/
theorem derivative_belyiPolynomial (hm : 0 < m) (hn : 0 < n) :
    derivative (belyiPolynomial m n) =
      -C (((m + n : ℚ) ^ (m + n)) / ((m : ℚ) ^ m * (n : ℚ) ^ n)) * X ^ (m - 1) *
        (1 - X) ^ (n - 1) * (C ((m : ℚ) + n) * X - C (m : ℚ)) :=
  derivative_C_mul_X_pow_mul_one_sub_X_pow m n _ hm hn

/-- **The zeros of `q₁'`.** For positive `m` and `n`, every zero `r` of the derivative of
`q₁ = c z ^ m (1 - z) ^ n` in a field `K` over `ℚ` is `0`, `1` or `m / (m + n)`.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof of
Lemma 3.6, p. 263. -/
theorem eq_of_aeval_derivative_belyiPolynomial_eq_zero {K : Type*} [Field K] [Algebra ℚ K]
    (hm : 0 < m) (hn : 0 < n) {r : K}
    (hr : aeval r (derivative (belyiPolynomial m n)) = 0) :
    r = 0 ∨ r = 1 ∨ r = algebraMap ℚ K ((m : ℚ) / (m + n)) := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : ((m + n : ℚ) ^ (m + n)) / ((m : ℚ) ^ m * (n : ℚ) ^ n) ≠ 0 := by positivity
  have hmnK : (m : K) + n ≠ 0 := by
    have hmnQ : (m : ℚ) + n ≠ 0 := by positivity
    have h := (FaithfulSMul.algebraMap_eq_zero_iff ℚ K).not.mpr hmnQ
    rwa [map_add, map_natCast, map_natCast] at h
  rw [derivative_belyiPolynomial m n hm hn] at hr
  simp only [map_mul, map_neg, aeval_C, aeval_X, map_pow, map_sub, map_one, map_natCast,
    mul_eq_zero, neg_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff, hc, false_or,
    pow_eq_zero_iff', sub_eq_zero] at hr
  rcases hr with ((⟨hr, -⟩ | ⟨hr, -⟩) | hr)
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr.symm)
  · refine Or.inr (Or.inr ?_)
    rw [map_div₀, map_add, map_natCast, map_natCast, eq_div_iff hmnK]
    rw [map_add, map_natCast, map_natCast] at hr
    linear_combination hr

/-- **Values and derivative of the polynomial `c z ^ m (1 - z) ^ n`.** Let `m` and `n` be
positive integers, `c = (m + n) ^ (m + n) / (m ^ m n ^ n)` and `q₁ = c z ^ m (1 - z) ^ n ∈ ℚ[z]`.
Then `q₁ (0) = q₁ (1) = 0`, `q₁ (m / (m + n)) = 1`,
`q₁' = -c z ^ (m - 1) (1 - z) ^ (n - 1) ((m + n) z - m)`, and every zero of `q₁'` in a field `K`
over `ℚ` lies in `{0, 1, m / (m + n)}`.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof of
Lemma 3.6, p. 263; Köck gives `q₁'` up to a constant, which is `-c`. -/
theorem belyiPolynomial_spec (K : Type*) [Field K] [Algebra ℚ K] (hm : 0 < m) (hn : 0 < n) :
    (belyiPolynomial m n).eval 0 = 0 ∧ (belyiPolynomial m n).eval 1 = 0 ∧
      (belyiPolynomial m n).eval ((m : ℚ) / (m + n)) = 1 ∧
      derivative (belyiPolynomial m n) =
        -C (((m + n : ℚ) ^ (m + n)) / ((m : ℚ) ^ m * (n : ℚ) ^ n)) * X ^ (m - 1) *
          (1 - X) ^ (n - 1) * (C ((m : ℚ) + n) * X - C (m : ℚ)) ∧
      ∀ r : K, aeval r (derivative (belyiPolynomial m n)) = 0 →
        r = 0 ∨ r = 1 ∨ r = algebraMap ℚ K ((m : ℚ) / (m + n)) :=
  ⟨belyiPolynomial_eval_zero m n hm, belyiPolynomial_eval_one m n hn,
    belyiPolynomial_eval_div m n hm hn, derivative_belyiPolynomial m n hm hn,
    fun _ hr => eq_of_aeval_derivative_belyiPolynomial_eq_zero m n hm hn hr⟩

end BelyiPolynomial

end Polynomial
