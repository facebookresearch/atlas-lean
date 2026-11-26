/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.ContinuedFractions.RationalFunctionFareyPath
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Farey paths of polynomials with all determinants −1

We prove `MetaMathlibExt.polyContFract_of_farey_path_det_neg_one`, the signed convergent
formula for Farey paths with increasing denominator degrees and adjacent determinants
minus one, by reduction to the determinant-one case.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 4.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

private theorem neg_one_pow_mul_pred {F : Type*} [Field F] (i : ℕ) (hi : 1 ≤ i) :
    (-1 : F) ^ i * (-1 : F) ^ (i - 1) = -1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show 1 + j - 1 = j by omega, ← pow_add]
  exact Odd.neg_one_pow ⟨j, by omega⟩

private theorem neg_one_pow_mul_pred_two {F : Type*} [Field F] (i : ℕ) (hi : 2 ≤ i) :
    (-1 : F) ^ i * (-1 : F) ^ (i - 2) = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show 2 + j - 2 = j by omega, ← pow_add]
  exact Even.neg_one_pow ⟨j + 1, by omega⟩

private theorem alternating_sign_mul {F : Type*} [Field F] (i : ℕ) :
    (if i % 4 = 0 ∨ i % 4 = 1 then (1 : F) else -1) * (-1 : F) ^ i =
      (if i % 4 = 0 ∨ i % 4 = 3 then (1 : F) else -1) := by
  have h4 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · have he : Even i := ⟨i / 2, by omega⟩
    simp [h, he.neg_one_pow]
  · have ho : Odd i := ⟨i / 2, by omega⟩
    simp [h, ho.neg_one_pow]
  · have he : Even i := ⟨i / 2, by omega⟩
    simp [h, he.neg_one_pow]
  · have ho : Odd i := ⟨i / 2, by omega⟩
    simp [h, ho.neg_one_pow]

/-- **Farey paths of polynomials with all determinants −1.** Let $F$ be a field, let
$n \in \mathbb{N}$, and let $u_i, v_i \in F[X]$ for $i \ge 0$. Suppose that $v_0 = 1$ and that
for $1 \le i \le n$ we have $\deg v_{i-1} < \deg v_i$ and $u_i v_{i-1} - u_{i-1} v_i = -1$. Let
$a_0, a_1, \ldots \in F[X]$ satisfy $a_0 = u_0$, $a_1 = -v_1$ and
$a_i = (-1)^{i+1} (u_i v_{i-2} - u_{i-2} v_i)$ for $2 \le i \le n$. Then $a_i$ is nonconstant
for $1 \le i \le n$, and for every $i \le n$ the numerator $A_i$ and denominator $B_i$ of the
$i$th convergent of the continued fraction $[a_0; a_1, \ldots, a_n]$ over $F(X)$ are
$A_i = \varepsilon_i u_i$ and $B_i = \varepsilon_i v_i$, where $\varepsilon_i = 1$ if
$i \equiv 0, 3 \pmod 4$ and $\varepsilon_i = -1$ if $i \equiv 1, 2 \pmod 4$.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Corollary 4. -/
public theorem polyContFract_of_farey_path_det_neg_one {F : Type*} [Field F]
    (u v : ℕ → F[X]) (n : ℕ) (hv0 : v 0 = 1)
    (hdeg : ∀ i, 1 ≤ i → i ≤ n → (v (i - 1)).degree < (v i).degree)
    (hdet : ∀ i, 1 ≤ i → i ≤ n → u i * v (i - 1) - u (i - 1) * v i = -1)
    (a : ℕ → F[X]) (ha0 : a 0 = u 0) (ha1 : a 1 = -v 1)
    (ha : ∀ i, 2 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1)) * (u i * v (i - 2) - u (i - 2) * v i)) :
    (∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) ∧
      ∀ i ≤ n, (polyContFract a n).nums i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 3 then 1 else -1) * u i) ∧
        (polyContFract a n).dens i = algebraMap F[X] (RatFunc F)
          (C (if i % 4 = 0 ∨ i % 4 = 3 then 1 else -1) * v i) := by
  -- Apply the determinant-one case to the alternatingly negated path.
  have hpow0 : ∀ i : ℕ, (-1 : F) ^ i ≠ 0 := fun i => pow_ne_zero i (by simp)
  have hv0' : (fun i => C ((-1 : F) ^ i) * v i) 0 = 1 := by simp [hv0]
  have hdeg' : ∀ i, 1 ≤ i → i ≤ n →
      ((fun i => C ((-1 : F) ^ i) * v i) (i - 1)).degree <
        ((fun i => C ((-1 : F) ^ i) * v i) i).degree := by
    intro i hi hin
    simp only [degree_C_mul (hpow0 (i - 1)), degree_C_mul (hpow0 i)]
    exact hdeg i hi hin
  have hdet' : ∀ i, 1 ≤ i → i ≤ n →
      (fun i => C ((-1 : F) ^ i) * u i) i * (fun i => C ((-1 : F) ^ i) * v i) (i - 1) -
        (fun i => C ((-1 : F) ^ i) * u i) (i - 1) *
          (fun i => C ((-1 : F) ^ i) * v i) i = 1 := by
    intro i hi hin
    have hs : (-1 : F) ^ i * (-1 : F) ^ (i - 1) = -1 := neg_one_pow_mul_pred i hi
    have hfactor : (C ((-1 : F) ^ i) * u i) * (C ((-1 : F) ^ (i - 1)) * v (i - 1)) -
        (C ((-1 : F) ^ (i - 1)) * u (i - 1)) * (C ((-1 : F) ^ i) * v i) =
        C ((-1 : F) ^ i * (-1 : F) ^ (i - 1)) * (u i * v (i - 1) - u (i - 1) * v i) := by
      rw [map_mul]
      ring
    simp only [hfactor, hdet i hi hin, hs, map_neg, map_one, neg_mul_neg, one_mul]
  have ha0' : a 0 = (fun i => C ((-1 : F) ^ i) * u i) 0 := by simp [ha0]
  have ha1' : a 1 = (fun i => C ((-1 : F) ^ i) * v i) 1 := by simp [ha1]
  have ha' : ∀ i, 2 ≤ i → i ≤ n →
      a i = C ((-1) ^ (i + 1)) * ((fun i => C ((-1 : F) ^ i) * u i) i *
        (fun i => C ((-1 : F) ^ i) * v i) (i - 2) -
        (fun i => C ((-1 : F) ^ i) * u i) (i - 2) *
          (fun i => C ((-1 : F) ^ i) * v i) i) := by
    intro i hi hin
    have hs : (-1 : F) ^ i * (-1 : F) ^ (i - 2) = 1 := neg_one_pow_mul_pred_two i hi
    have hfactor : (C ((-1 : F) ^ i) * u i) * (C ((-1 : F) ^ (i - 2)) * v (i - 2)) -
        (C ((-1 : F) ^ (i - 2)) * u (i - 2)) * (C ((-1 : F) ^ i) * v i) =
        C ((-1 : F) ^ i * (-1 : F) ^ (i - 2)) * (u i * v (i - 2) - u (i - 2) * v i) := by
      rw [map_mul]
      ring
    simp only [ha i hi hin, hfactor, hs, map_one, one_mul]
  have hscale : ∀ (i : ℕ) (p : F[X]),
      C (if i % 4 = 0 ∨ i % 4 = 1 then (1 : F) else -1) * (C ((-1 : F) ^ i) * p) =
        C (if i % 4 = 0 ∨ i % 4 = 3 then (1 : F) else -1) * p := by
    intro i p
    rw [← mul_assoc, ← map_mul, alternating_sign_mul i]
  obtain ⟨hpos, hconv⟩ := polyContFract_of_farey_path_det_one
    (fun i => C ((-1 : F) ^ i) * u i) (fun i => C ((-1 : F) ^ i) * v i) n
    hv0' hdeg' hdet' a ha0' ha1' ha'
  refine ⟨hpos, fun i hi => ?_⟩
  obtain ⟨hnum, hden⟩ := hconv i hi
  exact ⟨by simp only [hnum, hscale], by simp only [hden, hscale]⟩

end

end MetaMathlibExt
