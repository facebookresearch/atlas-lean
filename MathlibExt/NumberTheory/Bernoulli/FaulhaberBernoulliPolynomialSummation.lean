/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star

namespace MetaMathlibExt

@[expose] public section

/-- Two polynomials over ℚ agree if derivatives and values at 0 agree. -/
private theorem poly_eq_of_deriv_eval_zero {P Q : Polynomial ℚ} (hd : P.derivative = Q.derivative)
    (h0 : P.eval 0 = Q.eval 0) : P = Q := by
  have hsub : (P - Q).derivative = 0 := by rw [Polynomial.derivative_sub, hd, sub_self]
  have hPQ := Polynomial.eq_C_of_derivative_eq_zero hsub
  have hcoeff : (P - Q).coeff 0 = 0 := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_sub, h0, sub_self]
  have hPQ0 : P - Q = 0 := by rw [hPQ, hcoeff, Polynomial.C_0]
  exact sub_eq_zero.mp hPQ0

/-- Bernoulli polynomial evaluated at a point, from the definition. -/
private theorem bernoulli_eval_eq (k : ℕ) (a : ℚ) :
    (Polynomial.bernoulli k).eval a =
      ∑ i ∈ Finset.range (k + 1), _root_.bernoulli i * (k.choose i : ℚ) * a ^ (k - i) := by
  unfold Polynomial.bernoulli
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_monomial]

/-- Addition formula for Bernoulli polynomials: shifting by a constant. -/
private theorem bernoulli_comp_add_C (k : ℕ) (a : ℚ) :
    (Polynomial.bernoulli k).comp (Polynomial.X + Polynomial.C a) =
      ∑ s ∈ Finset.range (k + 1),
        Polynomial.C ((k.choose s : ℚ) * a ^ (k - s)) * Polynomial.bernoulli s := by
  induction k with
  | zero =>
    simp [Polynomial.bernoulli_zero]
  | succ k ih =>
    apply poly_eq_of_deriv_eval_zero
    · have hNCC : ((k : ℕ) : Polynomial ℚ).comp (Polynomial.X + Polynomial.C a)
          = ((k : ℕ) : Polynomial ℚ) :=
        map_natCast (Polynomial.compRingHom (Polynomial.X + Polynomial.C a)) k
      have hK : ((k : Polynomial ℚ) + 1) = (((k + 1 : ℕ)) : Polynomial ℚ) := by simp
      have hder : ((Polynomial.bernoulli (k + 1)).comp
            (Polynomial.X + Polynomial.C a)).derivative
            = (((k + 1 : ℕ)) : Polynomial ℚ) *
              ((Polynomial.bernoulli k).comp (Polynomial.X + Polynomial.C a)) := by
        rw [Polynomial.derivative_comp, Polynomial.derivative_bernoulli_add_one,
          Polynomial.derivative_X_add_C, one_mul, Polynomial.mul_comp,
          Polynomial.add_comp, Polynomial.one_comp, hNCC, hK]
      rw [hder, ih]
      have hRHS : (∑ s ∈ Finset.range (k + 1 + 1),
            Polynomial.C ((((k + 1).choose s : ℕ) : ℚ) * a ^ (k + 1 - s)) *
              Polynomial.bernoulli s).derivative
          = (((k + 1 : ℕ)) : Polynomial ℚ) * (∑ t ∈ Finset.range (k + 1),
            Polynomial.C (((k.choose t : ℕ) : ℚ) * a ^ (k - t)) *
              Polynomial.bernoulli t) := by
        rw [Polynomial.derivative_sum, Finset.sum_range_succ']
        have hz : (Polynomial.C ((((k + 1).choose 0 : ℕ) : ℚ) * a ^ (k + 1 - 0)) *
            Polynomial.bernoulli 0).derivative = 0 := by
          simp
        rw [hz, add_zero, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mem_range] at ht
        rw [Polynomial.derivative_C_mul, Polynomial.derivative_bernoulli]
        have hCt1 : (((t + 1 : ℕ)) : Polynomial ℚ)
            = Polynomial.C ((((t + 1 : ℕ))) : ℚ) := by exact_mod_cast rfl
        have hCk1 : Polynomial.C ((((k + 1 : ℕ))) : ℚ)
            = (((k + 1 : ℕ)) : Polynomial ℚ) := by exact_mod_cast rfl
        have hbin : ((((k + 1).choose (t + 1) : ℕ)) : ℚ) * ((((t + 1 : ℕ))) : ℚ)
            = ((((k + 1 : ℕ))) : ℚ) * ((((k.choose t : ℕ))) : ℚ) := by
          have h := Nat.add_one_mul_choose_eq k t
          have hQ := congrArg (Nat.cast : ℕ → ℚ) h
          push_cast at hQ
          have e1 : ((((t + 1 : ℕ))) : ℚ) = ((t : ℚ) + 1) := by simp
          have e2 : ((((k + 1 : ℕ))) : ℚ) = ((k : ℚ) + 1) := by simp
          rw [e1, e2]
          exact hQ.symm
        have hpow : k + 1 - (t + 1) = k - t := by omega
        rw [hpow, show t + 1 - 1 = t from Nat.add_sub_cancel t 1]
        have hC1 : Polynomial.C ((((k + 1).choose (t + 1) : ℕ)) : ℚ) *
            (((t + 1 : ℕ)) : Polynomial ℚ)
            = (((k + 1 : ℕ)) : Polynomial ℚ) *
              Polynomial.C ((((k.choose t : ℕ))) : ℚ) := by
          rw [hCt1, ← Polynomial.C_mul, hbin, Polynomial.C_mul, hCk1]
        calc Polynomial.C ((((k + 1).choose (t + 1) : ℕ) : ℚ) * a ^ (k - t)) *
                ((((t + 1 : ℕ)) : Polynomial ℚ) * Polynomial.bernoulli t)
            = (Polynomial.C ((((k + 1).choose (t + 1) : ℕ)) : ℚ) *
                (((t + 1 : ℕ)) : Polynomial ℚ)) *
                (Polynomial.C (a ^ (k - t)) * Polynomial.bernoulli t) := by
              rw [Polynomial.C_mul]
              ring
          _ = ((((k + 1 : ℕ)) : Polynomial ℚ) *
                Polynomial.C ((((k.choose t : ℕ))) : ℚ)) *
                (Polynomial.C (a ^ (k - t)) * Polynomial.bernoulli t) := by
              rw [hC1]
          _ = (((k + 1 : ℕ)) : Polynomial ℚ) * (Polynomial.C ((((k.choose t : ℕ)) : ℚ) *
                a ^ (k - t)) * Polynomial.bernoulli t) := by
              rw [Polynomial.C_mul]
              ring
      exact hRHS.symm
    · rw [Polynomial.eval_comp]
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]
      rw [bernoulli_eval_eq, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.bernoulli_eval_zero]
      ring

/-- `Polynomial.C` distributes over finset sums. -/
private theorem C_finset_sum (s : Finset ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ s, Polynomial.C (f j) = Polynomial.C (∑ j ∈ s, f j) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, ← Polynomial.C_add]

/-- Power sum starting at 1, via Faulhaber. -/
private theorem shifted_power_sum (m n : ℕ) :
    ((m : ℚ) + 1) * ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ m =
      (Polynomial.bernoulli (m + 1)).eval ((n : ℚ) + 1) +
        (-1) ^ m * _root_.bernoulli (m + 1) := by
  have eN : ((((n + 1 : ℕ))) : ℚ) = ((n : ℚ) + 1) := by simp
  cases m with
  | zero =>
    rw [show (0 : ℕ) + 1 = 1 from rfl]
    have hB1 : (Polynomial.bernoulli 1).eval ((n : ℚ) + 1) = (n : ℚ) + 1 - 1 / 2 := by
      rw [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      ring
    rw [hB1, _root_.bernoulli_one]
    simp only [Nat.cast_zero, zero_add, one_mul, pow_zero, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, one_mul]
    ring
  | succ m =>
    have hFaul := Polynomial.sum_range_pow_eq_bernoulli_sub (n + 1) (m + 1)
    simp only [Nat.succ_eq_add_one] at hFaul
    rw [eN, Finset.sum_range_succ'] at hFaul
    have hz : ((((0 : ℕ))) : ℚ) ^ (m + 1) = 0 := by simp
    rw [hz, add_zero] at hFaul
    have hS : ∑ j ∈ Finset.range n, ((((j + 1 : ℕ))) : ℚ) ^ (m + 1)
        = ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (m + 1) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.cast_add, Nat.cast_one]
    rw [hS] at hFaul
    rcases Nat.even_or_odd (m + 1) with hev | hodd
    · rw [hev.neg_one_pow]
      have hodd2 : Odd (m + 1 + 1) := hev.add_one
      have hlt : 1 < m + 1 + 1 := by omega
      have hB0 : _root_.bernoulli (m + 1 + 1) = 0 :=
        _root_.bernoulli_eq_zero_of_odd hodd2 hlt
      rw [hB0] at hFaul ⊢
      linear_combination hFaul
    · rw [hodd.neg_one_pow]
      linear_combination hFaul

/-! # Faulhaber-type Bernoulli polynomial summation formula
-/

/-- **Faulhaber-type summation formula for Bernoulli polynomials.** Let $B_i$ denote the
$i$-th Bernoulli number, with $B_1 = -1/2$, and let
$B_j(X) = \sum_{i=0}^{j} \binom{j}{i} B_i X^{j-i} \in \mathbb{Q}[X]$ be the $j$-th Bernoulli
polynomial. For all natural numbers $k$ and $n$, the following identity holds in $\mathbb{Q}[X]$:
$$\sum_{j=1}^{n} B_k(X + j) = \frac{1}{k+1} \sum_{r=0}^{k} \binom{k+1}{r+1}
\left(B_{r+1}(n+1) + (-1)^r B_{r+1}\right) B_{k-r}(X).$$

Proves `Wanted` entry `faulhaber_bernoulli_polynomial_sum`.

Source: Claudio de J. Pita Ruiz V., *Carlitz-Type and Other Bernoulli
Identities*, Journal of Integer Sequences 19 (2016), Article 16.1.8,
<https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex>,
Proposition [Faulhaber-type formula], equation (5.32), lines 1001-1007.
-/
theorem faulhaber_bernoulli_polynomial_sum
    (k n : ℕ) :
    Finset.sum (Finset.range n) (fun j =>
      (Polynomial.bernoulli k).comp (Polynomial.X + Polynomial.C ((j : ℚ) + 1))) =
      Polynomial.C (1 / ((k : ℚ) + 1)) * Finset.sum (Finset.range (k + 1)) (fun r =>
        Polynomial.C ((Nat.choose (k + 1) (r + 1) : ℚ) *
          ((Polynomial.bernoulli (r + 1)).eval ((n : ℚ) + 1) +
            (-1 : ℚ) ^ r * _root_.bernoulli (r + 1))) *
          Polynomial.bernoulli (k - r)) := by
  have e1 : (Finset.sum (Finset.range n) (fun j =>
        (Polynomial.bernoulli k).comp (Polynomial.X + Polynomial.C ((j : ℚ) + 1))))
        = ∑ j ∈ Finset.range n, ∑ s ∈ Finset.range (k + 1),
            Polynomial.C ((k.choose s : ℚ) * ((j : ℚ) + 1) ^ (k - s)) *
              Polynomial.bernoulli s :=
    Finset.sum_congr rfl fun j _ => bernoulli_comp_add_C k _
  rw [e1, Finset.sum_comm]
  have e2 : ∀ s ∈ Finset.range (k + 1),
      (∑ j ∈ Finset.range n, Polynomial.C ((k.choose s : ℚ) * ((j : ℚ) + 1) ^ (k - s)) *
        Polynomial.bernoulli s)
      = Polynomial.C ((k.choose s : ℚ) *
          ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (k - s)) *
        Polynomial.bernoulli s := by
    intro s _
    calc ∑ j ∈ Finset.range n, Polynomial.C ((k.choose s : ℚ) * ((j : ℚ) + 1) ^ (k - s)) *
            Polynomial.bernoulli s
        = ∑ j ∈ Finset.range n, Polynomial.C (k.choose s : ℚ) *
            (Polynomial.C (((j : ℚ) + 1) ^ (k - s)) * Polynomial.bernoulli s) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Polynomial.C_mul, mul_assoc]
      _ = Polynomial.C (k.choose s : ℚ) *
            ∑ j ∈ Finset.range n, (Polynomial.C (((j : ℚ) + 1) ^ (k - s)) *
              Polynomial.bernoulli s) := by
          rw [Finset.mul_sum]
      _ = Polynomial.C (k.choose s : ℚ) *
            ((∑ j ∈ Finset.range n, Polynomial.C (((j : ℚ) + 1) ^ (k - s))) *
              Polynomial.bernoulli s) := by
          rw [Finset.sum_mul]
      _ = Polynomial.C (k.choose s : ℚ) *
            (Polynomial.C (∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (k - s)) *
              Polynomial.bernoulli s) := by
          rw [C_finset_sum]
      _ = Polynomial.C ((k.choose s : ℚ) *
            ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (k - s)) *
          Polynomial.bernoulli s := by
          rw [Polynomial.C_mul, mul_assoc]
  have e3 : (∑ s ∈ Finset.range (k + 1), ∑ j ∈ Finset.range n,
        Polynomial.C ((k.choose s : ℚ) * ((j : ℚ) + 1) ^ (k - s)) *
          Polynomial.bernoulli s)
      = ∑ s ∈ Finset.range (k + 1), Polynomial.C ((k.choose s : ℚ) *
          ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (k - s)) *
        Polynomial.bernoulli s :=
    Finset.sum_congr rfl e2
  rw [e3, Finset.mul_sum]
  refine Finset.sum_bij (fun s _ => k - s) ?hi ?hinj ?hsurj ?hterm
  · intro s hs
    rw [Finset.mem_range] at hs ⊢
    omega
  · intro s₁ hs₁ s₂ hs₂ heq
    rw [Finset.mem_range] at hs₁ hs₂
    omega
  · intro r hr
    rw [Finset.mem_range] at hr
    refine ⟨k - r, Finset.mem_range.mpr (by omega), ?_⟩
    exact Nat.sub_sub_self (by omega)
  · intro s hs
    have hsk : s ≤ k := by
      rw [Finset.mem_range, Nat.lt_succ_iff] at hs
      exact hs
    have ekk : k - (k - s) = s := Nat.sub_sub_self hsk
    show Polynomial.C ((k.choose s : ℚ) *
          ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (k - s)) * Polynomial.bernoulli s
        = Polynomial.C (1 / ((k : ℚ) + 1)) *
          (Polynomial.C ((Nat.choose (k + 1) ((k - s) + 1) : ℚ) *
            ((Polynomial.bernoulli ((k - s) + 1)).eval ((n : ℚ) + 1) +
              (-1 : ℚ) ^ (k - s) * _root_.bernoulli ((k - s) + 1))) *
            Polynomial.bernoulli (k - (k - s)))
    rw [ekk]
    have hPS := shifted_power_sum (k - s) n
    have hBn := Nat.add_one_mul_choose_eq k (k - s)
    rw [Nat.choose_symm hsk] at hBn
    have hBinQ := congrArg (Nat.cast : ℕ → ℚ) hBn
    push_cast at hBinQ
    have hd : ((((k - s : ℕ))) : ℚ) + 1 ≠ 0 := by positivity
    have hK : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hSV : ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (k - s)
        = ((Polynomial.bernoulli ((k - s) + 1)).eval ((n : ℚ) + 1) +
            (-1 : ℚ) ^ (k - s) * _root_.bernoulli ((k - s) + 1)) /
          (((((k - s : ℕ))) : ℚ) + 1) := by
      rw [eq_div_iff hd, mul_comm]
      exact hPS
    have hscal : (k.choose s : ℚ) * ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (k - s)
        = ((Nat.choose (k + 1) ((k - s) + 1) : ℚ) / ((k : ℚ) + 1)) *
          ((Polynomial.bernoulli ((k - s) + 1)).eval ((n : ℚ) + 1) +
            (-1 : ℚ) ^ (k - s) * _root_.bernoulli ((k - s) + 1)) := by
      rw [hSV]
      field_simp
      linear_combination
        ((Polynomial.bernoulli ((k - s) + 1)).eval ((n : ℚ) + 1) +
          (-1 : ℚ) ^ (k - s) * _root_.bernoulli ((k - s) + 1)) * hBinQ
    calc Polynomial.C ((k.choose s : ℚ) *
            ∑ j ∈ Finset.range n, ((j : ℚ) + 1) ^ (k - s)) * Polynomial.bernoulli s
        = Polynomial.C (((Nat.choose (k + 1) ((k - s) + 1) : ℚ) / ((k : ℚ) + 1)) *
            ((Polynomial.bernoulli ((k - s) + 1)).eval ((n : ℚ) + 1) +
              (-1 : ℚ) ^ (k - s) * _root_.bernoulli ((k - s) + 1))) *
            Polynomial.bernoulli s := by
          rw [hscal]
      _ = Polynomial.C (1 / ((k : ℚ) + 1)) *
            (Polynomial.C ((Nat.choose (k + 1) ((k - s) + 1) : ℚ) *
              ((Polynomial.bernoulli ((k - s) + 1)).eval ((n : ℚ) + 1) +
                (-1 : ℚ) ^ (k - s) * _root_.bernoulli ((k - s) + 1))) *
              Polynomial.bernoulli s) := by
          have e : ((Nat.choose (k + 1) ((k - s) + 1) : ℚ) / ((k : ℚ) + 1)) *
                ((Polynomial.bernoulli ((k - s) + 1)).eval ((n : ℚ) + 1) +
                  (-1 : ℚ) ^ (k - s) * _root_.bernoulli ((k - s) + 1))
              = (1 / ((k : ℚ) + 1)) *
                ((Nat.choose (k + 1) ((k - s) + 1) : ℚ) *
                  ((Polynomial.bernoulli ((k - s) + 1)).eval ((n : ℚ) + 1) +
                    (-1 : ℚ) ^ (k - s) * _root_.bernoulli ((k - s) + 1))) := by
            ring
          rw [e, Polynomial.C_mul, mul_assoc]

end

end MetaMathlibExt
