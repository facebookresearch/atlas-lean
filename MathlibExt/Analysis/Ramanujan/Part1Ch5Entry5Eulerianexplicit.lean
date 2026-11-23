/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry4
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 5

Formulas (5.1) and (5.2) of Entry 5 from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985): two finite expansions of the Eulerian polynomial `chapter5Psi n p`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry5Eulerianexplicit

open scoped Nat BigOperators Polynomial
open Finset Entry4

noncomputable section

def chapter5Entry5Formula51Term (n : ℕ) (p : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * (n.choose k : ℂ) * chapter5Psi k p /
    (p + 1) ^ k

def chapter5Entry5Formula52Term (n : ℕ) (p : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * (n.choose (j + 1) : ℂ) * (p + 1) ^ j *
    chapter5Psi (n - j - 1) p


-- eulerianNumber is zero above the diagonal
private theorem eN_eq_zero_of_lt : ∀ (n k : ℕ), n < k → eulerianNumber n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rfl
  | succ n ih =>
    intro k hk
    have hk1 : n < k := by omega
    have hk2 : n + 1 - k = 0 := by omega
    rw [eulerianNumber]
    rw [ih k hk1, hk2]
    simp

private theorem eN_self : ∀ (n : ℕ), eulerianNumber (n + 1) (n + 1) = 0 := by
  intro n
  rw [eulerianNumber]
  have h1 : eulerianNumber n (n + 1) = 0 := eN_eq_zero_of_lt n (n + 1) (by omega)
  have h2 : n + 1 - (n + 1) = 0 := by omega
  rw [h1, h2]
  simp

private noncomputable def Apoly (n : ℕ) : ℂ[X] :=
  ∑ k ∈ range (n + 1), Polynomial.C (eulerianNumber n k : ℂ) * Polynomial.X ^ k

private theorem apoly_coeff (n j : ℕ) : (Apoly n).coeff j = (eulerianNumber n j : ℂ) := by
  rw [Apoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (range (n + 1)) j (fun k => (eulerianNumber n k : ℂ))]
  by_cases hj : j ∈ range (n + 1)
  · simp [hj]
  · simp only [hj, ite_false]
    rw [mem_range, not_lt] at hj
    rw [eN_eq_zero_of_lt n j (by omega)]
    simp

private theorem apoly_eval (n : ℕ) (q : ℂ) :
    (Apoly n).eval q = ∑ k ∈ range (n + 1), (eulerianNumber n k : ℂ) * q ^ k := by
  rw [Apoly, Polynomial.eval_finsetSum]
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

private theorem psi_eq_eval (n : ℕ) (p : ℂ) : chapter5Psi n p = (Apoly n).eval (-p) := by
  rw [apoly_eval]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Finset.sum_range_one]
    simp [chapter5Psi, eulerianNumber]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [show chapter5Psi (m + 1) p
        = ∑ k ∈ range (m + 1), (eulerianNumber (m + 1) k : ℂ) * (-p) ^ k from rfl]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [eN_self m]
    simp

private theorem eN_succ (n k : ℕ) :
    eulerianNumber (n + 1) k =
      (k + 1) * eulerianNumber n k +
        (n + 1 - k) * (if k = 0 then 0 else eulerianNumber n (k - 1)) := rfl

private theorem eN_succ_zero (n : ℕ) : eulerianNumber (n + 1) 0 = eulerianNumber n 0 := by
  rw [eN_succ]; simp

private theorem eN_succ_succ (n j : ℕ) :
    eulerianNumber (n + 1) (j + 1) =
      (j + 2) * eulerianNumber n (j + 1) + (n - j) * eulerianNumber n j := by
  rw [eN_succ]; simp [Nat.succ_sub_succ]

open Polynomial in
private theorem apoly_succ (n : ℕ) :
    Apoly (n + 1) =
      (1 + Polynomial.C (n : ℂ) * Polynomial.X) * Apoly n
        + Polynomial.X * (1 - Polynomial.X) * (Polynomial.derivative (Apoly n)) := by
  have hd : ∀ j : ℕ, (Polynomial.derivative (Apoly n)).coeff j
      = (eulerianNumber n (j + 1) : ℂ) * (j + 1) := by
    intro j
    rw [Polynomial.coeff_derivative, apoly_coeff]
  ext j
  rw [Polynomial.coeff_add, apoly_coeff]
  rw [show (1 + Polynomial.C (n : ℂ) * Polynomial.X) * Apoly n
      = Apoly n + Polynomial.C (n : ℂ) * (Polynomial.X * Apoly n) by ring]
  rw [show Polynomial.X * (1 - Polynomial.X) * (Polynomial.derivative (Apoly n))
      = Polynomial.X * (Polynomial.derivative (Apoly n))
        - Polynomial.X * (Polynomial.X * (Polynomial.derivative (Apoly n))) by ring]
  rcases j with _ | _ | j
  · -- j = 0
    simp [apoly_coeff, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, eN_succ_zero]
  · -- j = 1
    simp only [apoly_coeff, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_mul, hd, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero]
    rw [eN_succ_succ n 0, Nat.sub_zero]
    push_cast
    ring
  · -- j = j+2
    simp only [apoly_coeff, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_mul, hd]
    rw [eN_succ_succ n (j + 1)]
    by_cases hjn : j + 1 ≤ n
    · push_cast [Nat.cast_sub hjn]
      ring
    · have h1 : eulerianNumber n (j + 1) = 0 := eN_eq_zero_of_lt n (j + 1) (by omega)
      have h2 : eulerianNumber n (j + 1 + 1) = 0 := eN_eq_zero_of_lt n (j + 1 + 1) (by omega)
      rw [h1, h2]
      push_cast
      ring

private noncomputable def B (n : ℕ) : ℂ[X] :=
  ∑ i ∈ range (n + 1),
    Polynomial.C (Nat.choose n i : ℂ) * ((Polynomial.X - 1) ^ i * Apoly (n - i))

private noncomputable def cc (n : ℕ) : ℂ[X] :=
  ∑ i ∈ range (n + 1),
    Polynomial.C (Nat.choose n i : ℂ) * ((Polynomial.X - 1) ^ i * Apoly (n + 1 - i))

open Polynomial in
private theorem stepA (m : ℕ) : B (m + 1) = cc m + (Polynomial.X - 1) * B m := by
  -- Expand B (m+1) peeling the i = 0 term and using Pascal on the rest.
  have hB : B (m + 1)
      = Apoly (m + 1)
        + ∑ i ∈ range (m + 1),
            Polynomial.C (Nat.choose m i : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i))
        + ∑ i ∈ range (m + 1),
            Polynomial.C (Nat.choose m (i + 1) : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i)) := by
    rw [B, Finset.sum_range_succ']
    have hsplit : ∀ i ∈ range (m + 1),
        Polynomial.C ((Nat.choose (m + 1) (i + 1)) : ℂ)
            * ((X - 1) ^ (i + 1) * Apoly (m + 1 - (i + 1)))
          = Polynomial.C (Nat.choose m i : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i))
            + Polynomial.C (Nat.choose m (i + 1) : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i)) := by
      intro i _
      have hidx : m + 1 - (i + 1) = m - i := by omega
      rw [Nat.choose_succ_succ m i, hidx, Nat.cast_add, map_add]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hf0 : Polynomial.C ((Nat.choose (m + 1) 0) : ℂ)
        * ((X - 1) ^ 0 * Apoly (m + 1 - 0)) = Apoly (m + 1) := by
      simp
    rw [hf0]
    ring
  -- cc m peeled similarly
  have hcc : cc m
      = Apoly (m + 1)
        + ∑ i ∈ range m,
            Polynomial.C (Nat.choose m (i + 1) : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i)) := by
    rw [cc, Finset.sum_range_succ']
    have hbody : ∀ i ∈ range m,
        Polynomial.C (Nat.choose m (i + 1) : ℂ)
            * ((X - 1) ^ (i + 1) * Apoly (m + 1 - (i + 1)))
          = Polynomial.C (Nat.choose m (i + 1) : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i)) := by
      intro i _
      have hidx : m + 1 - (i + 1) = m - i := by omega
      rw [hidx]
    rw [Finset.sum_congr rfl hbody]
    have hg0 : Polynomial.C (Nat.choose m 0 : ℂ)
        * ((X - 1) ^ 0 * Apoly (m + 1 - 0)) = Apoly (m + 1) := by
      simp
    rw [hg0]
    ring
  -- the "shifted-binomial" sum over range (m+1) equals that over range m (last term 0)
  have hshift : ∑ i ∈ range (m + 1),
        Polynomial.C (Nat.choose m (i + 1) : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i))
      = ∑ i ∈ range m,
        Polynomial.C (Nat.choose m (i + 1) : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i)) := by
    rw [Finset.sum_range_succ]
    rw [Nat.choose_succ_self m]
    simp
  -- (X-1) * B m as a shifted sum
  have hXB : (X - 1) * B m
      = ∑ i ∈ range (m + 1),
        Polynomial.C (Nat.choose m i : ℂ) * ((X - 1) ^ (i + 1) * Apoly (m - i)) := by
    rw [B, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hB, hcc, hshift, hXB]
  ring

open Polynomial in
private theorem stepB (m : ℕ) :
    cc m = (1 + Polynomial.C (m : ℂ) * X) * B m
      + X * (1 - X) * Polynomial.derivative (B m) := by
  have hderiv : Polynomial.derivative (B m)
      = ∑ i ∈ range (m + 1),
          Polynomial.C (Nat.choose m i : ℂ)
            * Polynomial.derivative ((X - 1) ^ i * Apoly (m - i)) := by
    rw [B, Polynomial.derivative_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.derivative_C_mul]
  rw [cc]
  rw [show (1 + Polynomial.C (m : ℂ) * X) * B m
      = ∑ i ∈ range (m + 1),
          (1 + Polynomial.C (m : ℂ) * X)
            * (Polynomial.C (Nat.choose m i : ℂ) * ((X - 1) ^ i * Apoly (m - i)))
      from by rw [B, Finset.mul_sum] ]
  rw [show X * (1 - X) * Polynomial.derivative (B m)
      = ∑ i ∈ range (m + 1),
          X * (1 - X)
            * (Polynomial.C (Nat.choose m i : ℂ)
                * Polynomial.derivative ((X - 1) ^ i * Apoly (m - i)))
      from by rw [hderiv, Finset.mul_sum] ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hle : i ≤ m := by omega
  have hidx : m + 1 - i = (m - i) + 1 := by omega
  rw [hidx, apoly_succ (m - i), Polynomial.derivative_mul, Polynomial.derivative_pow]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_one,
    sub_zero, mul_one]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    simp
  · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    rw [Nat.cast_sub hle, map_sub]
    simp only [pow_succ]
    push_cast
    ring

private theorem apoly_zero : Apoly 0 = 1 := by
  rw [Apoly, Finset.sum_range_one]; simp [eulerianNumber]

private theorem apoly_one : Apoly 1 = 1 := by
  rw [Apoly, Finset.sum_range_succ, Finset.sum_range_one]; simp [eulerianNumber]

open Polynomial in
private theorem B_eq (m : ℕ) : B (m + 1) = Polynomial.X * Apoly (m + 1) := by
  induction m with
  | zero =>
    change B 1 = Polynomial.X * Apoly 1
    rw [B, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
      Nat.cast_one, map_one, pow_zero, pow_one, one_mul, apoly_zero, apoly_one]
    ring
  | succ k ih =>
    rw [stepA (k + 1), stepB (k + 1), ih, apoly_succ (k + 1)]
    rw [Polynomial.derivative_mul, Polynomial.derivative_X]
    ring

private theorem core (m : ℕ) (p : ℂ) :
    ∑ i ∈ range (m + 2),
        (Nat.choose (m + 1) i : ℂ) * (-(p + 1)) ^ i * chapter5Psi (m + 1 - i) p
      = -p * chapter5Psi (m + 1) p := by
  have h := congrArg (Polynomial.eval (-p)) (B_eq m)
  rw [B, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_X,
    ← psi_eq_eval] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow,
    ← psi_eq_eval, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
  ring

private theorem hsum (m : ℕ) (p : ℂ) :
    ∑ i ∈ range (m + 1),
        (Nat.choose (m + 1) (i + 1) : ℂ) * (-(p + 1)) ^ (i + 1) * chapter5Psi (m - i) p
      = -(p + 1) * chapter5Psi (m + 1) p := by
  have hc := core m p
  rw [Finset.sum_range_succ'] at hc
  have hidx : ∀ i ∈ range (m + 1),
      (Nat.choose (m + 1) (i + 1) : ℂ) * (-(p + 1)) ^ (i + 1)
          * chapter5Psi (m + 1 - (i + 1)) p
        = (Nat.choose (m + 1) (i + 1) : ℂ) * (-(p + 1)) ^ (i + 1)
          * chapter5Psi (m - i) p := by
    intro i _
    rw [show m + 1 - (i + 1) = m - i by omega]
  rw [Finset.sum_congr rfl hidx] at hc
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, mul_one,
    Nat.sub_zero] at hc
  linear_combination hc

private theorem conj4 (m : ℕ) (p : ℂ) (hp1 : p + 1 ≠ 0) :
    chapter5Psi (m + 1) p
      = ∑ j ∈ range (m + 1), chapter5Entry5Formula52Term (m + 1) p j := by
  have hne : -(p + 1) ≠ 0 := neg_ne_zero.mpr hp1
  apply mul_left_cancel₀ hne
  rw [Finset.mul_sum, ← hsum m p]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [chapter5Entry5Formula52Term, show m + 1 - j - 1 = m - j by omega, neg_pow]
  simp only [pow_succ]
  ring

private theorem conj3 (m : ℕ) (p : ℂ) (hp1 : p + 1 ≠ 0) :
    (-1 : ℂ) ^ (m + 1 + 1) * p * chapter5Psi (m + 1) p / (p + 1) ^ (m + 1)
      = ∑ k ∈ range (m + 2), chapter5Entry5Formula51Term (m + 1) p k := by
  rw [← Finset.sum_range_reflect (fun k => chapter5Entry5Formula51Term (m + 1) p k) (m + 2)]
  have hterm : ∀ i ∈ range (m + 2),
      chapter5Entry5Formula51Term (m + 1) p (m + 2 - 1 - i)
        = (-1 : ℂ) ^ (m + 1) * (Nat.choose (m + 1) i : ℂ) * (-(p + 1)) ^ i
            * chapter5Psi (m + 1 - i) p / (p + 1) ^ (m + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hile : i ≤ m + 1 := by omega
    have hp2 : (p + 1) ^ (m + 1) = (p + 1) ^ i * (p + 1) ^ (m + 1 - i) := by
      rw [← pow_add]; congr 1; omega
    have hs : (-1 : ℂ) ^ (m + 1 - i) = (-1) ^ (m + 1) * (-1) ^ i := by
      rw [← pow_add, show m + 1 + i = (m + 1 - i) + 2 * i by omega, pow_add, pow_mul]
      norm_num
    have hpi : (p + 1) ^ i ≠ 0 := pow_ne_zero _ hp1
    have hpmi : (p + 1) ^ (m + 1 - i) ≠ 0 := pow_ne_zero _ hp1
    have hnp : (-(p + 1) : ℂ) ^ i = (-1) ^ i * (p + 1) ^ i := by
      rw [← mul_pow]; congr 1; ring
    rw [chapter5Entry5Formula51Term, show m + 2 - 1 - i = m + 1 - i by omega,
      Nat.choose_symm hile, hs, hnp, hp2]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  rw [show ∑ i ∈ range (m + 2),
        (-1 : ℂ) ^ (m + 1) * (Nat.choose (m + 1) i : ℂ) * (-(p + 1)) ^ i
          * chapter5Psi (m + 1 - i) p
      = (-1 : ℂ) ^ (m + 1) * ∑ i ∈ range (m + 2),
          (Nat.choose (m + 1) i : ℂ) * (-(p + 1)) ^ i * chapter5Psi (m + 1 - i) p
      from by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
  rw [core]
  ring

/-- **Two finite expansions of the Eulerian polynomials.** Let $A(n,k)$ be the Eulerian numbers,
given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$, and let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$. For every integer
$n \ge 1$ and every complex number $p \ne -1$, we have $p + 1 \ne 0$, $\Psi_0(p) = 1$,
$(-1)^{n+1} p \, \Psi_n(p)/(p+1)^n = \sum_{k=0}^{n} (-1)^k \binom{n}{k} \Psi_k(p)/(p+1)^k$, and
$\Psi_n(p) = \sum_{j=0}^{n-1} (-1)^j \binom{n}{j+1} (p+1)^j \Psi_{n-j-1}(p)$.

Proves `Wanted` entry `ramanujan_part1_ch5_entry3_eulerianexplicit`, whose name misnumbered the
entry (Entry 3 is `Entry3.ramanujan_part1_ch5_entry3`).

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5, Entry 5,
formulas (5.1) and (5.2).
-/
theorem ramanujan_part1_ch5_entry5_eulerianexplicit (n : ℕ) (p : ℂ)
    (hn : 1 ≤ n) (hp : p ≠ -1) :
    p + 1 ≠ 0 ∧
      chapter5Psi 0 p = 1 ∧
      (-1 : ℂ) ^ (n + 1) * p * chapter5Psi n p / (p + 1) ^ n =
        ∑ k ∈ range (n + 1), chapter5Entry5Formula51Term n p k ∧
      chapter5Psi n p =
        ∑ j ∈ range n, chapter5Entry5Formula52Term n p j := by
  have hp1 : p + 1 ≠ 0 := by
    intro h
    apply hp
    linear_combination h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  refine ⟨hp1, ?_, conj3 m p hp1, conj4 m p hp1⟩
  simp [chapter5Psi]

end

end Entry5Eulerianexplicit

end MathlibExt.Analysis.Ramanujan.Part1Ch5
